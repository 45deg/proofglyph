module Source = Proofglyph_hieratic.Source

(** {1 Example Bundler and Catalog Generator}

    Processes source files under [examples/] for web demo and documentation:
    - Default mode: preserves original source files and their import statements
      and emits the [Examples_data.files] OCaml source for the browser demo.
    - [--catalog] mode: cross-references examples against [docs/proofs.md] to output
      the JSON proof catalog. *)

(** Reads an entire file into a string in binary mode. *)
let read path =
  let ch = open_in_bin path in
  Fun.protect ~finally:(fun () -> close_in ch)
    (fun () -> really_input_string ch (in_channel_length ch))

(** Recursively collects all [.ht] and [.pg] file paths in a directory. *)
let rec files path =
  if Sys.is_directory path then
    Sys.readdir path |> Array.to_list |> List.sort String.compare
    |> List.concat_map (fun name -> files (Filename.concat path name))
  else if Filename.check_suffix path ".ht" || Filename.check_suffix path ".pg" then [path]
  else []

let quote = Source.json_string

(** Formats key-value fields into an indented JSON object string. *)
let object_json fields =
  let indent s = String.split_on_char '\n' s |> String.concat "\n  " in
  "{\n" ^ String.concat ",\n" (List.map (fun (key, value) ->
    "  " ^ quote key ^ ": " ^ indent value) fields) ^ "\n}"

let () =
  let root = if Array.length Sys.argv > 2 then Sys.argv.(2) else "../examples" in
  let sources = List.map (fun path ->
    let name = "examples/" ^ String.sub path (String.length root + 1)
      (String.length path - String.length root - 1) in
    name, read path) (files root) in
  if Array.length Sys.argv > 1 && Sys.argv.(1) = "--catalog" then (
  let proofs = List.concat_map (fun (path, source) ->
    if Filename.check_suffix path ".pg" then [] else
    Source.parse_items ~file:path source |> List.filter_map (function
      | Source.Declaration d when d.body <> None -> Some (d.name, path, d.at.line)
      | _ -> None)) sources in
  let document = read (Filename.concat (Filename.dirname root) "docs/proofs.md") in
  let link = Str.regexp "\\[\\([^]]+\\)\\](\\.\\./\\(examples/[^)]+\\))" in
  let section = ref false in
  let started = ref false and finished = ref false in
  let lines = String.split_on_char '\n' document |> List.filter (fun line ->
    if line = "<!-- proof-catalog:start -->" then (
      if !started then failwith "duplicate proof catalog start marker";
      started := true; section := true; false)
    else if line = "<!-- proof-catalog:end -->" then (
      if not !section then failwith "unexpected proof catalog end marker";
      finished := true; section := false; false)
    else !section) in
  if not !started || not !finished then failwith "missing proof catalog markers";
  let rows = lines |> List.filter_map (fun row ->
    match String.split_on_char '|' row |> List.map String.trim with
    | [""; subject; title; links; _; ""] when String.contains links '[' ->
        let rec collect start acc =
          match (try Some (Str.search_forward link links start) with Not_found -> None) with
          | None -> List.rev acc
          | Some _ ->
              let name = Str.matched_group 1 links and path = Str.matched_group 2 links in
              let next = Str.match_end () in
              let _, _, line = match List.find_opt (fun (n, p, _) -> n = name && p = path) proofs with
                | Some proof -> proof
                | None -> failwith ("documented proof not found: " ^ path ^ ":" ^ name) in
              let entry = object_json ["name", quote name; "path", quote path;
                "line", string_of_int line] in
              collect next (entry :: acc) in
        let title = String.concat "" (String.split_on_char '`' title) in
        Some (subject ^ "：" ^ title, "[" ^ String.concat "," (collect 0 []) ^ "]")
    | _ -> None) in
  if rows = [] then failwith "empty proof catalog";
  let catalog = object_json ["proofs", object_json rows] ^ "\n" in
  print_string catalog)
  else (
    print_endline "let files = [";
    List.iter (fun (path, source) ->
      Printf.printf "  (%S, %S);\n" path source) sources;
    print_endline "]")
