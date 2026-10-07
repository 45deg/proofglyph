open Tinyprover

let read path =
  let ch = open_in_bin path in
  Fun.protect ~finally:(fun () -> close_in ch)
    (fun () -> really_input_string ch (in_channel_length ch))

let rec files path =
  if Sys.is_directory path then
    Sys.readdir path |> Array.to_list |> List.sort String.compare
    |> List.concat_map (fun name -> files (Filename.concat path name))
  else if Filename.check_suffix path ".tp" || Filename.check_suffix path ".pa" then [path]
  else []

(* Keep declaration text, replacing imports and removing repetitive file headers. *)
let expand path =
  let seen = Hashtbl.create 16 in
  let rec visit active path =
    let path = Unix.realpath path in
    if List.mem path active then failwith ("import cycle: " ^ path);
    if Hashtbl.mem seen path then "" else (
      let source = read path in
      let tokens = Source.lex ~file:path source in
      let line_starts = ref [0] in
      String.iteri (fun i c -> if c = '\n' then line_starts := (i+1) :: !line_starts) source;
      let line_starts = Array.of_list (List.rev !line_starts) in
      let offset (token : Source.token) = line_starts.(token.line - 1) + token.col - 1 in
      let output = Buffer.create (String.length source) in
      let copied = ref 0 in
      Array.iteri (fun i (token : Source.token) ->
        if token.text = "import" then (
          let start = offset token in
          Buffer.add_substring output source !copied (start - !copied);
          let relative = tokens.(i+1).text in
          let relative = String.sub relative 1 (String.length relative - 2) in
          let target = if Filename.is_relative relative then
            Filename.concat (Filename.dirname path) relative else relative in
          Buffer.add_string output (visit (path :: active) target);
          Buffer.add_char output '\n';
          copied := offset tokens.(i+2) + 1)) tokens;
      Buffer.add_substring output source !copied (String.length source - !copied);
      Hashtbl.add seen path ();
      Buffer.contents output)
  in
  (* Validate imports with the same parser and filesystem rules as the CLI. *)
  ignore (Source.load path);
  visit [] path |> String.split_on_char '\n'
  |> List.filter (fun line ->
    let line = String.trim line in
    line <> "// Checked proofs; prerequisites are imported by subject."
    && line <> "// Trusted vocabulary, inference rules and explicit definitions.")
  |> String.concat "\n"
  |> String.trim

let quote = Source.json_string
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
    if Filename.check_suffix path ".pa" then [] else
    Source.parse_items ~file:path source |> List.filter_map (function
      | Source.Declaration d when d.body <> None -> Some (d.name, path, d.at.line)
      | _ -> None)) sources in
  let document = read (Filename.concat (Filename.dirname root) "docs/proofs.md") in
  let link = Str.regexp "\\[\\([^]]+\\)\\](\\.\\./\\(examples/[^)]+\\))" in
  let section = ref false in
  let lines = String.split_on_char '\n' document |> List.filter (fun line ->
    if line = "## 実装した証明" then (section := true; false)
    else if String.starts_with ~prefix:"## " line then (section := false; false)
    else !section) in
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
  let catalog = object_json ["proofs", object_json rows] ^ "\n" in
  print_string catalog)
  else (
    print_endline "let files = [";
    List.iter (fun (path, source) ->
      let source = if Filename.check_suffix path ".tp" then
        expand (Filename.concat root (String.sub path 9 (String.length path - 9)))
        else source in
      Printf.printf "  (%S, %S);\n" path source) sources;
    print_endline "]")
