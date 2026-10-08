(* .tp parsing/imports and I/O remain unverified. Name resolution, .pa byte
   encoding/decoding and type checking are extracted from Rocq. *)
let usage () =
  prerr_endline "Usage: rocq4tp (check|check-pa|compile) FILE [--no-axioms] [--fuel N]\n       compile also accepts [-o FILE]; default output is stdout";
  exit 2

let reject () =
  prerr_endline "Rejected: invalid input, name resolution, typing, axiom policy, or fuel exhaustion";
  exit 1

let write_output path contents =
  match path with
  | None -> output_string stdout contents; flush stdout
  | Some path ->
      let channel = open_out_bin path in
      Fun.protect ~finally:(fun () -> close_out channel)
        (fun () -> output_string channel contents)

let run () =
  if Array.length Sys.argv < 3 then usage ();
  let command = Sys.argv.(1) in
  if not (List.mem command ["check"; "check-pa"; "compile"]) then usage ();
  let allow = ref true and fuel = ref 2048 and output = ref None in
  let rec options i =
    if i < Array.length Sys.argv then
      match Sys.argv.(i) with
      | "--no-axioms" -> allow := false; options (i + 1)
      | "-o" when command = "compile" && i + 1 < Array.length Sys.argv && !output = None ->
          output := Some Sys.argv.(i + 1); options (i + 2)
      | "--fuel" when i + 1 < Array.length Sys.argv ->
          (match int_of_string_opt Sys.argv.(i + 1) with
           | Some n when n > 0 && n <= 100_000 -> fuel := n
           | _ -> usage ());
          options (i + 2)
      | _ -> usage ()
  in
  options 3;
  let fuel = Adapter.nat_of_int !fuel in
  if command = "check-pa" then (
    let bytes = Adapter.Source.read_file Sys.argv.(2) |> Adapter.chars in
    match Frontend.check_pa fuel !allow bytes with
    | None -> reject ()
    | Some signature -> Printf.printf "Accepted %d declarations\n" (List.length signature))
  else (
    let ds = Adapter.Source.load Sys.argv.(2) |> Adapter.declarations in
    if command = "compile" then (
      match Frontend.compile_pa fuel !allow ds with
      | None -> reject ()
      | Some (bytes, _) -> write_output !output (Adapter.string_of_chars bytes))
    else match Frontend.compile fuel !allow ds with
      | None -> reject ()
      | Some (checked, _) -> Printf.printf "Accepted %d declarations\n" (List.length checked))

let () =
  try run () with
  | Adapter.Source.Error message | Sys_error message -> prerr_endline message; exit 1
  | Stack_overflow | Out_of_memory -> prerr_endline "Resource limit exceeded"; exit 1
