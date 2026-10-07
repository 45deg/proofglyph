open Tinyprover
open Js_of_ocaml

let response ?sourcemap ok output =
  Js.Unsafe.obj (Array.of_list ([
    "ok", Js.Unsafe.inject (Js.bool ok);
    "output", Js.Unsafe.inject (Js.string output)
  ] @ match sourcemap with None -> [] | Some value ->
    ["sourcemap", Js.Unsafe.inject (Js.string value)]))

let protect f input =
  try f (Js.to_string input) with
  | Source.Error s | Assembly.Error s | Kernel.Error s
  | Sys_error s | Failure s | Invalid_argument s -> response false ("error: " ^ s)
  | Stack_overflow -> response false "error: nesting exceeds runtime stack capacity"

let last_compiled : Source.compiled option ref = ref None

let check ?(mappings=[]) source =
  let kernel = Kernel.create () in
  (try Assembly.run kernel source with Assembly.Error message ->
    raise (Assembly.Error (Source.annotate_assembly_error mappings message)));
  let entries = Kernel.entries kernel in
  let output = Buffer.create 256 in
  let names index = match List.find_opt (fun (m : Source.mapping) -> m.constant = index) mappings with
    | Some m -> m.name | None -> "c" ^ string_of_int index in
  List.iteri (fun i (entry : Kernel.entry) ->
    Printf.bprintf output "%s [%s] : %s\n" (names i)
      (match entry.origin with Kernel.Assumption -> "assumption" | Kernel.Proven -> "proven")
      (Term.pretty ~names entry.typ)) entries;
  Printf.bprintf output "Accepted: %d declarations (%d assumptions).\n"
    (List.length entries)
    (List.length (List.filter (fun (e : Kernel.entry) -> e.origin = Kernel.Assumption) entries));
  response true (Buffer.contents output)

let check_mapped source =
  let mappings = match !last_compiled with
    | Some compiled when compiled.assembly = source -> compiled.sourcemap
    | _ -> [] in
  check ~mappings source

let compile_at path source =
  last_compiled := None;
  let declarations = Source.parse_items ~file:path source |> List.map (function
    | Source.Declaration d -> d
    | Source.Import (at, _) -> Source.error at "デモでは import を使えません。展開済みのソースを入力してください") in
  let compiled = Source.compile_declarations declarations in
  last_compiled := Some compiled;
  response ~sourcemap:(Source.sourcemap_json compiled) true compiled.assembly

let examples_json =
  "[" ^ String.concat "," (List.map (fun (path, source) ->
    "{\"path\":" ^ Source.json_string path ^ ",\"source\":" ^ Source.json_string source ^ "}")
    Examples_data.files) ^ "]"

let () =
  Js.export "tinyprover" (Js.Unsafe.obj [|
    "examples", Js.Unsafe.inject (Js.string examples_json);
    "compileAt", Js.Unsafe.inject (Js.wrap_callback (fun path input -> protect (compile_at (Js.to_string path)) input));
    "compile", Js.Unsafe.inject (Js.wrap_callback (protect (fun source -> response true (Source.compile source).assembly)));
    "checkMapped", Js.Unsafe.inject (Js.wrap_callback (protect check_mapped));
    "check", Js.Unsafe.inject (Js.wrap_callback (protect (check ~mappings:[])))
  |])
