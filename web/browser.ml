open Tinyprover_core
module Assembly = Tinyprover_pa.Reader
module Source = Tinyprover_tp.Source
open Js_of_ocaml

(** {1 Browser JavaScript Bindings}

    Interface exported via js_of_ocaml to run tinyprover's compiler and kernel
    inside web browsers.
    Exposes the following API on the global [window.tinyprover] object:
    - [examples]: Bundled example file list (JSON array).
    - [compileAt(path, source)]: Compiles source with virtual file path, returning assembly and sourcemap.
    - [checkMapped(source)]: Verifies assembly using declaration names if it matches the last compile output.
    - [check(source)]: Verifies assembly without source mapping. *)

(** Constructs a JS response object [{ok: bool, output: string, ?sourcemap: string}]. *)
let response ?sourcemap ok output =
  Js.Unsafe.obj (Array.of_list ([
    "ok", Js.Unsafe.inject (Js.bool ok);
    "output", Js.Unsafe.inject (Js.string output)
  ] @ match sourcemap with None -> [] | Some value ->
    ["sourcemap", Js.Unsafe.inject (Js.string value)]))

(** Exception handling wrapper returning [{ok: false, output: "error: ..."}]. *)
let protect f input =
  try f (Js.to_string input) with
  | Source.Error s | Assembly.Error s | Kernel.Error s
  | Sys_error s | Failure s | Invalid_argument s -> response false ("error: " ^ s)
  | Stack_overflow -> response false "error: nesting exceeds runtime stack capacity"

(** Cache holding the last successful compilation result from [compile_at] (used by [checkMapped]). *)
let last_compiled : Source.compiled option ref = ref None

(** Verifies .pa assembly and formats the output string.
    If [mappings] are provided, constant indices are replaced with original declaration names. *)
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

(** Verifies assembly using declaration names if it exactly matches the last compiled output. *)
let check_mapped source =
  let mappings = match !last_compiled with
    | Some compiled when compiled.assembly = source -> compiled.sourcemap
    | _ -> [] in
  check ~mappings source

(** Compiles source under virtual path [path].
    Rejects import statements because the browser environment lacks a filesystem (requires expanded sources). *)
let compile_at path source =
  last_compiled := None;
  let compiled = Source.compile ~file:path source in
  last_compiled := Some compiled;
  response ~sourcemap:(Source.sourcemap_json compiled) true compiled.assembly

(** Serialized JSON array of bundled example files. *)
let examples_json =
  "[" ^ String.concat "," (List.map (fun (path, source) ->
    "{\"path\":" ^ Source.json_string path ^ ",\"source\":" ^ Source.json_string source ^ "}")
    Examples_data.files) ^ "]"

let () =
  Js.export "tinyprover" (Js.Unsafe.obj [|
    "examples", Js.Unsafe.inject (Js.string examples_json);
    "compileAt", Js.Unsafe.inject (Js.wrap_callback (fun path input -> protect (compile_at (Js.to_string path)) input));
    "checkMapped", Js.Unsafe.inject (Js.wrap_callback (protect check_mapped));
    "check", Js.Unsafe.inject (Js.wrap_callback (protect (check ~mappings:[])))
  |])
