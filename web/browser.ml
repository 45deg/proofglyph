open Proofglyph_core
module Assembly = Proofglyph_language.Reader
module Source = Proofglyph_hieratic.Source
open Js_of_ocaml

(** {1 Browser JavaScript Bindings}

    Interface exported via js_of_ocaml to run proofglyph's compiler and kernel
    inside web browsers.
    Exposes the following API on the global [window.proofglyph] object:
    - [examples]: Bundled example file list (JSON array).
    - [compileAt(path, source)]: Compiles source with virtual file path, returning assembly and sourcemap.
    - [compileProject(path, filesJSON)]: Compiles bundled and edited files with imports.
    - [projectFiles(path, filesJSON)]: Lists the entry file and its transitive imports.
    - [checkMapped(source)]: Verifies assembly using declaration names if it matches the last compile output.
    - [check(source)]: Verifies assembly without source mapping. *)

(** Constructs a JS response object [{ok: bool, output: string, ?sourcemap: string}]. *)
let response ?sourcemap ?entries ok output =
  Js.Unsafe.obj (Array.of_list ([
    "ok", Js.Unsafe.inject (Js.bool ok);
    "output", Js.Unsafe.inject (Js.string output)
  ] @ (match sourcemap with None -> [] | Some value ->
    ["sourcemap", Js.Unsafe.inject (Js.string value)])
    @ (match entries with None -> [] | Some value ->
    ["entries", Js.Unsafe.inject (Js.string value)])))

(** Exception handling wrapper returning [{ok: false, output: "error: ..."}]. *)
let protect f input =
  try f (Js.to_string input) with
  | Source.Error s | Assembly.Error s | Kernel.Error s
  | Sys_error s | Failure s | Invalid_argument s -> response false ("error: " ^ s)
  | Stack_overflow -> response false "error: nesting exceeds runtime stack capacity"

(** Cache holding the last successful compilation result from [compile_at] (used by [checkMapped]). *)
let last_compiled : Source.compiled option ref = ref None

(** Verifies .pg assembly and formats the output string.
    If [mappings] are provided, constant indices are replaced with original declaration names. *)
let check ?(mappings=[]) ?(display_types=[]) ?(declarations=[]) source =
  let kernel = Kernel.create () in
  (try Assembly.run kernel source with Assembly.Error message ->
    raise (Assembly.Error (Source.annotate_assembly_error mappings message)));
  let entries = Kernel.entries kernel in
  let output = Buffer.create 256 in
  let names index = match List.find_opt (fun (m : Source.mapping) -> m.constant = index) mappings with
    | Some m -> m.name | None -> "c" ^ string_of_int index in
  (* Export the checked type itself; presentation never parses or guesses from titles. *)
  let rec term_json = function
    | Term.Type -> "[\"type\"]" | Term.Kind -> "[\"kind\"]"
    | Term.Var n -> "[\"var\"," ^ string_of_int n ^ "]"
    | Term.Const n -> "[\"const\"," ^ Source.json_string (names n) ^ "]"
    | Term.App (f, x) -> pair "app" f x
    | Term.Pi (a, b) -> pair "pi" a b
    | Term.Lam (a, b) -> pair "lam" a b
  and pair tag a b = "[" ^ Source.json_string tag ^ "," ^ term_json a ^ "," ^ term_json b ^ "]" in
  let entries_json = "[" ^ String.concat "," (List.mapi (fun i (entry : Kernel.entry) ->
    "{\"name\":" ^ Source.json_string (names i) ^ ",\"origin\":"
    ^ Source.json_string (match entry.origin with Kernel.Assumption -> "assumption" | Kernel.Proven -> "proven")
    ^ (match List.nth_opt declarations i with None -> "" | Some (d : Source.declaration) ->
      ",\"declarationKind\":" ^ Source.json_string d.at.text)
    ^ ",\"type\":" ^ term_json entry.typ
    ^ (match List.nth_opt display_types i with None -> "" | Some typ ->
      ",\"surfaceType\":" ^ term_json typ) ^ "}") entries) ^ "]" in
  List.iteri (fun i (entry : Kernel.entry) ->
    Printf.bprintf output "%s [%s] : %s\n" (names i)
      (match entry.origin with Kernel.Assumption -> "assumption" | Kernel.Proven -> "proven")
      (Term.pretty ~names entry.typ)) entries;
  Printf.bprintf output "Accepted: %d declarations (%d assumptions).\n"
    (List.length entries)
    (List.length (List.filter (fun (e : Kernel.entry) -> e.origin = Kernel.Assumption) entries));
  response ~entries:entries_json true (Buffer.contents output)

(** Verifies assembly using declaration names if it exactly matches the last compiled output. *)
let check_mapped source =
  let mappings, display_types, declarations = match !last_compiled with
    | Some compiled when compiled.assembly = source -> compiled.sourcemap, compiled.display_types, compiled.declarations
    | _ -> [], [], [] in
  check ~mappings ~display_types ~declarations source

(** Normalize virtual paths without consulting the host filesystem. *)
let normalize path =
  if not (Filename.is_relative path) then raise (Source.Error "absolute paths are not supported");
  let rec fold stack = function
    | [] -> String.concat "/" (List.rev stack)
    | "" :: rest | "." :: rest -> fold stack rest
    | ".." :: rest -> (match stack with
        | [] -> raise (Source.Error "import path escapes the virtual workspace")
        | _ :: tail -> fold tail rest)
    | part :: rest -> fold (part :: stack) rest in
  fold [] (String.split_on_char '/' path)

let project_files json =
  let array = Js.to_array (Js.Unsafe.coerce (Js.Unsafe.meth_call Js._JSON "parse" [|Js.Unsafe.inject (Js.string json)|])) in
  Array.to_list array |> List.map (fun entry ->
    let field name = Js.to_string (Js.Unsafe.get entry name) in
    normalize (field "path"), field "source")

(** Resolve imports using bundled files plus edited sources. Keep original locations. *)
let load_project path edits =
  let files = Hashtbl.create 64 in
  List.iter (fun (path, source) -> Hashtbl.replace files (normalize path) source) Examples_data.files;
  List.iter (fun (path, source) -> Hashtbl.replace files path source) edits;
  let seen = Hashtbl.create 16 and paths = ref [] in
  let rec visit active at path =
    let report message = match at with
      | Some token -> Source.error token message
      | None -> raise (Source.Error (path ^ ": " ^ message)) in
    let path = try normalize path with Source.Error message -> report message in
    if List.mem path active then report ("import cycle: " ^ String.concat " -> " (List.rev (path :: active)));
    if Hashtbl.mem seen path then [] else (
      let source = match Hashtbl.find_opt files path with
        | Some source -> source | None -> report ("source not found: " ^ path) in
      paths := path :: !paths;
      let declarations = Source.parse_items ~file:path source |> List.concat_map (function
        | Source.Declaration declaration -> [declaration]
        | Source.Import (token, relative) ->
            if not (Filename.is_relative relative) then report "absolute imports are not supported";
            visit (path :: active) (Some token) (Filename.concat (Filename.dirname path) relative)) in
      Hashtbl.add seen path ();
      declarations) in
  let declarations = visit [] None path in
  declarations, List.rev !paths

let compile_project path edits =
  last_compiled := None;
  let declarations, _ = load_project path edits in
  let compiled = Source.compile_declarations declarations in
  last_compiled := Some compiled;
  response ~sourcemap:(Source.sourcemap_json compiled) true compiled.assembly

let compile_at path source =
  last_compiled := None;
  compile_project path [normalize path, source]

(** Serialized JSON array of bundled example files. *)
let examples_json =
  "[" ^ String.concat "," (List.map (fun (path, source) ->
    "{\"path\":" ^ Source.json_string path ^ ",\"source\":" ^ Source.json_string source ^ "}")
    Examples_data.files) ^ "]"

let () =
  Js.export "proofglyph" (Js.Unsafe.obj [|
    "examples", Js.Unsafe.inject (Js.string examples_json);
    "compileAt", Js.Unsafe.inject (Js.wrap_callback (fun path input -> protect (compile_at (Js.to_string path)) input));
    "compileProject", Js.Unsafe.inject (Js.wrap_callback (fun path input ->
      protect (fun json -> last_compiled := None; compile_project (Js.to_string path) (project_files json)) input));
    "projectFiles", Js.Unsafe.inject (Js.wrap_callback (fun path input ->
      protect (fun json ->
        let _, paths = load_project (Js.to_string path) (project_files json) in
        response true ("[" ^ String.concat "," (List.map Source.json_string paths) ^ "]")) input));
    "checkMapped", Js.Unsafe.inject (Js.wrap_callback (protect check_mapped));
    "check", Js.Unsafe.inject (Js.wrap_callback (protect (check ~mappings:[] ~display_types:[] ~declarations:[])))
  |])
