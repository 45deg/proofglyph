open Tinyprover_core
module Assembly = Tinyprover_pa.Reader

(** {1 .tp Language Compiler and Frontend}

    Provides lexing, parsing, recursive import resolution, name resolution,
    code generation to the .pa assembly language, and source mapping for the
    high-level named λΠ language (.tp). *)

(** Raised on syntax, name resolution, or import errors, with source location. *)
exception Error of string

(** Lexical token annotated with source position. *)
type token = {
  text : string;          (** Token string content. *)
  line : int;             (** 1-based line number. *)
  col : int;              (** 1-based column byte offset. *)
  file : string option;   (** Source file path, or [None] for direct string inputs. *)
}

(** Abstract syntax tree for expressions in .tp. *)
type expr =
  | Name of string                     (** Identifier (variable or global constant). *)
  | Universe                           (** Universe [Type]. *)
  | Top                                (** Super-universe [Kind]. *)
  | Apply of expr * expr               (** Function application [e1 e2] (left-associative). *)
  | Product of string option * expr * expr
    (** Dependent product [forall (x:A), B] or non-dependent arrow [A -> B] ([None] name). *)
  | Lambda of string * expr * expr     (** Lambda abstraction [fun (x:A) => b]. *)

(** AST for a top-level declaration. *)
type declaration = {
  name : string;          (** Declared identifier name. *)
  typ : expr;             (** Declared type expression. *)
  body : expr option;     (** Definition or proof term, or [None] for [axiom]. *)
  at : token;             (** Token pointing to the declaration keyword (for diagnostics). *)
}

(** Formats and raises an [Error] with file and line:column coordinates. *)
let error t msg =
  let location = Printf.sprintf "%d:%d" t.line t.col in
  let location = match t.file with None -> location | Some p -> p ^ ":" ^ location in
  raise (Error (location ^ ": " ^ msg))

(** Lexer for the .tp language.
    - Recognizes ASCII identifiers, keywords, quoted import paths, and punctuation symbols.
    - Skips line comments ([// ...]) and whitespace.
    - Appends an [<eof>] token at the end of the input. *)
let lex ?file s =
  let n = String.length s in
  let ident_start = function 'a'..'z' | 'A'..'Z' | '_' -> true | _ -> false in
  let ident c = ident_start c || (c >= '0' && c <= '9') || c = '\'' in
  let rec loop i line col acc =
    let tok text j = j, line, col+j-i, {text;line;col;file}::acc in
    if i = n then Array.of_list (List.rev ({text="<eof>";line;col;file}::acc))
    else
    let next_i, next_line, next_col, next_acc = match s.[i] with
    | '\n' -> i+1, line+1, 1, acc
    | ' ' | '\r' | '\t' -> i+1, line, col+1, acc
    | '/' when i+1 < n && s.[i+1] = '/' ->
        let j = ref (i+2) in while !j < n && s.[!j] <> '\n' do incr j done;
        !j, line, col+ !j-i, acc
    | '"' ->
        let j = ref (i+1) in
        while !j < n && s.[!j] <> '"' && s.[!j] <> '\n' && s.[!j] <> '\r'
          && s.[!j] <> '\\' do incr j done;
        if !j = n || s.[!j] <> '"' then
          error {text="";line;col;file} "unterminated import path or unsupported escape";
        tok (String.sub s i (!j-i+1)) (!j+1)
    | ':' when i+1 < n && s.[i+1] = '=' -> tok ":=" (i+2)
    | '-' when i+1 < n && s.[i+1] = '>' -> tok "->" (i+2)
    | '=' when i+1 < n && s.[i+1] = '>' -> tok "=>" (i+2)
    | '(' | ')' | ':' | ';' | ',' as c -> tok (String.make 1 c) (i+1)
    | c when ident_start c ->
        let j = ref (i+1) in while !j < n && ident s.[!j] do incr j done;
        tok (String.sub s i (!j-i)) !j
    | c -> error {text="";line;col;file} (Printf.sprintf "unexpected character %C" c)
    in loop next_i next_line next_col next_acc
  in loop 0 1 1 []

(** Reserved keyword list. *)
let reserved = ["axiom";"def";"theorem";"import";"forall";"fun";"Type";"Kind"]

(** Checks if a string is a valid non-keyword identifier. *)
let is_name s = String.length s > 0 &&
  (match s.[0] with 'a'..'z' | 'A'..'Z' | '_' -> true | _ -> false) &&
  not (List.mem s reserved)

(** Top-level item in a source file (declaration or import statement). *)
type item = Declaration of declaration | Import of token * string

(** Recursive descent parser converting tokens into top-level items.
    Desugars multi-variable parameters like [(x y : A)] into sequential bindings
    and lifts declaration parameters into outer Pi (for types) and Lam (for bodies). *)
let parse_items ?file source =
  let tokens = lex ?file source in
  let pos = ref 0 in
  let peek () = tokens.(!pos) in
  let take () = let t = peek () in incr pos; t in
  let accept s = if (peek ()).text = s then (incr pos; true) else false in
  let expect s = if not (accept s) then error (peek ()) ("expected " ^ s) in
  let name () = let t = peek () in if is_name t.text then (ignore(take());t.text)
    else error t "expected an identifier" in
  let rec term () =
    if accept "forall" then (
      let ps = parameters () in
      if ps=[] then error (peek ()) "forall requires a parameter";
      expect ","; let body = term () in
      List.fold_right (fun (x,a) b -> Product(Some x,a,b)) ps body)
    else if accept "fun" then (
      let ps = parameters () in
      if ps=[] then error (peek ()) "fun requires a parameter";
      expect "=>"; let body = term () in
      List.fold_right (fun (x,a) b -> Lambda(x,a,b)) ps body)
    else (
      let a = application () in
      if accept "->" then Product(None,a,term ()) else a)
  and parameters () =
    if accept "(" then (
      let first = name () in
      let rec names acc = if is_name (peek ()).text then names (name()::acc)
        else List.rev acc in
      let ns = names [first] in expect ":";
      let a = term () in expect ")";
      List.map (fun x -> x,a) ns @ parameters ())
    else []
  and application () =
    let rec more f =
      let s = (peek ()).text in
      if s="(" || s="Type" || s="Kind" || is_name s then
        let x = atom () in more (Apply(f,x)) else f
    in more (atom ())
  and atom () =
    if accept "Type" then Universe else if accept "Kind" then Top
    else if accept "(" then (let t = term () in expect ")"; t)
    else Name (name ())
  in
  let rec declarations acc =
    if (peek ()).text="<eof>" then List.rev acc else (
      let at = take () in
      if at.text="import" then (
        let path = take () in
        if String.length path.text < 2 || path.text.[0] <> '"' then
          error path "expected a quoted import path";
        let path = String.sub path.text 1 (String.length path.text-2) in
        if path="" then error at "import path must not be empty";
        expect ";";
        declarations (Import(at,path)::acc))
      else (
      if not (List.mem at.text ["axiom";"def";"theorem"]) then
        error at "expected import, axiom, def, or theorem";
      let n = name () in
      let ps = parameters () in
      expect ":"; let result = term () in
      let body = if at.text="axiom" then None else (
        expect ":="; let b = term () in
        Some (List.fold_right (fun (x,a) b -> Lambda(x,a,b)) ps b)) in
      expect ";";
      let typ = List.fold_right (fun (x,a) b -> Product(Some x,a,b)) ps result in
      declarations (Declaration {name=n;typ;body;at}::acc)))
  in declarations []

(** Parses declarations directly from a string source.
    Direct string parsing rejects import statements, requiring file-based compilation. *)
let parse source =
  List.map (function
    | Declaration d -> d
    | Import(at,_) -> error at "imports require compile_file or load")
    (parse_items source)

(** Reads an entire file into a string in binary mode. *)
let read_file path =
  let ch = open_in_bin path in
  Fun.protect ~finally:(fun () -> close_in ch)
    (fun () -> really_input_string ch (in_channel_length ch))

(** Recursively expands import statements in place into a single declaration list.
    - Resolves file paths via [Unix.realpath] to deduplicate diamonds and aliases.
    - Relative imports are resolved relative to the importing file's directory.
    - Detects cyclic dependencies and reports an error with the import cycle.
    - Does not modify the process working directory. *)
let load path =
  let seen = Hashtbl.create 16 in
  let rec visit active at path =
    let report msg = match at with
      | Some t -> error t msg
      | None -> raise (Error (path ^ ": " ^ msg)) in
    let canonical = try Unix.realpath path with
      | Unix.Unix_error (e,_,_) -> report (Unix.error_message e) in
    if List.mem canonical active then
      report ("import cycle: " ^ String.concat " -> " (List.rev (canonical::active)));
    if Hashtbl.mem seen canonical then [] else (
      let source = try read_file canonical with Sys_error msg -> report msg in
      let declarations = List.concat_map (function
        | Declaration d -> [d]
        | Import(t,p) ->
            let target = if Filename.is_relative p then
              Filename.concat (Filename.dirname canonical) p else p in
            visit (canonical::active) (Some t) target)
        (parse_items ~file:canonical source) in
      Hashtbl.add seen canonical ();
      declarations)
  in visit [] None path

(** Resolves names in expression [expr] into kernel terms [Term.t].
    - Scopes local variables from innermost outward to de Bruijn indices ([Term.Var i]).
    - Scopes global constants against prior declarations [globals] to constant indices ([Term.Const i]).
    - Rejects unknown names, forward references, and duplicate names. *)
let resolve globals at expr =
  let rec go locals = function
    | Universe -> Term.Type | Top -> Term.Kind
    | Name n ->
        let rec find i = function
          | [] -> None
          | x::xs -> if x=Some n then Some i else find (i+1) xs
        in (match find 0 locals with
          | Some i -> Term.Var i
          | None -> (match List.assoc_opt n globals with
            | Some i -> Term.Const i | None -> error at ("unknown name: " ^ n)))
    | Apply(f,x) -> Term.App(go locals f,go locals x)
    | Product(x,a,b) -> Term.Pi(go locals a,go (x::locals) b)
    | Lambda(x,a,b) -> Term.Lam(go locals a,go (Some x::locals) b)
  in go [] expr

(** Source mapping entry associating a byte range in the generated assembly with source location. *)
type mapping = {
  constant : int;          (** Assigned constant index (0-indexed). *)
  name : string;           (** Original declaration name. *)
  file : string option;    (** Canonical file path, or [None] for string inputs. *)
  line : int;              (** 1-based declaration line number. *)
  column : int;            (** 1-based declaration column byte offset. *)
  start_byte : int;        (** Start byte offset in generated .pa assembly (inclusive). *)
  end_byte : int;          (** End byte offset in generated .pa assembly (exclusive). *)
}

(** Compilation result record. *)
type compiled = {
  assembly : string;              (** Serialized .pa assembly instructions. *)
  names : string list;            (** Declared constant names in registration order. *)
  declarations : declaration list;(** Expanded declaration ASTs. *)
  sourcemap : mapping list;       (** Declaration-level source mappings. *)
}

(** Escapes a string into a JSON string literal. *)
let json_string s =
  let b = Buffer.create (String.length s + 2) in
  Buffer.add_char b '"';
  String.iter (function
    | '"' -> Buffer.add_string b "\\\""
    | '\\' -> Buffer.add_string b "\\\\"
    | c when Char.code c < 0x20 ->
        Buffer.add_string b (Printf.sprintf "\\u%04x" (Char.code c))
    | c -> Buffer.add_char b c) s;
  Buffer.add_char b '"'; Buffer.contents b

(** Serializes source mappings into JSON. *)
let sourcemap_json result =
  let entries = List.map (fun (m:mapping) ->
    Printf.sprintf
      "    {\"constant\":%d,\"name\":%s,\"file\":%s,\"line\":%d,\"column\":%d,\"start_byte\":%d,\"end_byte\":%d}"
      m.constant (json_string m.name)
      (match m.file with None -> "null" | Some p -> json_string p)
      m.line m.column m.start_byte m.end_byte) result.sourcemap in
  "{\"version\":1,\"mappings\":[\n" ^ String.concat ",\n" entries ^ "\n]}\n"

(** Annotates an assembly-level byte offset error with the matching declaration's source location.
    Returns the original message unchanged if the byte offset falls outside mapped ranges. *)
let annotate_assembly_error mappings message =
  let offset =
    try
      if not (String.starts_with ~prefix:"byte " message) then None else
      let colon = String.index message ':' in
      Some (int_of_string (String.sub message 5 (colon - 5)))
    with Not_found | Failure _ | Invalid_argument _ -> None in
  match offset with
  | None -> message
  | Some offset ->
      match List.find_opt (fun (m : mapping) ->
        m.start_byte <= offset && offset < m.end_byte) mappings with
      | None -> message
      | Some m ->
          Printf.sprintf "%s%d:%d (%s): %s"
            (match m.file with None -> "" | Some file -> file ^ ":")
            m.line m.column m.name message

(** Resolves names, generates .pa assembly, and verifies the serialized output through a fresh kernel.
    @raise Error if verification fails (annotated with source location). *)
let compile_declarations ?(fuel=1_000_000) declarations =
  let globals = ref [] in
  let names = ref [] in
  let output = Buffer.create 256 in
  let mappings = ref [] in
  List.iteri (fun constant (d:declaration) ->
    let start_byte = Buffer.length output in
    if List.mem_assoc d.name !globals then error d.at ("duplicate declaration: " ^ d.name);
    let typ = resolve !globals d.at d.typ in
    Buffer.add_string output (Tinyprover_pa.Writer.encode typ);
    (match d.body with
     | None -> Buffer.add_char output ':'
     | Some b -> Buffer.add_string output (Tinyprover_pa.Writer.encode (resolve !globals d.at b));
         Buffer.add_char output '!');
    let end_byte = Buffer.length output in
    mappings := {constant; name=d.name; file=d.at.file; line=d.at.line;
      column=d.at.col; start_byte; end_byte} :: !mappings;
    Buffer.add_char output '\n';
    globals := (d.name,List.length !names)::!globals;
    names := !names @ [d.name]) declarations;
  let assembly = Buffer.contents output in
  (* Verify precisely the serialized output through the independent assembly reader and kernel *)
  (try Assembly.run (Kernel.create ~fuel ()) assembly
   with Assembly.Error message ->
     raise (Error (annotate_assembly_error (List.rev !mappings) message)));
  {assembly; names= !names; declarations; sourcemap=List.rev !mappings}

(** Compiles source code from a string into verified assembly and source mappings. *)
let compile ?fuel source = compile_declarations ?fuel (parse source)

(** Compiles a file and all its transitive imports into verified assembly and source mappings. *)
let compile_file ?fuel path = compile_declarations ?fuel (load path)
