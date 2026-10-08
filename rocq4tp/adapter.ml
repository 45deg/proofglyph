(* Host I/O boundary and reference AST adapters used by differential tests. *)
module Source = Tinyprover_tp.Source
module F = Frontend

let chars s = List.init (String.length s) (String.get s)
let string_of_chars cs = String.of_seq (List.to_seq cs)

let rec expression = function
  | Source.Name x -> F.Name (chars x)
  | Source.Universe -> F.Universe
  | Source.Top -> F.Top
  | Source.Apply (f, x) -> F.Apply (expression f, expression x)
  | Source.Product (x, a, b) ->
      F.Product (Option.map chars x, expression a, expression b)
  | Source.Lambda (x, a, b) -> F.Lambda (chars x, expression a, expression b)

let declaration (d : Source.declaration) =
  { F.decl_name = chars d.name; decl_type = expression d.typ;
    decl_body = Option.map expression d.body }

let declarations ds = List.map declaration ds

let rec parameters = function
  | [] -> F.PNil
  | (first :: others, typ) :: rest ->
      F.PGroup (chars first, List.map chars others, typ, parameters rest)
  | ([], _) :: _ -> invalid_arg "parser produced an empty parameter group"

let raw_syntax : F.raw_expr Source.syntax = {
  name_expr = (fun n -> F.RName (chars n));
  universe_expr = F.RType; top_expr = F.RKind;
  apply_expr = (fun f x -> F.RApply (f, x));
  arrow_expr = (fun a b -> F.RArrow (a, b));
  forall_expr = (fun ps b -> F.RForall (parameters ps, b));
  lambda_expr = (fun ps b -> F.RLambda (parameters ps, b));
}

let raw_declaration (d : F.raw_expr Source.parsed_declaration) =
  { F.raw_name = chars d.name; raw_type = d.typ; raw_body = d.body }

(* Parsing and graph expansion run in extracted code. Only byte I/O and
   canonical path resolution are host operations. The old algebra above is
   retained for differential tests. *)
let parse_items ?file source =
  match F.parse_tp (chars source) with
  | Some items -> items
  | None -> raise (Source.Error ((match file with None -> "" | Some p -> p ^ ": ") ^
      "invalid .tp syntax or lexical input"))

let parse_raw source =
  List.map (function
    | F.TpDeclaration d -> d
    | F.TpImport _ -> raise (Source.Error "imports require load_raw"))
    (parse_items source)

let load_raw path =
  let canonical path =
    try Unix.realpath path with
    | Unix.Unix_error (e, _, _) -> raise (Source.Error (path ^ ": " ^ Unix.error_message e))
    | Invalid_argument msg -> raise (Source.Error (path ^ ": " ^ msg)) in
  let files = Hashtbl.create 16 in
  let rec discover path =
    if not (Hashtbl.mem files path) then (
      (* Register before walking dependencies so discovery terminates on cycles.
         The extracted traversal decides whether the graph is acceptable. *)
      Hashtbl.add files path [];
      let items = parse_items ~file:path (Source.read_file path) in
      let items = List.map (function
        | F.TpDeclaration d -> F.TpDeclaration d
        | F.TpImport p ->
            let target = string_of_chars p in
            let target = canonical (if Filename.is_relative target then
              Filename.concat (Filename.dirname path) target else target) in
            discover target;
            F.TpImport (chars target)) items in
      Hashtbl.replace files path items) in
  let entry = canonical path in
  discover entry;
  let table = Hashtbl.fold (fun path items acc -> (chars path, items) :: acc) files [] in
  match F.load_tp table (chars entry) with
  | Some ds -> ds
  | None -> raise (Source.Error (entry ^ ": import cycle or exhausted import traversal budget"))

let nat_of_int n =
  if n < 0 then invalid_arg "negative natural";
  let rec loop n acc = if n = 0 then acc else loop (n - 1) (F.S acc) in
  loop n F.O
