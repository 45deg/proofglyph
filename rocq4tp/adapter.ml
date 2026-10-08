(* Unverified input boundary. Reuse the lexer, parser and import loader with an
   algebra that preserves sugar. Desugaring itself runs in extracted Rocq code. *)
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

let parse_raw source = Source.parse_with raw_syntax source |> List.map raw_declaration
let load_raw path = Source.load_with raw_syntax path |> List.map raw_declaration

let nat_of_int n =
  if n < 0 then invalid_arg "negative natural";
  let rec loop n acc = if n = 0 then acc else loop (n - 1) (F.S acc) in
  loop n F.O
