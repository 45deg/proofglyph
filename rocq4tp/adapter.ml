(* Unverified input boundary. Reuse the existing lexer, parser, desugaring and
   import loader, but never Source.resolve, Source.compile or the OCaml kernel. *)
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

let nat_of_int n =
  if n < 0 then invalid_arg "negative natural";
  let rec loop n acc = if n = 0 then acc else loop (n - 1) (F.S acc) in
  loop n F.O
