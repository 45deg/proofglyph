open Tinyprover_core.Term

(** [encode term] serializes [term] into the reverse-Polish notation of the .pa assembly language:
    - [Type] -> [*]
    - [Kind] -> [^]
    - [Var n] -> [$n]
    - [Const n] -> [#n]
    - [Pi (a,b)] -> [encode a] [encode b] [>]
    - [Lam (a,b)] -> [encode a] [encode b] [\]
    - [App (f,x)] -> [encode f] [encode x] [@] *)
let encode term =
  let b = Buffer.create 64 in
  let rec go = function
    | Type -> Buffer.add_char b '*'
    | Kind -> Buffer.add_char b '^'
    | Var n -> Buffer.add_string b ("$" ^ string_of_int n)
    | Const n -> Buffer.add_string b ("#" ^ string_of_int n)
    | Pi (a,c) -> go a; go c; Buffer.add_char b '>'
    | Lam (a,c) -> go a; go c; Buffer.add_char b '\\'
    | App (f,x) -> go f; go x; Buffer.add_char b '@'
  in go term; Buffer.contents b

