type t = Type | Kind | Var of int | Const of int | Pi of t * t | Lam of t * t | App of t * t

let rec shift delta cutoff = function
  | Var n -> if n >= cutoff then Var (n + delta) else Var n
  | Pi (a,b) -> Pi (shift delta cutoff a, shift delta (cutoff+1) b)
  | Lam (a,b) -> Lam (shift delta cutoff a, shift delta (cutoff+1) b)
  | App (f,x) -> App (shift delta cutoff f, shift delta cutoff x)
  | (Type | Kind | Const _) as t -> t

(* Substitute for the outermost variable, removing its binder. *)
let instantiate body value =
  let rec go depth = function
    | Var n when n = depth -> shift depth 0 value
    | Var n when n > depth -> Var (n-1)
    | Var n -> Var n
    | Pi (a,b) -> Pi (go depth a, go (depth+1) b)
    | Lam (a,b) -> Lam (go depth a, go (depth+1) b)
    | App (f,x) -> App (go depth f, go depth x)
    | (Type | Kind | Const _) as t -> t
  in go 0 body

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

let pretty ?(names = fun n -> "c" ^ string_of_int n) t =
  let rec go ctx = function
    | Type -> "Type" | Kind -> "Kind"
    | Var n -> (try List.nth ctx n with _ -> "$" ^ string_of_int n)
    | Const n -> names n
    | App (f,x) -> "(" ^ go ctx f ^ " " ^ go ctx x ^ ")"
    | Pi (a,b) -> binder "forall" ", " ctx a b
    | Lam (a,b) -> binder "fun" " => " ctx a b
  and binder keyword sep ctx a b =
    let x = "$x" ^ string_of_int (List.length ctx) in
    "(" ^ keyword ^ " (" ^ x ^ " : " ^ go ctx a ^ ")" ^ sep ^ go (x::ctx) b ^ ")"
  in go [] t
