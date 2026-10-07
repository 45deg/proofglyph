(** {1 Term Representation and Basic Operations}

    Provides the abstract syntax tree (AST) for types and terms in the λΠ-calculus
    (an LF-style dependent type theory), de Bruijn index operations (shifting and substitution),
    and pretty-printing to human-readable strings. *)

(** Abstract syntax tree for terms and types.
    In this system, terms and types share the same syntax.
    Variable bindings use de Bruijn indices, where [Var 0] refers to the innermost bound variable. *)
type t =
  | Type          (** Universe [Type] : [Kind] *)
  | Kind          (** Super-universe [Kind]; has no type of its own *)
  | Var of int    (** Bound variable identified by its de Bruijn index (>= 0) *)
  | Const of int  (** Global constant identifier, numbered sequentially from 0 *)
  | Pi of t * t   (** Dependent product type [Π (x:A). B]. Only the second argument [B] binds a variable *)
  | Lam of t * t  (** Lambda abstraction [λ (x:A). b]. Only the second argument [b] binds a variable *)
  | App of t * t  (** Function application [f x] *)

(** [shift delta cutoff t] adjusts the de Bruijn indices of free variables in term [t].
    - [delta]: index adjustment (+1 when introducing a binder, -1 when removing one)
    - [cutoff]: current binding depth. Only variables with indices >= cutoff are shifted.
    When descending into the body of [Pi] or [Lam], [cutoff] is incremented by 1. *)
let rec shift delta cutoff = function
  | Var n -> if n >= cutoff then Var (n + delta) else Var n
  | Pi (a,b) -> Pi (shift delta cutoff a, shift delta (cutoff+1) b)
  | Lam (a,b) -> Lam (shift delta cutoff a, shift delta (cutoff+1) b)
  | App (f,x) -> App (shift delta cutoff f, shift delta cutoff x)
  | (Type | Kind | Const _) as t -> t

(** [instantiate body value] substitutes [value] for the outermost variable (index 0) in [body],
    stripping the corresponding binder (used for β-reduction: [(λ x. body) value → body[value/x]]).
    - [Var n] matching [depth] is replaced with [value] shifted to [depth].
    - Free variables [Var n] with [n > depth] have their indices decremented by 1.
    - Bound variables [Var n] with [n < depth] remain unchanged. *)
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

(** [pretty ?names t] formats [term] into a human-readable string.
    Bound variables are named [$x0], [$x1], ... according to their binding depth.
    - [names]: function mapping constant indices to identifiers (defaults to "c" ^ index). *)
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
