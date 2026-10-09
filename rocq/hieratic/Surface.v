From Stdlib Require Import List String.
Import ListNotations.

(** The desugared, named AST at the boundary of Proofglyph_hieratic.Source.resolve.
    Parsing, grouped parameters, locations and imports are outside this layer. *)
Inductive expr :=
| Name (x : string)
| Universe | Top
| Apply (f x : expr)
| Product (x : option string) (a b : expr)
| Lambda (x : string) (a b : expr).

Record source_decl := Decl {
  decl_name : string;
  decl_type : expr;
  decl_body : option expr
}.

(** None is a real binder, but cannot be looked up by name. *)
Definition locals := list (option string).
(** Oldest first: position is the stable constant number. *)
Definition globals := list string.

Definition is_assumption (d : source_decl) : bool :=
  match decl_body d with None => true | Some _ => false end.
