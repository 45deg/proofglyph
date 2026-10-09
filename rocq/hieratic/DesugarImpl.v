From Stdlib Require Import List String Arith Lia.
Import ListNotations.
From Proofglyph.Hieratic Require Export DesugarSpec.

Fixpoint bind_products (ps : bindings) (body : expr) : expr :=
  match ps with [] => body | (x, a) :: rest => Product (Some x) a (bind_products rest body) end.
Fixpoint bind_lambdas (ps : bindings) (body : expr) : expr :=
  match ps with [] => body | (x, a) :: rest => Lambda x a (bind_lambdas rest body) end.

Fixpoint desugar (e : raw_expr) : expr :=
  match e with
  | RName x => Name x | RType => Universe | RKind => Top
  | RApply f x => Apply (desugar f) (desugar x)
  | RArrow a b => Product None (desugar a) (desugar b)
  | RForall ps b => bind_products (desugar_parameters ps) (desugar b)
  | RLambda ps b => bind_lambdas (desugar_parameters ps) (desugar b)
  end
with desugar_parameters (ps : parameters) : bindings :=
  match ps with
  | PNil => []
  | PGroup x xs a rest =>
      map (fun n => (n, desugar a)) (x :: xs) ++ desugar_parameters rest
  end.

(** Relational specifications are independent of the executable folds. Each
    copied annotation is resolved later in its own sequential binder scope. *)
Definition desugar_declaration d :=
  Decl (raw_name d) (desugar (raw_type d)) (option_map desugar (raw_body d)).
Definition desugar_program := map desugar_declaration.

