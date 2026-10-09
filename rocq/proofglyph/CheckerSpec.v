From Stdlib Require Import List.
From Tinyprover.Proofglyph Require Export Syntax EvaluationSpec.
Import ListNotations.

Inductive synthesizes (sg : list term) : list term -> term -> term -> Prop :=
| ds_type : forall ctx, synthesizes sg ctx tType tKind
| ds_var : forall ctx n a, nth_error ctx n = Some a ->
    synthesizes sg ctx (tVar n) (shift (S n) 0 a)
| ds_const : forall ctx n a, nth_error sg n = Some a -> synthesizes sg ctx (tConst n) a
| ds_pi : forall ctx a b aty bt s,
    synthesizes sg ctx a aty -> evaluates aty tType ->
    synthesizes sg (a :: ctx) b bt -> evaluates bt s -> is_sort s ->
    synthesizes sg ctx (tPi a b) s
| ds_lam : forall ctx a b aty bt,
    synthesizes sg ctx a aty -> evaluates aty tType ->
    synthesizes sg (a :: ctx) b bt -> bt <> tKind ->
    synthesizes sg ctx (tLam a b) (tPi a bt)
| ds_app : forall ctx f x ft a b xt u,
    synthesizes sg ctx f ft -> evaluates ft (tPi a b) ->
    synthesizes sg ctx x xt -> evaluates xt u -> evaluates a u ->
    synthesizes sg ctx (tApp f x) (instantiate b x).

