From Stdlib Require Import List.
From Tinyprover.Pa Require Export Syntax.
Import ListNotations.

Inductive evaluates : term -> term -> Prop :=
| ev_type : evaluates tType tType
| ev_kind : evaluates tKind tKind
| ev_var : forall n, evaluates (tVar n) (tVar n)
| ev_const : forall n, evaluates (tConst n) (tConst n)
| ev_pi : forall a b a' b', evaluates a a' -> evaluates b b' ->
    evaluates (tPi a b) (tPi a' b')
| ev_lam : forall a b a' b', evaluates a a' -> evaluates b b' ->
    evaluates (tLam a b) (tLam a' b')
| ev_app : forall f x f' x', evaluates f f' -> evaluates x x' ->
    (forall a b, f' <> tLam a b) -> evaluates (tApp f x) (tApp f' x')
| ev_beta : forall f x a b x' u, evaluates f (tLam a b) -> evaluates x x' ->
    evaluates (instantiate b x') u -> evaluates (tApp f x) u.


Lemma evaluation_conv t u : evaluates t u -> conv t u.
Proof.
  intros H; induction H; eauto using conv.
Qed.
