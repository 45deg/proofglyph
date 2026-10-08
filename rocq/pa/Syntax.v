From Stdlib Require Import List PeanoNat Bool.
Import ListNotations.

Inductive term : Type :=
| tType | tKind
| tVar (n : nat) | tConst (n : nat)
| tPi (a b : term) | tLam (a b : term) | tApp (f x : term).

Fixpoint term_eq_dec (a b : term) : {a = b} + {a <> b}.
Proof. decide equality; apply Nat.eq_dec. Defined.

Fixpoint shift (delta cutoff : nat) (t : term) : term :=
  match t with
  | tVar n => tVar (if cutoff <=? n then n + delta else n)
  | tPi a b => tPi (shift delta cutoff a) (shift delta (S cutoff) b)
  | tLam a b => tLam (shift delta cutoff a) (shift delta (S cutoff) b)
  | tApp f x => tApp (shift delta cutoff f) (shift delta cutoff x)
  | t => t
  end.

Fixpoint subst (depth : nat) (value body : term) : term :=
  match body with
  | tVar n => if n =? depth then shift depth 0 value
              else tVar (if depth <? n then pred n else n)
  | tPi a b => tPi (subst depth value a) (subst (S depth) value b)
  | tLam a b => tLam (subst depth value a) (subst (S depth) value b)
  | tApp f x => tApp (subst depth value f) (subst depth value x)
  | t => t
  end.

Definition instantiate body value := subst 0 value body.

(** Raw beta convertibility: no eta, unfolding, or proof irrelevance. *)
Inductive conv : term -> term -> Prop :=
| cv_refl : forall t, conv t t
| cv_sym : forall a b, conv a b -> conv b a
| cv_trans : forall a b c, conv a b -> conv b c -> conv a c
| cv_pi : forall a a' b b', conv a a' -> conv b b' -> conv (tPi a b) (tPi a' b')
| cv_lam : forall a a' b b', conv a a' -> conv b b' -> conv (tLam a b) (tLam a' b')
| cv_app : forall f f' x x', conv f f' -> conv x x' -> conv (tApp f x) (tApp f' x')
| cv_beta : forall a b x, conv (tApp (tLam a b) x) (instantiate b x).

Definition is_sort t := t = tType \/ t = tKind.
Definition sortb t := match t with tType | tKind => true | _ => false end.

Lemma sortb_sound t : sortb t = true -> is_sort t.
Proof. destruct t; simpl; intros; try discriminate; unfold is_sort; auto. Qed.

(** Declarative type assignment modulo beta. Context entries are relative
    to the context before the variable was introduced; constants are closed.
    Well-formed contexts/signatures are enforced by construction in the checker.
    This judgment itself deliberately permits arbitrary contexts/signatures. *)
Inductive typing (sg : list term) : list term -> term -> term -> Prop :=
| ty_type : forall ctx, typing sg ctx tType tKind
| ty_var : forall ctx n a, nth_error ctx n = Some a ->
    typing sg ctx (tVar n) (shift (S n) 0 a)
| ty_const : forall ctx n a, nth_error sg n = Some a ->
    typing sg ctx (tConst n) a
| ty_pi : forall ctx a b s, typing sg ctx a tType ->
    typing sg (a :: ctx) b s -> is_sort s -> typing sg ctx (tPi a b) s
| ty_lam : forall ctx a b bt s, typing sg ctx a tType ->
    typing sg (a :: ctx) b bt -> typing sg ctx (tPi a bt) s ->
    is_sort s -> typing sg ctx (tLam a b) (tPi a bt)
| ty_app : forall ctx f x a b, typing sg ctx f (tPi a b) ->
    typing sg ctx x a -> typing sg ctx (tApp f x) (instantiate b x)
| ty_conv : forall ctx t a b, typing sg ctx t a -> conv a b -> typing sg ctx t b.
