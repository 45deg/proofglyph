From Stdlib Require Import List String Arith Lia.
Import ListNotations.
From Tinyprover.Proofglyph Require Export Syntax.
From Tinyprover.Hieratic Require Export Surface.

Inductive binds (x : string) : locals -> nat -> Prop :=
| binds_here : forall ns, binds x (Some x :: ns) 0
| binds_later : forall n ns i,
    n <> Some x -> binds x ns i -> binds x (n :: ns) (S i).

Lemma binds_bound x ns i : binds x ns i -> i < List.length ns.
Proof. intros H; induction H; cbn; lia. Qed.

Lemma binds_append x ns i extra : binds x ns i -> binds x (ns ++ extra) i.
Proof. intros H; induction H; cbn; constructor; assumption. Qed.

Inductive resolves (gs : globals) : locals -> expr -> term -> Prop :=
| resolves_local : forall ls x i,
    binds x ls i -> resolves gs ls (Name x) (tVar i)
| resolves_global : forall ls x i,
    ~ In (Some x) ls -> binds x (map (@Some string) gs) i ->
    resolves gs ls (Name x) (tConst i)
| resolves_type : forall ls, resolves gs ls Universe tType
| resolves_kind : forall ls, resolves gs ls Top tKind
| resolves_app : forall ls f x f' x',
    resolves gs ls f f' -> resolves gs ls x x' ->
    resolves gs ls (Apply f x) (tApp f' x')
| resolves_pi : forall ls x a b a' b',
    resolves gs ls a a' -> resolves gs (x :: ls) b b' ->
    resolves gs ls (Product x a b) (tPi a' b')
| resolves_lam : forall ls x a b a' b',
    resolves gs ls a a' -> resolves gs (Some x :: ls) b b' ->
    resolves gs ls (Lambda x a b) (tLam a' b').

Theorem resolves_extend_globals gs ls e t extra :
  resolves gs ls e t -> resolves (gs ++ extra) ls e t.
Proof.
  intros H; induction H.
  - constructor; assumption.
  - apply resolves_global; [assumption|].
    rewrite map_app; apply binds_append; assumption.
  - constructor.
  - constructor.
  - constructor; assumption.
  - constructor; assumption.
  - constructor; assumption.
Qed.

Fixpoint scoped (constants depth : nat) (t : term) : Prop :=
  match t with
  | tVar i => i < depth
  | tConst i => i < constants
  | tPi a b | tLam a b => scoped constants depth a /\ scoped constants (S depth) b
  | tApp f x => scoped constants depth f /\ scoped constants depth x
  | _ => True
  end.

Theorem resolves_scoped gs ls e t :
  resolves gs ls e t -> scoped (List.length gs) (List.length ls) t.
Proof.
  intros H; induction H; cbn in *.
  - eapply binds_bound; eauto.
  - match goal with B : binds _ (map _ _) _ |- _ =>
      pose proof (binds_bound _ _ _ B) as L; rewrite length_map in L; exact L end.
  - exact I.
  - exact I.
  - auto.
  - auto.
  - auto.
Qed.


Lemma binds_member x ns i : binds x ns i -> In (Some x) ns.
Proof. intros H; induction H; cbn; auto. Qed.
Lemma binds_unique x ns i j : binds x ns i -> binds x ns j -> i = j.
Proof.
  intros A; revert j; induction A; intros j B; inversion B; subst; try reflexivity;
    try contradiction; f_equal; auto.
Qed.
Theorem resolves_unique gs ls e t u : resolves gs ls e t -> resolves gs ls e u -> t = u.
Proof.
  intros A; revert u; induction A; intros u B; inversion B; subst;
    try (f_equal; eauto using binds_unique; fail).
  all: exfalso; eauto using binds_member.
Qed.
