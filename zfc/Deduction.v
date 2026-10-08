From Stdlib Require Import List PeanoNat Bool Lia.
From Zfc Require Import Formula Axioms Semantics.
Import ListNotations.

(** Capture-avoiding instantiation of the outermost variable by a free
    variable x. rename lifts this map under every nested binder. *)
Definition unbind x i := match i with 0 => x | S j => j end.
Definition instantiate_formula x p := rename (unbind x) p.
Definition lift_hypotheses := map (rename S).

(** Classical natural deduction for pure first-order set theory. Generalization
    raises all hypotheses, so the new variable cannot occur freely in them. *)
Inductive derives : nat -> list formula -> formula -> Prop :=
| nd_assume : forall n gamma p, scoped n p = true -> In p gamma -> derives n gamma p
| nd_axiom : forall n gamma p, zfc_axiom p -> derives n gamma p
| nd_imp_intro : forall n gamma p q, scoped n p = true ->
    derives n (p :: gamma) q -> derives n gamma (Implies p q)
| nd_imp_elim : forall n gamma p q,
    derives n gamma (Implies p q) -> derives n gamma p -> derives n gamma q
| nd_false : forall n gamma p, scoped n p = true -> derives n gamma Bot -> derives n gamma p
| nd_classical : forall n gamma p, scoped n p = true ->
    derives n (Neg p :: gamma) Bot -> derives n gamma p
| nd_all_intro : forall n gamma p,
    derives (S n) (lift_hypotheses gamma) p -> derives n gamma (Forall p)
| nd_all_elim : forall n gamma p x, x < n -> derives n gamma (Forall p) ->
    derives n gamma (instantiate_formula x p)
| nd_eq_refl : forall n gamma x, x < n -> derives n gamma (Equal x x)
| nd_eq_subst : forall n gamma p x y, scoped (S n) p = true -> x < n -> y < n ->
    derives n gamma (Equal x y) -> derives n gamma (instantiate_formula x p) ->
    derives n gamma (instantiate_formula y p).

Definition ZFC_proves p := derives 0 [] p.

Lemma scoped_monotone p : forall n m, n <= m -> scoped n p = true -> scoped m p = true.
Proof.
  induction p; intros n0 m L H; cbn in *; try reflexivity.
  - apply andb_true_iff in H as [X Y]; apply andb_true_iff; split;
      apply Nat.ltb_lt; apply Nat.ltb_lt in X; apply Nat.ltb_lt in Y; lia.
  - apply andb_true_iff in H as [X Y]; apply andb_true_iff; split;
      apply Nat.ltb_lt; apply Nat.ltb_lt in X; apply Nat.ltb_lt in Y; lia.
  - apply andb_true_iff in H as [P Q]; apply andb_true_iff; split; eauto.
  - apply (IHp (S n0) (S m)); [lia|exact H].
Qed.

Theorem derives_scoped n gamma p : derives n gamma p -> scoped n p = true.
Proof.
  intros H; induction H; cbn [scoped] in *; auto.
  - eapply scoped_monotone with (n := 0); [lia|apply all_axioms_closed; exact H].
  - apply andb_true_iff; auto.
  - apply andb_true_iff in IHderives1 as [_ Q]; exact Q.
  - unfold instantiate_formula; eapply rename_scoped; [|exact IHderives].
    intros [|i] L; cbn [unbind]; lia.
  - apply andb_true_iff; split; apply Nat.ltb_lt; assumption.
  - unfold instantiate_formula; eapply rename_scoped; [|exact H].
    intros [|i] L; cbn [unbind]; lia.
Qed.

Corollary provable_sentence p : ZFC_proves p -> sentence p.
Proof. apply derives_scoped. Qed.

Section Soundness.
Context {D : Type} (member : D -> D -> Prop).
Context (dne : forall P : Prop, ((P -> False) -> False) -> P).
Context (model : forall p, zfc_axiom p -> forall env, holds member env p).

Lemma instantiation_meaning env x p :
  holds member env (instantiate_formula x p) <->
  holds member (extend (env x) env) p.
Proof.
  unfold instantiate_formula; rewrite holds_rename.
  apply holds_ext; intros [|i]; reflexivity.
Qed.

Theorem derives_sound n gamma p : derives n gamma p ->
  forall env, (forall q, In q gamma -> holds member env q) -> holds member env p.
Proof.
  intros H; induction H; intros env G; cbn [holds].
  - apply G; assumption.
  - apply model; assumption.
  - intros P; apply IHderives; intros r [E|IN]; [subst; exact P|apply G; exact IN].
  - apply (IHderives1 env G); apply IHderives2; exact G.
  - exfalso; apply (IHderives env G).
  - apply dne; intros N; apply (IHderives env).
    intros q [E|IN]; [subst; exact N|apply G; exact IN].
  - intros x; apply IHderives; intros q IN.
    apply in_map_iff in IN as [r [E IN]]; subst q.
    apply (proj2 (holds_rename member r (extend x env) S)).
    change (holds member env r); apply G; exact IN.
  - apply (proj2 (instantiation_meaning env x p)); apply (IHderives env G).
  - reflexivity.
  - apply (proj2 (instantiation_meaning env y p)).
    pose proof (IHderives1 env G) as E; cbn [holds] in E.
    rewrite <- E; apply (proj1 (instantiation_meaning env x p)); apply IHderives2; exact G.
Qed.

Corollary ZFC_proves_sound p : ZFC_proves p -> forall env, holds member env p.
Proof. intros H env; eapply derives_sound; [exact H|intros q Hq; inversion Hq]. Qed.
End Soundness.

Example equality_reflexive : ZFC_proves (Forall (Equal 0 0)).
Proof. apply nd_all_intro; apply nd_eq_refl; lia. Qed.
Example excluded_middle p : sentence p -> ZFC_proves (Or p (Neg p)).
Proof.
  intros H; unfold sentence in H; unfold Or.
  assert (N : scoped 0 (Neg p) = true) by (cbn [Neg scoped]; rewrite H; reflexivity).
  apply nd_imp_intro; [exact N|].
  apply nd_assume; [exact N|left; reflexivity].
Qed.

Print Assumptions derives_scoped.
Print Assumptions derives_sound.
Print Assumptions ZFC_proves_sound.

Example equality_symmetry : ZFC_proves
  (Forall (Forall (Implies (Equal 1 0) (Equal 0 1)))).
Proof.
  apply nd_all_intro; apply nd_all_intro; apply nd_imp_intro; [reflexivity|].
  change (derives 2 [Equal 1 0] (instantiate_formula 0 (Equal 0 2))).
  eapply nd_eq_subst with (x := 1); try reflexivity; try lia.
  - apply nd_assume; [reflexivity|left; reflexivity].
  - change (derives 2 [Equal 1 0] (Equal 1 1)); apply nd_eq_refl; lia.
Qed.

Example equality_transitivity : ZFC_proves
  (Forall (Forall (Forall
    (Implies (Equal 2 1) (Implies (Equal 1 0) (Equal 2 0)))))).
Proof.
  apply nd_all_intro; apply nd_all_intro; apply nd_all_intro.
  apply nd_imp_intro; [reflexivity|]; apply nd_imp_intro; [reflexivity|].
  change (derives 3 [Equal 1 0; Equal 2 1] (instantiate_formula 0 (Equal 3 0))).
  eapply nd_eq_subst with (x := 1); try reflexivity; try lia.
  - apply nd_assume; [reflexivity|left; reflexivity].
  - change (derives 3 [Equal 1 0; Equal 2 1] (Equal 2 1)).
    apply nd_assume; [reflexivity|right; left; reflexivity].
Qed.
