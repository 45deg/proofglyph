From Stdlib Require Import List PeanoNat Bool Lia.
From Zfc Require Import Formula Axioms Semantics Deduction.
Import ListNotations.

(** Structural and propositional rules, derived from the existing constructors. *)
Lemma weaken_hypotheses n g p : derives n g p -> forall h,
  (forall q, In q g -> In q h) -> derives n h p.
Proof.
  intros D; induction D; intros h Inc.
  - apply nd_assume; auto.
  - apply nd_axiom; assumption.
  - apply nd_imp_intro; [assumption|]. apply IHD; intros r [E|IN]; [left; exact E|right; apply Inc; exact IN].
  - eapply nd_imp_elim; [apply IHD1|apply IHD2]; exact Inc.
  - apply nd_false; [assumption|apply IHD; exact Inc].
  - apply nd_classical; [assumption|]. apply IHD; intros r [E|IN]; [left; exact E|right; apply Inc; exact IN].
  - apply nd_all_intro; apply IHD; intros r IN.
    apply in_map_iff in IN as [q [E IN]]; subst r; apply in_map; apply Inc; exact IN.
  - apply nd_all_elim; [assumption|apply IHD; exact Inc].
  - apply nd_eq_refl; assumption.
  - eapply nd_eq_subst with (p := p) (x := x) (y := y); eauto.
Qed.
Lemma weaken_cons n g p q : derives n g p -> derives n (q :: g) p.
Proof. intros D; eapply weaken_hypotheses; [exact D|intros r IN; right; exact IN]. Qed.
Lemma and_scopes n p q : scoped n (And p q) = true -> scoped n p = true /\ scoped n q = true.
Proof. cbn [And Neg scoped]; rewrite !andb_true_iff; tauto. Qed.
Lemma and_left n g p q : derives n g (And p q) -> derives n g p.
Proof.
  intros D; destruct (and_scopes _ _ _ (derives_scoped _ _ _ D)) as [P Q].
  apply nd_classical; [exact P|].
  eapply nd_imp_elim with (p := Implies p (Neg q)); [apply weaken_cons; exact D|].
  apply nd_imp_intro; [exact P|].
  apply nd_false; [cbn [Neg scoped]; rewrite Q; reflexivity|].
  eapply nd_imp_elim with (p := p).
  - apply nd_assume; [cbn [Neg scoped]; rewrite P; reflexivity|right; left; reflexivity].
  - apply nd_assume; [exact P|left; reflexivity].
Qed.
Lemma and_right n g p q : derives n g (And p q) -> derives n g q.
Proof.
  intros D; destruct (and_scopes _ _ _ (derives_scoped _ _ _ D)) as [P Q].
  apply nd_classical; [exact Q|].
  eapply nd_imp_elim with (p := Implies p (Neg q)); [apply weaken_cons; exact D|].
  apply nd_imp_intro; [exact P|].
  apply nd_assume; [cbn [Neg scoped]; rewrite Q; reflexivity|right; left; reflexivity].
Qed.
Lemma and_intro n g p q : derives n g p -> derives n g q -> derives n g (And p q).
Proof.
  intros P Q; unfold And, Neg.
  apply nd_imp_intro; [cbn [scoped]; rewrite (derives_scoped _ _ _ P), (derives_scoped _ _ _ Q); reflexivity|].
  eapply nd_imp_elim with (p := q); [|apply weaken_cons; exact Q].
  eapply nd_imp_elim with (p := p); [|apply weaken_cons; exact P].
  apply nd_assume; [cbn [scoped]; rewrite (derives_scoped _ _ _ P), (derives_scoped _ _ _ Q); reflexivity|left; reflexivity].
Qed.

(** Exists p is Not (Forall (Not p)), so refuting every witness suffices. *)
Lemma exists_absurd n g p : scoped (S n) p = true ->
  derives n g (Exists p) -> derives (S n) (p :: lift_hypotheses g) Bot -> derives n g Bot.
Proof.
  intros P E B; eapply nd_imp_elim; [exact E|].
  apply nd_all_intro; apply nd_imp_intro; [exact P|exact B].
Qed.

Definition universal_set := Exists (Forall (Member 0 1)).
Definition no_universal_set := Neg universal_set.
Definition russell_predicate := Neg (Member 0 0).
Definition russell_property := Forall
  (Iff (Member 0 1) (And (Member 0 2) (Neg (Member 0 0)))).
Example no_universal_set_closed : sentence no_universal_set.
Proof. reflexivity. Qed.

Theorem no_universal_set_meaning {D : Type} (member : D -> D -> Prop)
  (dne : forall P : Prop, ((P -> False) -> False) -> P) (env : nat -> D) :
  holds member env no_universal_set <-> ~ (exists u, forall x, member x u).
Proof.
  change ((holds member env universal_set -> False) <->
    ~ (exists u, forall x, member x u)).
  unfold universal_set.
  rewrite (holds_exists member dne); cbn [holds extend]; reflexivity.
Qed.

(** Only Separation and classical first-order inference are used. *)
Theorem no_universal_set_proved : ZFC_proves no_universal_set.
Proof.
  unfold ZFC_proves, no_universal_set, Neg.
  apply nd_imp_intro; [reflexivity|].
  eapply exists_absurd with (p := Forall (Member 0 1)); [reflexivity| |].
  - apply nd_assume; [reflexivity|left; reflexivity].
  - change (derives 1 [Forall (Member 0 1); universal_set] Bot).
    assert (R : derives 1 [Forall (Member 0 1); universal_set] (Exists russell_property)).
    { change (derives 1 [Forall (Member 0 1); universal_set]
        (instantiate_formula 0 (Exists russell_property))).
      apply nd_all_elim; [lia|].
      change (derives 1 [Forall (Member 0 1); universal_set] (separation 0 russell_predicate)).
      apply nd_axiom; apply ax_separation; reflexivity. }
    eapply exists_absurd with (p := russell_property); [reflexivity|exact R|].
    change (derives 2 [russell_property; Forall (Member 0 2); universal_set] Bot).
    set (g := [russell_property; Forall (Member 0 2); universal_set]).
    assert (U : derives 2 g (Member 0 1)).
    { change (derives 2 g (instantiate_formula 0 (Member 0 2))).
      apply nd_all_elim; [lia|]. apply nd_assume; [reflexivity|right; left; reflexivity]. }
    assert (D : derives 2 g (Iff (Member 0 0) (And (Member 0 1) (Neg (Member 0 0))))).
    { change (derives 2 g (instantiate_formula 0
        (Iff (Member 0 1) (And (Member 0 2) (Neg (Member 0 0)))))).
      apply nd_all_elim; [lia|]. apply nd_assume; [reflexivity|left; reflexivity]. }
    assert (Forward : derives 2 g (Implies (Member 0 0) (And (Member 0 1) (Neg (Member 0 0))))).
    { apply and_left in D; exact D. }
    assert (Backward : derives 2 g (Implies (And (Member 0 1) (Neg (Member 0 0))) (Member 0 0))).
    { apply and_right in D; exact D. }
    assert (N : derives 2 g (Neg (Member 0 0))).
    { apply nd_imp_intro; [reflexivity|].
      assert (Self : derives 2 (Member 0 0 :: g) (Member 0 0)).
      { apply nd_assume; [reflexivity|left; reflexivity]. }
      eapply nd_imp_elim; [|exact Self].
      apply and_right with (p := Member 0 1).
      eapply nd_imp_elim; [apply weaken_cons; exact Forward|exact Self]. }
    eapply nd_imp_elim; [exact N|].
    eapply nd_imp_elim; [exact Backward|].
    apply and_intro; assumption.
Qed.

Print Assumptions no_universal_set_proved.
