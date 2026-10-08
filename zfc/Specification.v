From Stdlib Require Import List.
From Rocq4pa Require Import Syntax Kernel WellFormed Checker.
From Zfc Require Import Formula Axioms Encoding Deduction.

(** The abstract target contract. Reflection.v supplies a concrete inhabitant
    for the full fixed proof_prelude.tp signature. *)
Record correct_presentation (sg : list term) (proof_type : formula -> term) : Prop := {
  presentation_wf : wf_signature sg;
  presentation_target_sorted : forall p, sentence p -> sorted_type sg nil (proof_type p);
  presentation_sound : forall p t fuel, sentence p ->
    check fuel sg t (proof_type p) = true -> ZFC_proves p;
  presentation_complete : forall p, ZFC_proves p ->
    exists t bound, forall fuel, bound <= fuel -> check fuel sg t (proof_type p) = true
}.

Theorem presentation_iff sg proof_type : correct_presentation sg proof_type ->
  forall p, sentence p ->
    (ZFC_proves p <-> exists t fuel, check fuel sg t (proof_type p) = true).
Proof.
  intros [W S Sound Complete] p Closed; split.
  - intros H; destruct (Complete p H) as [t [bound HT]].
    exists t, bound; apply HT; reflexivity.
  - intros [t [fuel H]]; eapply Sound; eauto.
Qed.

Theorem every_axiom_has_a_typed_code p : zfc_axiom p ->
  sentence p /\ typing syntax_signature nil (encode p) formula_type.
Proof. intros H; split; [apply all_axioms_closed; exact H|apply encode_typed]. Qed.

Example unbound_separation_not_an_axiom : ~ zfc_axiom (separation 0 (Member 0 1)).
Proof. intros H; apply all_axioms_closed in H; discriminate H. Qed.
Example unbound_replacement_not_an_axiom : ~ zfc_axiom (replacement 0 (Member 0 2)).
Proof. intros H; apply all_axioms_closed in H; discriminate H. Qed.

Print Assumptions presentation_iff.
Print Assumptions every_axiom_has_a_typed_code.

(** The remaining ZFC-specific obligation is entirely declarative.
    Inverse adequacy must cover arbitrary typed terms, not just translations. *)
Record declarative_presentation (sg : list term)
    (proof_type : formula -> term) : Prop := {
  declarative_wf : wf_signature sg;
  declarative_target_sorted : forall p, sentence p ->
    sorted_type sg nil (proof_type p);
  declarative_sound : forall p t, sentence p ->
    typing sg nil t (proof_type p) -> ZFC_proves p;
  declarative_complete : forall p, ZFC_proves p ->
    exists t, typing sg nil t (proof_type p)
}.

Theorem typed_translation_accepted sg proof_type :
  wf_signature sg ->
  (forall p, sentence p -> sorted_type sg nil (proof_type p)) ->
  (forall p, ZFC_proves p -> exists t, typing sg nil t (proof_type p)) ->
  forall p, ZFC_proves p ->
    exists t bound, forall fuel, bound <= fuel ->
      check fuel sg t (proof_type p) = true.
Proof.
  intros W S Translate p H.
  destruct (Translate p H) as [t T].
  destruct (declarative_check_complete sg t (proof_type p) W
    (S p (provable_sentence p H)) T) as [bound B].
  exists t, bound; exact B.
Qed.

Theorem declarative_to_correct sg proof_type :
  declarative_presentation sg proof_type -> correct_presentation sg proof_type.
Proof.
  intros [W S Sound Complete]; constructor.
  - exact W.
  - exact S.
  - intros p t fuel Closed Accepted.
    apply (Sound p t Closed).
    exact (proj1 (check_sound fuel sg t (proof_type p) W Accepted)).
  - exact (typed_translation_accepted sg proof_type W S Complete).
Qed.

Corollary declarative_presentation_iff sg proof_type :
  declarative_presentation sg proof_type ->
  forall p, sentence p ->
    (ZFC_proves p <-> exists t fuel, check fuel sg t (proof_type p) = true).
Proof.
  intros H; apply presentation_iff; apply declarative_to_correct; exact H.
Qed.

Print Assumptions typed_translation_accepted.
Print Assumptions declarative_to_correct.
Print Assumptions declarative_presentation_iff.
