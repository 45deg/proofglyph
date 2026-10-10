From Stdlib Require Import List Lia.
From Proofglyph.Zfc Require Import Formula Axioms Deduction Russell.
Import ListNotations.

Lemma exists_intro n g p x : x < n -> scoped (S n) p = true ->
  derives n g (instantiate_formula x p) -> derives n g (Exists p).
Proof.
  intros X P D; unfold Exists, Neg.
  apply nd_imp_intro; [cbn [scoped]; rewrite P; reflexivity|].
  eapply nd_imp_elim; [|apply weaken_cons; exact D].
  change (derives n (Forall (Implies p Bot) :: g)
    (instantiate_formula x (Implies p Bot))).
  apply nd_all_elim; [exact X|].
  apply nd_assume; [cbn [scoped]; rewrite P; reflexivity|left; reflexivity].
Qed.

(** Infinity explicitly contains an empty member. No empty-set axiom is used. *)
Theorem empty_set_derived n g : derives n g empty_set.
Proof.
  apply nd_classical; [reflexivity|].
  unfold infinity in *.
  eapply exists_absurd; [|apply nd_axiom; apply ax_infinity|]; [reflexivity|].
  cbn [lift_hypotheses map rename up].
  eapply exists_absurd with
    (p := And (Member 0 1) (Forall (Neg (Member 0 1)))); [reflexivity| |].
  - eapply and_left. apply nd_assume; [|left; reflexivity]; reflexivity.
  - cbn [lift_hypotheses map rename up].
    eapply nd_imp_elim with (p := empty_set).
    + apply nd_assume; [reflexivity|right; right; left; reflexivity].
    + unfold empty_set. apply exists_intro with (x := 0); [lia|reflexivity|].
      cbn [instantiate_formula rename up unbind].
      eapply and_right. apply nd_assume; [|left; reflexivity]; reflexivity.
Qed.

Corollary empty_set_proved : ZFC_proves empty_set.
Proof. apply empty_set_derived. Qed.

Example empty_set_not_primitive : ~ zfc_axiom empty_set.
Proof. intros H; inversion H; destruct n; discriminate. Qed.

Print Assumptions empty_set_proved.
