From Stdlib Require Import List Permutation.
From Rocq4pa Require Import Syntax Kernel Checker.
From Calculi Require Import Calculi Encoding Verification Derivations
  CutElimination Restoration.
Import ListNotations.

Definition atom0 := Atom 0.
Definition compound := Imp (Conj atom0 (Neg (Atom 1))) (Disj atom0 Top).
Definition nk_identity_evidence a := rule_app 26 [
  encode_context []; encode a; encode a;
  rule_app 23 [encode_context [a]; encode a;
    rule_app 15 [encode a; encode_context []]]].
Definition beta_identity_evidence := tApp
  (tLam (NK_code [] (Imp atom0 atom0)) (tVar 0))
  (nk_identity_evidence atom0).

Example beta_identity_checked :
  check 128 fixed_signature beta_identity_evidence (NK_code [] (Imp atom0 atom0)) = true.
Proof. vm_compute; reflexivity. Qed.
Example beta_identity_restored : NK [] (Imp atom0 atom0).
Proof.
  apply LF_restores_NK with (t := beta_identity_evidence).
  exact (proj1 (check_sound _ _ _ _ prelude_well_formed beta_identity_checked)).
Qed.

Definition lk_cut_evidence a p := rule_app 55 [
  encode_context [a]; encode_context [a]; encode a;
  rule_app 42 [encode_context [a]; encode_context [a]; encode a; p];
  rule_app 41 [encode_context [a]; encode_context [a]; encode a; p]].
Definition nested_cut_evidence := lk_cut_evidence compound
  (lk_cut_evidence compound (rule_app 38 [encode compound])).
Example nested_cut_checked :
  check 128 fixed_signature nested_cut_evidence (LK_code [compound] [compound]) = true.
Proof. vm_compute; reflexivity. Qed.
Example nested_cut_restored : LK [compound] [compound].
Proof.
  apply LF_restores_LK with (t := nested_cut_evidence).
  exact (proj1 (check_sound _ _ _ _ prelude_well_formed nested_cut_checked)).
Qed.
Example nested_cut_eliminated : LK_cut_free [compound] [compound].
Proof. apply LK_cut_elimination; exact nested_cut_restored. Qed.
Example lf_nested_cut_eliminated : LK_cut_free [compound] [compound].
Proof.
  apply LF_restores_cut_free_LK with (t := nested_cut_evidence).
  exact (proj1 (check_sound _ _ _ _ prelude_well_formed nested_cut_checked)).
Qed.

Example excluded_middle_cut_free a : LK_cut_free [] [Disj a (Neg a)].
Proof.
  apply cf_disj_right.
  eapply cf_exchange_right; [apply perm_swap|].
  apply cf_neg_right; apply cf_identity.
Qed.
Example cut_free_imp_left a b : LK_cut_free [Imp a b; a] [b].
Proof.
  apply cf_imp_left.
  - eapply cf_exchange_right; [apply perm_swap|].
    apply cf_weak_right; apply cf_identity.
  - eapply cf_exchange_left; [apply perm_swap|].
    apply cf_weak_left; apply cf_identity.
Qed.

Example no_empty_LF_sequent t : ~ lf (LK_code [] []) t.
Proof.
  intros T; pose proof (LF_restores_LK _ _ _ T) as H.
  pose proof (LK_boolean_sound _ _ H (fun _ => false)) as S.
  assert (A : all_hold (boolean_interpretation (fun _ => false)) []).
  { intros a IN; inversion IN. }
  destruct (S A) as [a [IN _]]; inversion IN.
Qed.

Print Assumptions beta_identity_restored.
Print Assumptions lf_nested_cut_eliminated.
Print Assumptions no_empty_LF_sequent.
