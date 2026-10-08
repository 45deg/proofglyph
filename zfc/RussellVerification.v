From Stdlib Require Import List.
From Rocq4pa Require Import Syntax Program Checker.
From Zfc Require Import Russell Encoding.
From ZfcDeep Require Import DeepVerification Translation.
From ZfcRussell Require Import Artifact.
Import ListNotations.

(** The same fixed prelude accepts a proof of the Russell example. *)
Theorem no_universal_set_accepted :
  exists t bound, forall fuel, bound <= fuel ->
    check fuel zfc_signature t (proof_type no_universal_set) = true.
Proof. apply ZFC_accepted; exact no_universal_set_proved. Qed.

Print Assumptions no_universal_set_accepted.

Definition russell_pa_term : term :=
  match ZfcRussell.Artifact.proofs with
  | [Prove _ t] => t
  | _ => tType
  end.

Example russell_fixed_prelude :
  ZfcRussell.Artifact.prelude = ZfcDeep.Artifact.prelude.
Proof. reflexivity. Qed.

Example russell_exact_statement : ZfcRussell.Artifact.proofs =
  [Prove (proof_type no_universal_set) russell_pa_term].
Proof. reflexivity. Qed.

Example russell_pa_accepted :
  check 128 zfc_signature russell_pa_term (proof_type no_universal_set) = true.
Proof. vm_compute; reflexivity. Qed.

Print Assumptions russell_pa_accepted.
