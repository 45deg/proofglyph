From Stdlib Require Import List.
From Rocq4pa Require Import Syntax Kernel Program WellFormed Checker.
From Calculi Require Import Artifact Encoding.
Import ListNotations.

Definition fixed_signature := map declared_type prelude.
Definition final_signature := fixed_signature ++ map declared_type proofs.
Example prelude_accepted : check_program 128 true [] prelude = Some fixed_signature.
Proof. vm_compute; reflexivity. Qed.
Example proofs_accepted : check_program 128 false fixed_signature proofs = Some final_signature.
Proof. vm_compute; reflexivity. Qed.
Theorem prelude_well_formed : wf_signature fixed_signature.
Proof. eapply accepted_program_wf; [constructor|exact prelude_accepted]. Qed.
Theorem actual_proofs_have_derivations : valid_program fixed_signature proofs final_signature.
Proof. eapply check_program_sound; [exact prelude_well_formed|exact proofs_accepted]. Qed.
Theorem actual_proofs_add_no_axioms :
  Forall (fun d => match d with Prove _ _ => True | Assume _ => False end) proofs.
Proof.
  pose proof (check_program_no_axioms _ _ _ _ proofs_accepted) as H.
  eapply Forall_impl; [|exact H].
  intros [a|a t]; simpl; [discriminate|auto].
Qed.

Print Assumptions prelude_well_formed.
Print Assumptions actual_proofs_have_derivations.
Print Assumptions actual_proofs_add_no_axioms.

(** Check the intended six theorem statements independently of the exporter. *)
Definition nk_type g a := tApp (tApp (tConst 22) g) a.
Definition lk_type g d := tApp (tApp (tConst 37) g) d.
Definition singleton a := code_binary 13 a (tConst 12).
Definition em a := code_binary 9 a (tApp (tConst 10) a).
Example exported_goals_match : map declared_type proofs = [
  tPi (tConst 3) (nk_type (tConst 12) (code_binary 7 (tVar 0) (tVar 0)));
  tPi (tConst 3) (tPi (tConst 3) (nk_type (tConst 12)
    (code_binary 7 (code_binary 8 (tVar 1) (tVar 0)) (code_binary 8 (tVar 0) (tVar 1)))));
  tPi (tConst 3) (nk_type (tConst 12) (em (tVar 0)));
  tPi (tConst 3) (lk_type (tConst 12) (singleton (code_binary 7 (tVar 0) (tVar 0))));
  tPi (tConst 3) (lk_type (tConst 12) (singleton (em (tVar 0))));
  tPi (tConst 3) (lk_type (singleton (tVar 0)) (singleton (tVar 0)))].
Proof. vm_compute; reflexivity. Qed.
Print Assumptions exported_goals_match.
