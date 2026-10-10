From Stdlib Require Import List.
From Proofglyph.Language Require Import Syntax Kernel Program WellFormed WeakChecker.
From Proofglyph.Zfc Require Import Artifact.
Import ListNotations.

Definition prelude_signature := map declared_type prelude.
Definition final_signature := prelude_signature ++ map declared_type proofs.

Example prelude_accepted : check_program 128 true [] prelude = Some prelude_signature.
Proof. vm_compute; reflexivity. Qed.
Example proofs_accepted : check_program 128 false prelude_signature proofs = Some final_signature.
Proof. vm_compute; reflexivity. Qed.
Theorem prelude_well_formed : wf_signature prelude_signature.
Proof. eapply accepted_program_wf; [constructor|exact prelude_accepted]. Qed.
Theorem actual_proofs_have_derivations : valid_program prelude_signature proofs final_signature.
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
