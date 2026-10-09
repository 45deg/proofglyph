From Tinyprover.Proofglyph Require Export Preservation.
From Tinyprover.Proofglyph Require Import Kernel Evaluation WellFormed.

Theorem normalization_preserves_type fuel sg ctx t u typ : wf_signature sg ->
  typing sg ctx t typ -> normal fuel t = Some u -> typing sg ctx u typ.
Proof.
  intros W T E; eapply subject_reduction_parallel_steps; [exact W| |exact T].
  apply evaluates_steps; eapply normal_evaluates; exact E.
Qed.
