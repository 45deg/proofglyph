From Proofglyph.Language Require Export Confluence.
From Proofglyph.Language Require Import Kernel Evaluation.

Theorem equal_complete_from_convertibility a b u v :
  conv a b -> evaluates a u -> evaluates b v ->
  eventually (fun fuel => equal fuel a b = true).
Proof.
  intros C A B; pose proof (convertible_evaluations_agree _ _ _ _ C A B); subst.
  eapply equal_complete; eauto.
Qed.

