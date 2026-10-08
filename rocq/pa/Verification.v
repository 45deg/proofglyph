From Tinyprover.Pa Require Import Checker.

(** Audit the public soundness/completeness guarantees and the CLI's signature
    invariant. Every command must report [Closed under the global context]. *)
Print Assumptions infer_sound.
Print Assumptions check_sound.
Print Assumptions check_program_sound.
Print Assumptions declarative_infer_complete.
Print Assumptions declarative_check_complete.
Print Assumptions declarative_program_complete.
Print Assumptions program_correct.
Print Assumptions accepted_program_wf.
Print Assumptions prelude_and_main_sound.
Print Assumptions prelude_and_main_complete.
Print Assumptions program_monotone.
