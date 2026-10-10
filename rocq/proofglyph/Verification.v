From Proofglyph.Language Require Import Checker.

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

From Proofglyph.Language Require Import Codec.
Print Assumptions lex_proofglyph_correct.
Print Assumptions decode_proofglyph_correct.
Print Assumptions proofglyph_roundtrip.

From Proofglyph.Language Require Import WeakHead.
Print Assumptions whnf_steps.
Print Assumptions whnf_sound.
Print Assumptions whnf_preserves_type.
Print Assumptions weak_equal_sound.
Print Assumptions weak_as_sort_sound.
Print Assumptions weak_infer_sound.
Print Assumptions weak_check_sound.
Print Assumptions weak_check_declaration_sound.
Print Assumptions weak_check_program_sound.
Print Assumptions weak_accepted_program_wf.
Print Assumptions cached_infer_sound.
Print Assumptions inference_cache_insert_valid.
Print Assumptions inference_cache_empty_valid.

From Proofglyph.Language Require Import WeakNormalization WeakEvaluation WeakChecker.
Print Assumptions strongly_normalizing_weak_head.
Print Assumptions weak_equal_complete.
Print Assumptions declarative_weak_infer.
Print Assumptions whnf_relation.
Print Assumptions whnf_complete.
Print Assumptions w_equal_relation.
Print Assumptions w_equal_complete.
Print Assumptions infer_relation.
Print Assumptions infer_sound.
Print Assumptions declarative_infer_complete.
Print Assumptions check_sound.
Print Assumptions declarative_check_complete.
Print Assumptions check_program_sound.
Print Assumptions declarative_program_complete.
Print Assumptions program_correct.
Print Assumptions accepted_program_wf.
Print Assumptions prelude_and_main_sound.
Print Assumptions prelude_and_main_complete.
Print Assumptions program_monotone.
