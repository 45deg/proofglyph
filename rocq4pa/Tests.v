From Stdlib Require Import List.
From Rocq4pa Require Import Syntax Kernel Program WellFormed Completeness Counterexamples.
From Rocq4pa Require Import Substitution Confluence Generation.
From Rocq4pa Require Import TypingSubstitution Preservation Regularity.
Import ListNotations.

Definition identity :=
  [Assume tType;
   Prove (tPi (tConst 0) (tConst 0)) (tLam (tConst 0) (tVar 0))].

Example identity_accepted :
  check_program 64 true [] identity = Some [tType; tPi (tConst 0) (tConst 0)].
Proof. vm_compute. reflexivity. Qed.

Example identity_has_derivation :
  valid_program [] identity [tType; tPi (tConst 0) (tConst 0)].
Proof. eapply check_program_sound; exact identity_accepted. Qed.

Example kind_rejected : check_program 64 true [] [Assume tKind] = None.
Proof. vm_compute. reflexivity. Qed.

Example polymorphism_rejected : infer 64 [] [] (tPi tType (tVar 0)) = None.
Proof. vm_compute. reflexivity. Qed.

Example fuel_exhausted : infer 0 [] [] tType = None.
Proof. reflexivity. Qed.

Example disabled_axioms : check_program 64 false [] identity = None.
Proof. vm_compute. reflexivity. Qed.

Example forward_reference : check_program 64 true [] [Assume (tConst 0)] = None.
Proof. vm_compute. reflexivity. Qed.

Example wrong_proof : check 64 [tType; tType; tConst 0] (tConst 2) (tConst 1) = false.
Proof. vm_compute. reflexivity. Qed.

Example beta_conversion :
  check 64 [tType; tConst 0; tPi (tConst 0) tType]
    (tLam (tConst 0) (tVar 0))
    (tPi (tConst 0) (tApp (tLam (tConst 0) (tConst 0)) (tConst 1))) = true.
Proof. vm_compute. reflexivity. Qed.

Example dependent_identity :
  check_program 128 true []
    [Assume tType; Assume (tPi (tConst 0) tType);
     Prove (tPi (tConst 0)
               (tPi (tApp (tConst 1) (tVar 0)) (tApp (tConst 1) (tVar 1))))
           (tLam (tConst 0) (tLam (tApp (tConst 1) (tVar 0)) (tVar 0)))]
  = Some [tType; tPi (tConst 0) tType;
          tPi (tConst 0) (tPi (tApp (tConst 1) (tVar 0)) (tApp (tConst 1) (tVar 1)))].
Proof. vm_compute. reflexivity. Qed.

Example substitution_under_binder :
  instantiate (tLam (tConst 0) (tApp (tVar 1) (tVar 0))) (tVar 0)
  = tLam (tConst 0) (tApp (tVar 1) (tVar 0)).
Proof. reflexivity. Qed.

Print Assumptions normal_sound.
Print Assumptions equal_sound.
Print Assumptions infer_sound.
Print Assumptions check_sound.
Print Assumptions check_program_sound.
Print Assumptions no_axioms.

Example identity_all_larger_fuels fuel : 64 <= fuel ->
  check_program fuel true [] identity = Some [tType; tPi (tConst 0) (tConst 0)].
Proof. intros H; eapply program_monotone; [exact H|exact identity_accepted]. Qed.

Lemma identity_type_synthesis :
  synthesizes [tType] [] (tPi (tConst 0) (tConst 0)) tType.
Proof.
  eapply sy_pi with (aty := tType) (bt := tType).
  - apply sy_const; reflexivity.
  - constructor.
  - apply sy_const; reflexivity.
  - constructor.
  - left; reflexivity.
Qed.

Example identity_finite_derivation :
  program_derivation true [] identity [tType; tPi (tConst 0) (tConst 0)].
Proof.
  unfold identity. econstructor.
  - eapply dd_assume with (aty := tKind) (s := tKind).
    + reflexivity.
    + constructor.
    + constructor.
    + right; reflexivity.
  - econstructor; [|constructor]. apply dd_prove.
    eapply checks_intro with (aty := tType) (s := tType)
      (actual := tPi (tConst 0) (tConst 0)) (u := tPi (tConst 0) (tConst 0)).
    + exact identity_type_synthesis.
    + constructor.
    + left; reflexivity.
    + eapply sy_lam with (aty := tType) (bt := tConst 0) (pt := tType) (s := tType).
      * apply sy_const; reflexivity.
      * constructor.
      * change (synthesizes [tType] [tConst 0] (tVar 0) (shift 1 0 (tConst 0))).
        apply sy_var; reflexivity.
      * exact identity_type_synthesis.
      * constructor.
      * left; reflexivity.
    + constructor; constructor.
    + constructor; constructor.
Qed.

Example identity_has_sufficient_fuel :
  exists bound, forall fuel, bound <= fuel ->
    check_program fuel true [] identity = Some [tType; tPi (tConst 0) (tConst 0)].
Proof. apply program_complete; exact identity_finite_derivation. Qed.

Print Assumptions normal_monotone.
Print Assumptions infer_monotone.
Print Assumptions program_monotone.
Print Assumptions normal_complete.
Print Assumptions normalization_iff.
Print Assumptions infer_complete.
Print Assumptions check_complete.
Print Assumptions program_complete.
Print Assumptions identity_has_sufficient_fuel.
Print Assumptions unrestricted_program_completeness_is_false.

Example ordinary_axioms_still_allowed :
  check_program 64 true [] [Assume tType; Assume (tConst 0)] = Some [tType; tConst 0].
Proof. vm_compute; reflexivity. Qed.

Example ordinary_axioms_wf : wf_signature [tType; tConst 0].
Proof. eapply accepted_prelude_wf; exact ordinary_axioms_still_allowed. Qed.

Example identity_wf : wf_signature [tType; tPi (tConst 0) (tConst 0)].
Proof. eapply accepted_prelude_wf; exact identity_accepted. Qed.

Print Assumptions accepted_prelude_wf.
Print Assumptions valid_program_preserves_wf.
Print Assumptions bad_expansion_not_sorted.
Print Assumptions bad_signature_not_wf.
Print Assumptions bad_signature_not_from_accepted_prelude.
Print Assumptions ordinary_axioms_wf.

Example beta_equal_eventually :
  eventually (fun fuel => equal fuel (tApp (tLam tType (tVar 0)) (tConst 0)) (tConst 0) = true).
Proof.
  eapply equal_complete_from_convertibility with (u := tConst 0) (v := tConst 0).
  - change (conv (tApp (tLam tType (tVar 0)) (tConst 0)) (instantiate (tVar 0) (tConst 0))).
    apply cv_beta.
  - eapply ev_beta with (a := tType) (b := tVar 0) (x' := tConst 0);
      cbn [instantiate subst shift]; repeat constructor.
  - constructor.
Qed.

Example sort_separation : ~ conv tType tKind.
Proof.
  intros H; pose proof (normal_forms_unique _ _ H nf_type nf_kind); discriminate.
Qed.

Print Assumptions instantiate_as_substitute.
Print Assumptions substitute_beta.
Print Assumptions conv_substitute.
Print Assumptions parallel_diamond.
Print Assumptions steps_confluent.
Print Assumptions conv_joins.
Print Assumptions normal_forms_unique.
Print Assumptions conv_pi_injective.
Print Assumptions equal_complete_from_convertibility.
Print Assumptions typing_generation.
Print Assumptions typing_unique.

Example identity_application_typed :
  typing [tType; tConst 0] [] (tApp (tLam (tConst 0) (tVar 0)) (tConst 1)) (tConst 0).
Proof.
  exact (proj1 (check_sound 64 [tType; tConst 0]
    (tApp (tLam (tConst 0) (tVar 0)) (tConst 1)) (tConst 0) eq_refl)).
Qed.

Example identity_application_reduction_preserves_type :
  typing [tType; tConst 0] [] (tConst 1) (tConst 0).
Proof.
  eapply subject_reduction; [exact ordinary_axioms_wf| |exact identity_application_typed].
  change (reduces (tApp (tLam (tConst 0) (tVar 0)) (tConst 1)) (instantiate (tVar 0) (tConst 1))).
  apply red_beta.
Qed.

Example identity_application_normalization_preserves_type :
  typing [tType; tConst 0] [] (tConst 1) (tConst 0).
Proof.
  eapply normalization_preserves_type with (fuel := 64);
    [exact ordinary_axioms_wf|exact identity_application_typed|reflexivity].
Qed.

Example raw_expansion_has_regular_representative :
  exists proper, conv bad_expansion proper /\ (proper = tKind \/ sorted_type [] [] proper).
Proof.
  eapply typing_regular_representative with (t := tType);
    [constructor|constructor|exact (proj1 raw_typing_does_not_check)].
Qed.

Print Assumptions typing_subject_closed.
Print Assumptions wf_signature_closed.
Print Assumptions typing_rename.
Print Assumptions typing_weaken.
Print Assumptions typing_substitute.
Print Assumptions typing_instantiate.
Print Assumptions typing_context_conversion.
Print Assumptions subject_reduction.
Print Assumptions normalization_preserves_type.
Print Assumptions wf_signature_lookup.
Print Assumptions wf_context_lookup.
Print Assumptions typing_regular_representative.
