From Stdlib Require Import List.
From Rocq4pa Require Import Syntax Kernel Program WellFormed Completeness.
Import ListNotations.

(** Raw conversion permits an untypable beta expansion of a type. *)
Definition bad_expansion := tApp (tLam tKind tKind) tKind.

Example raw_typing_does_not_check :
  typing [] [] tType bad_expansion /\
  forall fuel, check fuel [] tType bad_expansion = false.
Proof.
  split.
  - eapply ty_conv; [constructor|]. apply cv_sym.
    change (conv bad_expansion (instantiate tKind tKind)). apply cv_beta.
  - intros [|[|[|fuel]]]; reflexivity.
Qed.

(** Even requiring a sorted target does not suffice for an arbitrary signature.
    The eager normalizer tries to evaluate omega in an erased argument. *)
Definition delta := tLam tType (tApp (tVar 0) (tVar 0)).
Definition omega := tApp delta delta.

Lemma delta_normal fuel : normal (S (S (S fuel))) delta = Some delta.
Proof. reflexivity. Qed.

Lemma omega_never_normalizes fuel : normal fuel omega = None.
Proof.
  induction fuel as [|fuel IH]; [reflexivity|].
  destruct fuel as [|[|[|fuel]]]; try reflexivity.
  change (normal (S (S (S fuel))) omega = None); exact IH.
Qed.

Definition erased_omega_type := tApp (tLam tKind (tPi tType tType)) omega.
Definition bad_signature := [erased_omega_type; tType].
Definition bad_application := tApp (tConst 0) (tConst 1).

Lemma erased_omega_never_normalizes fuel : normal fuel erased_omega_type = None.
Proof.
  destruct fuel as [|fuel]; [reflexivity|].
  cbn [normal erased_omega_type]; unfold bind.
  destruct (normal fuel (tLam tKind (tPi tType tType)));
    [rewrite omega_never_normalizes|]; reflexivity.
Qed.

Lemma bad_application_never_infers fuel : infer fuel bad_signature [] bad_application = None.
Proof.
  destruct fuel as [|[|fuel]]; try reflexivity.
  cbn [infer bad_signature bad_application nth_error bind].
  rewrite erased_omega_never_normalizes; reflexivity.
Qed.

Example sorted_declaration_counterexample :
  valid_declaration bad_signature (Prove tType bad_application) /\
  forall fuel, check_declaration fuel true bad_signature (Prove tType bad_application) = false.
Proof.
  split.
  - split.
    + exists tKind; split; [constructor|right; reflexivity].
    + unfold bad_application. eapply ty_app with (a := tType) (b := tType).
      * eapply ty_conv.
        -- apply ty_const; reflexivity.
        -- change (conv erased_omega_type (instantiate (tPi tType tType) omega)).
           apply cv_beta.
      * apply ty_const; reflexivity.
  - intros fuel; cbn [check_declaration]; unfold check.
    rewrite bad_application_never_infers.
    destruct (infer fuel bad_signature [] tType); reflexivity.
Qed.

Example unrestricted_program_completeness_is_false :
  valid_program bad_signature [Prove tType bad_application] (bad_signature ++ [tType]) /\
  forall fuel, check_program fuel true bad_signature [Prove tType bad_application] = None.
Proof.
  destruct sorted_declaration_counterexample as [V R]. split.
  - constructor; [exact V|constructor].
  - intros fuel; cbn [check_program]; rewrite R; reflexivity.
Qed.

(** These counterexamples are outside the corrected completeness premises.
    They cannot be introduced by an ordinary sorted axiom declaration. *)
Theorem bad_expansion_not_sorted : ~ sorted_type [] [] bad_expansion.
Proof.
  intros [s [T _]]; unfold bad_expansion in T.
  eapply kind_domain_application_has_no_type; eauto.
Qed.

Theorem bad_signature_not_wf : ~ wf_signature bad_signature.
Proof.
  intros W.
  change (wf_signature ([erased_omega_type] ++ [tType])) in W.
  apply wf_signature_last in W as [W _].
  change (wf_signature ([] ++ [erased_omega_type])) in W.
  apply wf_signature_last in W as [_ [s [T _]]].
  unfold erased_omega_type in T.
  eapply kind_domain_application_has_no_type; eauto.
Qed.

Corollary bad_signature_not_from_valid_program ds : ~ valid_program [] ds bad_signature.
Proof.
  intros V; apply bad_signature_not_wf.
  eapply valid_program_preserves_wf; [constructor|exact V].
Qed.

Corollary bad_signature_not_from_accepted_prelude fuel ds :
  check_program fuel true [] ds <> Some bad_signature.
Proof.
  intros H; apply bad_signature_not_wf; eapply accepted_prelude_wf; exact H.
Qed.
