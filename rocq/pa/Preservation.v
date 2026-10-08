From Stdlib Require Import List.
From Tinyprover.Pa Require Import Syntax Substitution WellFormed TypingSubstitution Confluence Generation EvaluationSpec.
Import ListNotations.

(** One beta step, including all annotations and binder bodies. *)
Inductive reduces : term -> term -> Prop :=
| red_beta : forall a b x, reduces (tApp (tLam a b) x) (instantiate b x)
| red_pi_domain : forall a a' b, reduces a a' -> reduces (tPi a b) (tPi a' b)
| red_pi_body : forall a b b', reduces b b' -> reduces (tPi a b) (tPi a b')
| red_lam_domain : forall a a' b, reduces a a' -> reduces (tLam a b) (tLam a' b)
| red_lam_body : forall a b b', reduces b b' -> reduces (tLam a b) (tLam a b')
| red_app_function : forall f f' x, reduces f f' -> reduces (tApp f x) (tApp f' x)
| red_app_argument : forall f x x', reduces x x' -> reduces (tApp f x) (tApp f x').

Lemma reduces_conv t u : reduces t u -> conv t u.
Proof. intros H; induction H; eauto using conv. Qed.

Lemma context_conv_head a b ctx : conv a b -> context_conv (a :: ctx) (b :: ctx).
Proof. intros C; constructor; [exact C|apply context_conv_refl]. Qed.

Lemma typing_pi_domain_conversion sg ctx a a' b s : wf_signature sg ->
  typing sg ctx (tPi a b) s -> typing sg ctx a' tType -> conv a a' ->
  typing sg ctx (tPi a' b) s.
Proof.
  intros W T A C; apply typing_generation in T; cbn [generates] in T.
  destruct T as [k [TA [TB [K EQ]]]].
  eapply ty_conv; [eapply ty_pi; [exact A| |exact K]|exact EQ].
  eapply typing_context_conversion; [exact W|apply context_conv_head; exact C|exact TB].
Qed.

Theorem typing_beta sg ctx a b x typ : wf_signature sg ->
  typing sg ctx (tApp (tLam a b) x) typ -> typing sg ctx (instantiate b x) typ.
Proof.
  intros W T; apply typing_generation in T; cbn [generates] in T.
  destruct T as [dom [cod [F [X RESULT]]]].
  apply typing_generation in F; cbn [generates] in F.
  destruct F as [bt [s [A [B [PI [SORT EQ]]]]]].
  apply conv_pi_injective in EQ as [DOMAIN BODY].
  assert (ARG : typing sg ctx x a) by (eapply ty_conv; [exact X|apply cv_sym; exact DOMAIN]).
  eapply ty_conv; [eapply typing_instantiate; [exact W|exact B|exact ARG]|].
  eapply cv_trans; [|exact RESULT].
  rewrite !instantiate_as_substitute; apply conv_substitute; exact BODY.
Qed.

Theorem subject_reduction sg ctx t u typ : wf_signature sg ->
  reduces t u -> typing sg ctx t typ -> typing sg ctx u typ.
Proof.
  intros W R; revert ctx typ; induction R; intros ctx typ T.
  - eapply typing_beta; eauto.
  - apply typing_generation in T; cbn [generates] in T.
    destruct T as [s [A [B [S C]]]].
    eapply ty_conv; [eapply ty_pi; [apply IHR; exact A| |exact S]|exact C].
    eapply typing_context_conversion; [exact W|apply context_conv_head; apply reduces_conv; exact R|exact B].
  - apply typing_generation in T; cbn [generates] in T.
    destruct T as [s [A [B [S C]]]].
    eapply ty_conv; [eapply ty_pi; [exact A|apply IHR; exact B|exact S]|exact C].
  - apply typing_generation in T; cbn [generates] in T.
    destruct T as [bt [s [A [B [PI [S C]]]]]].
    eapply ty_conv.
    + eapply ty_lam with (bt := bt) (s := s).
      * apply IHR; exact A.
      * eapply typing_context_conversion; [exact W|apply context_conv_head; apply reduces_conv; exact R|exact B].
      * eapply typing_pi_domain_conversion; [exact W|exact PI|apply IHR; exact A|apply reduces_conv; exact R].
      * exact S.
    + eapply cv_trans; [apply cv_pi; [apply cv_sym; apply reduces_conv; exact R|apply cv_refl]|exact C].
  - apply typing_generation in T; cbn [generates] in T.
    destruct T as [bt [s [A [B [PI [S C]]]]]].
    eapply ty_conv; [eapply ty_lam; [exact A|apply IHR; exact B|exact PI|exact S]|exact C].
  - apply typing_generation in T; cbn [generates] in T.
    destruct T as [a [b [F [X C]]]].
    eapply ty_conv; [eapply ty_app; [apply IHR; exact F|exact X]|exact C].
  - apply typing_generation in T; cbn [generates] in T.
    destruct T as [a [b [F [X C]]]].
    eapply ty_conv; [eapply ty_app; [exact F|apply IHR; exact X]|].
    eapply cv_trans; [apply conv_instantiate_argument; apply cv_sym; apply reduces_conv; exact R|exact C].
Qed.

Inductive beta_steps : term -> term -> Prop :=
| beta_refl : forall t, beta_steps t t
| beta_cons : forall t u v, reduces t u -> beta_steps u v -> beta_steps t v.

Lemma beta_trans t u v : beta_steps t u -> beta_steps u v -> beta_steps t v.
Proof. intros H; induction H; eauto using beta_steps. Qed.

Lemma beta_congruence f :
  (forall t u, reduces t u -> reduces (f t) (f u)) ->
  forall t u, beta_steps t u -> beta_steps (f t) (f u).
Proof. intros F t u H; induction H; eauto using beta_steps. Qed.

Lemma beta_binary f :
  (forall a a' b, reduces a a' -> reduces (f a b) (f a' b)) ->
  (forall a b b', reduces b b' -> reduces (f a b) (f a b')) ->
  forall a a' b b', beta_steps a a' -> beta_steps b b' -> beta_steps (f a b) (f a' b').
Proof.
  intros L R a a' b b' A B; eapply beta_trans with (u := f a' b).
  - eapply (beta_congruence (fun x => f x b)); eauto.
  - eapply (beta_congruence (f a')); eauto.
Qed.

Lemma parallel_beta_steps t u : parallel t u -> beta_steps t u.
Proof.
  intros H; induction H; eauto using beta_refl.
  - eapply beta_binary; eauto using red_pi_domain, red_pi_body.
  - eapply beta_binary; eauto using red_lam_domain, red_lam_body.
  - eapply beta_binary; eauto using red_app_function, red_app_argument.
  - eapply beta_trans with (u := tApp (tLam a b') x').
    + eapply beta_binary; eauto using red_app_function, red_app_argument.
      eapply (beta_congruence (tLam a)); eauto using red_lam_body.
    + econstructor; [apply red_beta|constructor].
Qed.

Theorem subject_reduction_steps sg ctx t u typ : wf_signature sg ->
  beta_steps t u -> typing sg ctx t typ -> typing sg ctx u typ.
Proof.
  intros W H; induction H; intros T; [exact T|].
  apply IHbeta_steps; eapply subject_reduction; eauto.
Qed.

Theorem subject_reduction_parallel_steps sg ctx t u typ : wf_signature sg ->
  steps t u -> typing sg ctx t typ -> typing sg ctx u typ.
Proof.
  intros W H; induction H; intros T; [exact T|].
  apply IHsteps; eapply subject_reduction_steps; [exact W|apply parallel_beta_steps; exact H|exact T].
Qed.

Lemma evaluates_steps t u : evaluates t u -> steps t u.
Proof.
  intros H; induction H; eauto using steps_refl.
  - eapply steps_trans with (b := tPi a' b).
    + eapply (steps_congruence (fun x => tPi x b)); eauto using par_pi, parallel_refl.
    + eapply (steps_congruence (tPi a')); eauto using par_pi, parallel_refl.
  - eapply steps_trans with (b := tLam a' b).
    + eapply (steps_congruence (fun x => tLam x b)); eauto using par_lam, parallel_refl.
    + eapply (steps_congruence (tLam a')); eauto using par_lam, parallel_refl.
  - eapply steps_trans with (b := tApp f' x).
    + eapply (steps_congruence (fun f => tApp f x)); eauto using par_app, parallel_refl.
    + eapply (steps_congruence (tApp f')); eauto using par_app, parallel_refl.
  - eapply steps_trans with (b := tApp (tLam a b) x').
    + eapply steps_trans with (b := tApp (tLam a b) x).
      * eapply (steps_congruence (fun f => tApp f x)); eauto using par_app, parallel_refl.
      * eapply (steps_congruence (tApp (tLam a b))); eauto using par_app, parallel_refl.
    + econstructor; [apply par_beta; apply parallel_refl|exact IHevaluates3].
Qed.
