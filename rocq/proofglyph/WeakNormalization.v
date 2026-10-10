From Stdlib Require Import List.
From Proofglyph.Language Require Export WeakHead.
From Proofglyph.Language Require Import Normalization TypedNormalization EvaluationSpec Confluence Preservation Checker WellFormed Regularity Generation Arity TypingSubstitution Substitution.

Lemma sn_context (f : term -> term) :
  (forall t u, reduces t u -> reduces (f t) (f u)) ->
  forall t, strongly_normalizing (f t) -> strongly_normalizing t.
Proof.
  intros F t H; remember (f t) as ft eqn:E; revert t E.
  induction H as [ft NEXT IH]; intros t E; subst ft.
  constructor; intros u R; apply (IH (f u)); [apply F; exact R|reflexivity].
Qed.

Lemma sn_pi_parts a b : strongly_normalizing (tPi a b) ->
  strongly_normalizing a /\ strongly_normalizing b.
Proof.
  intros H; split.
  - eapply (sn_context (fun z => tPi z b)); [intros; apply red_pi_domain; eassumption|exact H].
  - eapply (sn_context (tPi a)); [intros; apply red_pi_body; eassumption|exact H].
Qed.
Lemma sn_lam_parts a b : strongly_normalizing (tLam a b) ->
  strongly_normalizing a /\ strongly_normalizing b.
Proof.
  intros H; split.
  - eapply (sn_context (fun z => tLam z b)); [intros; apply red_lam_domain; eassumption|exact H].
  - eapply (sn_context (tLam a)); [intros; apply red_lam_body; eassumption|exact H].
Qed.
Lemma sn_app_parts a b : strongly_normalizing (tApp a b) ->
  strongly_normalizing a /\ strongly_normalizing b.
Proof.
  intros H; split.
  - eapply (sn_context (fun z => tApp z b)); [intros; apply red_app_function; eassumption|exact H].
  - eapply (sn_context (tApp a)); [intros; apply red_app_argument; eassumption|exact H].
Qed.

Lemma sn_steps t u : strongly_normalizing t -> steps t u -> strongly_normalizing u.
Proof.
  intros N S; apply parallel_steps_beta_steps in S.
  induction S; eauto using strongly_normalizing_step.
Qed.

Lemma weak_head_from_reducts t :
  (forall u, beta_plus t u -> exists v, weak_head u v) -> exists v, weak_head t v.
Proof.
  induction t as [| |n|n|a IHA b IHB|a IHA b IHB|f IHF x IHX]; intros IH;
    try (eexists; constructor; fail).
  destruct IHF as [f' F].
  { intros u R. destruct (IH (tApp u x)) as [v V].
    - eapply (beta_plus_congruence (fun z => tApp z x));
        [intros; apply red_app_function; eassumption|exact R].
    - inversion V; subst; eauto. }
  destruct f' as [| |n|n|a b|a b|g y];
    try (eexists; apply wh_app; [exact F|intros; discriminate]).
  destruct (IH (instantiate b x)) as [u U].
  - eapply beta_steps_plus; [|apply plus_one; apply red_beta].
    apply parallel_steps_beta_steps.
    eapply (steps_congruence (fun z => tApp z x));
      [intros; apply par_app; [assumption|apply parallel_refl]|apply whnf_steps; exact F].
  - exists u; eapply wh_beta; eauto.
Qed.

Theorem strongly_normalizing_weak_head t : strongly_normalizing t ->
  exists u, weak_head t u.
Proof.
  intros N; pose proof (strongly_normalizing_plus _ N) as A; clear N.
  induction A as [t NEXT IH]; apply weak_head_from_reducts; exact IH.
Qed.

Fixpoint head_normal t : Prop := match t with
| tApp f x => head_normal f /\ (forall a b, f <> tLam a b)
| _ => True end.

Lemma weak_head_normal t u : weak_head t u -> head_normal u.
Proof. intros H; induction H; cbn; auto. Qed.

(** A weak-head normal term keeps its outer constructor during full evaluation.
    In particular its function spine cannot turn into a lambda. *)
Lemma head_normal_evaluation t u : head_normal t -> evaluates t u ->
  match t, u with
  | tType, tType | tKind, tKind => True
  | tVar n, tVar m | tConst n, tConst m => n = m
  | tPi a b, tPi c d | tLam a b, tLam c d | tApp a b, tApp c d =>
      evaluates a c /\ evaluates b d
  | _, _ => False end.
Proof.
  revert u; induction t; intros u N E; inversion E; subst; cbn in *; auto.
  destruct N as [N NL].
  specialize (IHt1 _ N H1).
  destruct t1; cbn in IHt1; try contradiction.
  exfalso; eapply NL; reflexivity.
Qed.

Lemma weak_head_evaluates t u n : strongly_normalizing t ->
  weak_head t u -> evaluates t n -> evaluates u n.
Proof.
  intros SN W E.
  destruct (strongly_normalizing_evaluates _ (sn_steps _ _ SN (whnf_steps _ _ W))) as [v V].
  pose proof (convertible_evaluations_agree _ _ _ _ (whnf_sound _ _ W) E V); subst; exact V.
Qed.

Theorem weak_equal_complete_normal n : forall a b,
  strongly_normalizing a -> strongly_normalizing b ->
  evaluates a n -> evaluates b n -> weak_compare a b.
Proof.
  induction n as [| |i|i|c IHC d IHD|c IHC d IHD|c IHC d IHD];
    intros a b SA SB EA EB;
    destruct (strongly_normalizing_weak_head _ SA) as [u U];
    destruct (strongly_normalizing_weak_head _ SB) as [v V];
    pose proof (weak_head_evaluates _ _ _ SA U EA) as EU;
    pose proof (weak_head_evaluates _ _ _ SB V EB) as EV;
    pose proof (head_normal_evaluation _ _ (weak_head_normal _ _ U) EU) as HU;
    pose proof (head_normal_evaluation _ _ (weak_head_normal _ _ V) EV) as HV;
    pose proof (sn_steps _ _ SA (whnf_steps _ _ U)) as SU;
    pose proof (sn_steps _ _ SB (whnf_steps _ _ V)) as SV.
  all: eapply wc_heads; [exact U|exact V|].
  all:
    destruct u; cbn in HU; try contradiction;
    destruct v; cbn in HV; try contradiction.
  - apply wc_same.
  - apply wc_same.
  - subst; apply wc_same.
  - subst; apply wc_same.
  - destruct HU, HV; destruct (sn_pi_parts _ _ SU), (sn_pi_parts _ _ SV).
    apply wc_pi; [apply IHC|apply IHD]; assumption.
  - destruct HU, HV; destruct (sn_lam_parts _ _ SU), (sn_lam_parts _ _ SV).
    apply wc_lam; [apply IHC|apply IHD]; assumption.
  - destruct HU, HV; destruct (sn_app_parts _ _ SU), (sn_app_parts _ _ SV).
    apply wc_app; [apply IHC|apply IHD]; assumption.
Qed.

Theorem weak_equal_complete a b : strongly_normalizing a ->
  strongly_normalizing b -> conv a b -> weak_compare a b.
Proof.
  intros SA SB C.
  destruct (strongly_normalizing_evaluates _ SA) as [u U].
  destruct (strongly_normalizing_evaluates _ SB) as [v V].
  pose proof (convertible_evaluations_agree _ _ _ _ C U V); subst v.
  eapply weak_equal_complete_normal; eauto.
Qed.

Lemma proper_sn sg ctx a : wf_signature sg -> wf_context sg ctx ->
  proper_type sg ctx a -> strongly_normalizing a.
Proof.
  intros W CT [->|[s [T S]]].
  - constructor; intros u R; inversion R.
  - eapply typing_strong_normalization; eauto.
Qed.

Lemma proper_weak_sort sg ctx a s : wf_signature sg -> wf_context sg ctx ->
  proper_type sg ctx a -> conv a s -> is_sort s -> weak_sort a s.
Proof.
  intros W CT P C S.
  pose proof (proper_sn _ _ _ W CT P) as SN.
  destruct (strongly_normalizing_weak_head _ SN) as [u U].
  pose proof (proper_evaluates_sort _ _ _ _ W CT P C S) as E.
  pose proof (head_normal_evaluation _ _ (weak_head_normal _ _ U)
    (weak_head_evaluates _ _ _ SN U E)) as H.
  split; [|exact S]; destruct S as [-> | ->]; destruct u; cbn in H; try contradiction; exact U.
Qed.

Lemma proper_weak_pi sg ctx t a b : wf_signature sg -> wf_context sg ctx ->
  proper_type sg ctx t -> conv t (tPi a b) ->
  exists c d, weak_head t (tPi c d) /\ conv a c /\ conv b d /\
    strongly_normalizing c /\ strongly_normalizing d.
Proof.
  intros W CT P C; pose proof (proper_sn _ _ _ W CT P) as SN.
  destruct (strongly_normalizing_weak_head _ SN) as [u U].
  destruct (proper_evaluates _ _ _ W CT P) as [v V].
  destruct (evaluates_convertible_pi _ _ _ _ V C) as [c [d [E _]]]; subst v.
  pose proof (head_normal_evaluation _ _ (weak_head_normal _ _ U)
    (weak_head_evaluates _ _ _ SN U V)) as H.
  destruct u; cbn in H; try contradiction.
  assert (CP : conv (tPi a b) (tPi u1 u2)) by
    (eapply cv_trans; [apply cv_sym; exact C|apply whnf_sound; exact U]).
  destruct (conv_pi_injective _ _ _ _ CP) as [A B].
  destruct (sn_pi_parts _ _ (sn_steps _ _ SN (whnf_steps _ _ U))) as [SA SB].
  exists u1, u2; auto.
Qed.
Theorem declarative_weak_infer sg ctx t a : wf_signature sg -> wf_context sg ctx ->
  typing sg ctx t a -> exists inferred,
    weak_infer sg ctx t inferred /\ conv inferred a.
Proof.
  intros W; revert ctx a; induction t as [| |n|n|a IHA b IHB|a IHA b IHB|f IHF x IHX];
    intros ctx typ CT T; apply typing_generation in T; cbn [generates] in T.
  - exists tKind; split; [constructor|exact T].
  - contradiction.
  - destruct T as [a [LOOK C]]; eexists; split; [constructor; exact LOOK|exact C].
  - destruct T as [a [LOOK C]]; exists a; split; [constructor; exact LOOK|exact C].
  - destruct T as [s [A [B [S C]]]].
    destruct (IHA _ _ CT A) as [aty [DA AC]].
    assert (CB : wf_context sg (a :: ctx)) by (constructor; assumption).
    destruct (IHB _ _ CB B) as [bt [DB BC]].
    destruct (weak_infer_sound _ _ _ _ W CT DA) as [_ AP].
    destruct (weak_infer_sound _ _ _ _ W CB DB) as [_ BP].
    exists s; split; [|exact C]. eapply wi_pi; [exact DA| |exact DB|].
    + exact (proper_weak_sort _ _ _ _ W CT AP AC (or_introl eq_refl)).
    + exact (proper_weak_sort _ _ _ _ W CB BP BC S).
  - destruct T as [bt [s [A [B [PI [S C]]]]]].
    destruct (IHA _ _ CT A) as [aty [DA AC]].
    assert (CB : wf_context sg (a :: ctx)) by (constructor; assumption).
    destruct (IHB _ _ CB B) as [inferred [DB BC]].
    destruct (weak_infer_sound _ _ _ _ W CT DA) as [_ AP].
    exists (tPi a inferred); split.
    + eapply wi_lam; [exact DA| |exact DB|].
      * exact (proper_weak_sort _ _ _ _ W CT AP AC (or_introl eq_refl)).
      * intros K; subst inferred.
        apply typing_generation in PI; cbn [generates] in PI.
        destruct PI as [k [_ [BT [KS _]]]].
        eapply sorted_not_conv_kind; [exact W|exists k; split; eassumption|apply cv_sym; exact BC].
    + eapply cv_trans; [apply cv_pi; [constructor|exact BC]|exact C].
  - destruct T as [a [b [F [X C]]]].
    destruct (IHF _ _ CT F) as [ft [DF FC]].
    destruct (IHX _ _ CT X) as [xt [DX XC]].
    destruct (weak_infer_sound _ _ _ _ W CT DF) as [_ FP].
    destruct (weak_infer_sound _ _ _ _ W CT DX) as [_ XP].
    destruct (proper_weak_pi _ _ _ _ _ W CT FP FC) as [d [e [U [AD [BE [SD SE]]]]]].
    assert (XD : conv xt d) by (eapply cv_trans; eauto).
    exists (instantiate e x); split.
    + eapply wi_app; [exact DF|exact U|exact DX|].
      apply weak_equal_complete; [eapply proper_sn; eauto|exact SD|exact XD].
    + eapply cv_trans; [|exact C]. rewrite !instantiate_as_substitute.
      apply conv_substitute; apply cv_sym; exact BE.
Qed.

