From Stdlib Require Import List.
From Proofglyph.Language Require Export WeakHeadSpec.
From Proofglyph.Language Require Import WellFormed Substitution
  TypingSubstitution Confluence Generation Preservation Regularity Arity.
Import ListNotations.

Theorem whnf_steps t u : weak_head t u -> steps t u.
Proof.
  intros H; induction H; try (constructor; fail).
  - eapply (steps_congruence (fun f => tApp f x));
      [intros; apply par_app; [assumption|apply parallel_refl]|exact IHweak_head].
  - eapply steps_trans.
    + eapply (steps_congruence (fun f => tApp f x));
        [intros; apply par_app; [assumption|apply parallel_refl]|exact IHweak_head1].
    + eapply steps_cons; [apply par_beta; apply parallel_refl|exact IHweak_head2].
Qed.



Theorem whnf_sound t u : weak_head t u -> conv t u.
Proof. intros H; apply steps_conv; apply whnf_steps; exact H. Qed.

Theorem whnf_preserves_type sg ctx t u typ : wf_signature sg ->
  typing sg ctx t typ -> weak_head t u -> typing sg ctx u typ.
Proof.
  intros W T H; eapply subject_reduction_parallel_steps;
    [exact W|apply whnf_steps; exact H|exact T].
Qed.

Lemma weak_comparison_sound :
  (forall a b, weak_compare a b -> conv a b) /\
  (forall a b, weak_components a b -> conv a b).
Proof.
  apply weak_comparison_ind.
  - intros; constructor.
  - intros a b u v A B C IH.
    eapply cv_trans; [apply whnf_sound; exact A|].
    eapply cv_trans; [exact IH|apply cv_sym; apply whnf_sound; exact B].
  - intros; constructor.
  - intros; apply cv_pi; assumption.
  - intros; apply cv_lam; assumption.
  - intros; apply cv_app; assumption.
Qed.

Theorem weak_equal_sound a b : weak_compare a b -> conv a b.
Proof. apply weak_comparison_sound. Qed.

Lemma weak_as_sort_sound a s : weak_sort a s -> conv a s /\ is_sort s.
Proof. intros [H S]; split; [apply whnf_sound; exact H|exact S]. Qed.

Theorem weak_infer_sound sg ctx t a : wf_signature sg -> wf_context sg ctx ->
  weak_infer sg ctx t a -> typing sg ctx t a /\ proper_type sg ctx a.
Proof.
  intros W CT H; revert CT.
  induction H as [ctx|ctx n a LOOK|ctx n a LOOK|
    ctx a b aty bt s A IHA AS B IHB BS|
    ctx a b aty bt A IHA AS B IHB NK|
    ctx f x ft a b xt F IHF HEAD X IHX EQ]; intros CT.
  - split; [constructor|left; reflexivity].
  - split; [constructor; exact LOOK|right].
    exists tType; split; [eapply wf_context_lookup; eauto|left; reflexivity].
  - split; [constructor; exact LOOK|right].
    apply sorted_type_any_context; [exact W|eapply wf_signature_lookup; eauto].
  - destruct (IHA CT) as [AT AP].
    destruct (weak_as_sort_sound _ _ AS) as [AC _].
    assert (DOMAIN : typing sg ctx a tType) by (eapply ty_conv; eauto).
    destruct (IHB (wf_context_cons _ _ _ CT DOMAIN)) as [BT BP].
    destruct (weak_as_sort_sound _ _ BS) as [BC S].
    split.
    + eapply ty_pi; [exact DOMAIN|eapply ty_conv; eauto|exact S].
    + apply sort_proper; exact S.
  - destruct (IHA CT) as [AT AP].
    destruct (weak_as_sort_sound _ _ AS) as [AC _].
    assert (DOMAIN : typing sg ctx a tType) by (eapply ty_conv; eauto).
    destruct (IHB (wf_context_cons _ _ _ CT DOMAIN)) as [BT [K|[s [SORT IS]]]].
    + contradiction.
    + assert (PI : typing sg ctx (tPi a bt) s) by (eapply ty_pi; eauto).
      split; [eapply ty_lam; eauto|right; exists s; auto].
  - destruct (IHF CT) as [FT FP].
    destruct (IHX CT) as [XT XP].
    assert (ARG : typing sg ctx x a) by
      (eapply ty_conv; [exact XT|apply weak_equal_sound; exact EQ]).
    split.
    + eapply ty_app; [eapply ty_conv; [exact FT|apply whnf_sound; exact HEAD]|exact ARG].
    + right; destruct FP as [K|[s [T S]]].
      * subst ft; exfalso; eapply conv_pi_not_kind; apply cv_sym; apply whnf_sound; exact HEAD.
      * pose proof (whnf_preserves_type _ _ _ _ _ W T HEAD) as PI.
        apply typing_generation in PI; cbn [generates] in PI.
        destruct PI as [k [DA [DB [KS C]]]]; exists k; split; [|exact KS].
        rewrite <- (instantiate_sort k x KS); eapply typing_instantiate; eauto.
Qed.

Theorem weak_check_sound sg t a : wf_signature sg ->
  weak_check sg t a -> typing sg [] t a /\ sorted_type sg [] a.
Proof.
  intros W [aty [actual [s [A [S [T EQ]]]]]].
  destruct (weak_as_sort_sound _ _ S) as [C IS].
  destruct (weak_infer_sound _ _ _ _ W (wf_context_nil _) A) as [AT _].
  destruct (weak_infer_sound _ _ _ _ W (wf_context_nil _) T) as [TT _].
  split.
  - eapply ty_conv; [exact TT|apply weak_equal_sound; exact EQ].
  - exists s; split; [eapply ty_conv; eauto|exact IS].
Qed.

Theorem weak_check_declaration_sound allow sg d : wf_signature sg ->
  weak_check_declaration allow sg d -> valid_declaration sg d.
Proof.
  intros W H; destruct d as [a|a t]; cbn [weak_check_declaration] in H.
  - destruct H as [_ [aty [s [A S]]]].
    destruct (weak_infer_sound _ _ _ _ W (wf_context_nil _) A) as [AT _].
    destruct (weak_as_sort_sound _ _ S) as [C IS].
    split; [exists s; split; [eapply ty_conv; eauto|exact IS]|exact I].
  - destruct (weak_check_sound _ _ _ W H) as [T A]; split; assumption.
Qed.

Theorem weak_check_program_sound allow sg ds final : wf_signature sg ->
  weak_check_program allow sg ds final -> valid_program sg ds final.
Proof.
  intros W H; revert W; induction H; intros W.
  - constructor.
  - pose proof (weak_check_declaration_sound _ _ _ W H) as VD.
    constructor; [exact VD|apply IHweak_check_program; eapply valid_declaration_extends_wf; eauto].
Qed.

Theorem weak_accepted_program_wf allow sg ds final : wf_signature sg ->
  weak_check_program allow sg ds final -> wf_signature final.
Proof.
  intros W H; eapply valid_program_preserves_wf; [exact W|].
  eapply weak_check_program_sound; eauto.
Qed.

Theorem cached_infer_sound sg cache ctx t a :
  inference_cache_valid sg cache -> wf_signature sg -> wf_context sg ctx ->
  cached_infer sg cache ctx t a -> typing sg ctx t a /\ proper_type sg ctx a.
Proof.
  intros VALID W CT H; apply weak_infer_sound; [exact W|exact CT|].
  destruct H; [assumption|apply VALID; assumption].
Qed.

Theorem inference_cache_insert_valid sg cache ctx t a :
  inference_cache_valid sg cache -> weak_infer sg ctx t a ->
  inference_cache_valid sg ((ctx, t, a) :: cache).
Proof.
  intros VALID T c u b [E|H].
  - inversion E; subst; exact T.
  - apply VALID; exact H.
Qed.

Lemma inference_cache_empty_valid sg : inference_cache_valid sg [].
Proof. intros ctx t a H; inversion H. Qed.

(** WHNF leaves binder bodies alone, but conversion still compares them. *)
Example weak_compare_under_pi :
  weak_compare (tPi tType (tApp (tLam tType (tVar 0)) (tConst 0)))
    (tPi tType (tConst 0)).
Proof.
  eapply wc_heads; [apply wh_pi|apply wh_pi|].
  apply wc_pi; [apply wc_refl|].
  eapply wc_heads.
  - eapply wh_beta; [apply wh_lam|cbn [instantiate subst shift]; apply wh_const].
  - apply wh_const.
  - apply wc_same.
Qed.

Example weak_compare_distinct_sorts : ~ weak_compare tType tKind.
Proof.
  intros H; pose proof (weak_equal_sound _ _ H) as C.
  assert (E : tType = tKind) by
    (eapply conv_sort_unique; [left; reflexivity|right; reflexivity|exact C]).
  discriminate.
Qed.
