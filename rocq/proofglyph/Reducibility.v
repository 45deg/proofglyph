From Stdlib Require Import List.
From Proofglyph.Language Require Import Syntax Substitution EvaluationSpec Confluence
  Preservation Normalization Arity.
Import ListNotations.

Lemma reduces_substitute t u : reduces t u -> forall s,
  reduces (substitute s t) (substitute s u).
Proof.
  intros R; induction R; intros s; cbn [substitute]; try (constructor; auto; fail).
  rewrite substitute_beta; apply red_beta.
Qed.

Lemma reduces_parallel t u : reduces t u -> parallel t u.
Proof. intros R; induction R; eauto using parallel, parallel_refl. Qed.

Lemma sn_substitution_reflect t s : strongly_normalizing (substitute s t) ->
  strongly_normalizing t.
Proof.
  unfold strongly_normalizing; intros H.
  remember (substitute s t) as v eqn:E; revert t E.
  induction H as [v NEXT IH]; intros t E; subst v.
  constructor; intros u R; eapply IH; [apply reduces_substitute; exact R|reflexivity].
Qed.

Lemma sn_pi a b : strongly_normalizing a -> strongly_normalizing b ->
  strongly_normalizing (tPi a b).
Proof.
  intros A; revert b; induction A as [a NA IHA]; intros b B; induction B as [b NB IHB].
  constructor; intros u R; inversion R; subst.
  - apply IHA; [assumption|constructor; exact NB].
  - apply IHB; assumption.
Qed.

Lemma sn_lam a b : strongly_normalizing a -> strongly_normalizing b ->
  strongly_normalizing (tLam a b).
Proof.
  intros A; revert b; induction A as [a NA IHA]; intros b B; induction B as [b NB IHB].
  constructor; intros u R; inversion R; subst.
  - apply IHA; [assumption|constructor; exact NB].
  - apply IHB; assumption.
Qed.

Definition neutral t := forall a b, t <> tLam a b.

Fixpoint reducible (tau : arity) (t : term) : Prop :=
  match tau with
  | base => strongly_normalizing t
  | arrow a b => strongly_normalizing t /\
      forall x, reducible a x -> reducible b (tApp t x)
  end.

Lemma reducible_sn tau t : reducible tau t -> strongly_normalizing t.
Proof. destruct tau; cbn [reducible]; tauto. Qed.

Lemma reducible_step tau t u : reducible tau t -> reduces t u -> reducible tau u.
Proof.
  revert t u; induction tau as [|a IHA b IHB]; intros t u T R; cbn [reducible] in *.
  - eapply strongly_normalizing_step; eauto.
  - destruct T as [SN APP]; split.
    + eapply strongly_normalizing_step; eauto.
    + intros x X; eapply IHB; [apply APP; exact X|apply red_app_function; exact R].
Qed.

Lemma reducible_steps tau t u : reducible tau t -> beta_steps t u -> reducible tau u.
Proof. intros T R; induction R; eauto using reducible_step. Qed.

Lemma reducible_neutral tau t : neutral t ->
  (forall u, reduces t u -> reducible tau u) -> reducible tau t.
Proof.
  revert t; induction tau as [|a IHA b IHB]; intros t N NEXT; cbn [reducible] in *.
  - constructor; exact NEXT.
  - assert (ST : strongly_normalizing t).
    { constructor; intros u R; exact (proj1 (NEXT u R)). }
    split; [exact ST|]. intros x X.
    pose proof (reducible_sn _ _ X) as SX.
    induction SX as [x NX IHX].
    apply IHB; [intros; discriminate|]. intros u R; inversion R; subst.
    + exfalso; eapply N; reflexivity.
    + exact (proj2 (NEXT _ H2) x X).
    + apply IHX; [assumption|eapply reducible_step; eauto].
Qed.

Lemma reducible_var tau n : reducible tau (tVar n).
Proof. apply reducible_neutral; [intros; discriminate|intros u R; inversion R]. Qed.
Lemma reducible_const tau n : reducible tau (tConst n).
Proof. apply reducible_neutral; [intros; discriminate|intros u R; inversion R]. Qed.

Lemma reducible_beta tau a b x : strongly_normalizing a -> strongly_normalizing b ->
  strongly_normalizing x -> reducible tau (instantiate b x) ->
  reducible tau (tApp (tLam a b) x).
Proof.
  intros A; revert b x; induction A as [a NA IHA]; intros b x B;
    revert x; induction B as [b NB IHB]; intros x X;
    induction X as [x NX IHX]; intros BODY.
  apply reducible_neutral; [intros; discriminate|].
  intros u R; inversion R; subst.
  - exact BODY.
  - match goal with H : reduces (tLam _ _) _ |- _ => inversion H; subst end.
    + apply IHA; [assumption|constructor; exact NB|constructor; exact NX|exact BODY].
    + apply IHB; [assumption|constructor; exact NX|].
      eapply reducible_step; [exact BODY|].
      unfold instantiate; rewrite !subst_as_substitute.
      apply reduces_substitute; assumption.
  - apply IHX; [assumption|].
    eapply reducible_steps; [exact BODY|].
    apply parallel_beta_steps; apply parallel_instantiate; [apply parallel_refl|].
    apply reduces_parallel; assumption.
Qed.

Lemma reducible_lambda a b sigma tau : strongly_normalizing a ->
  (forall x, reducible sigma x -> reducible tau (instantiate b x)) ->
  reducible (arrow sigma tau) (tLam a b).
Proof.
  intros A BODY.
  assert (B : strongly_normalizing b).
  { apply (sn_substitution_reflect b (single (tConst 0))).
    rewrite <- instantiate_as_substitute; apply (reducible_sn tau).
    apply BODY; apply reducible_const. }
  split; [apply sn_lam; assumption|].
  intros x X; apply reducible_beta; eauto using reducible_sn.
Qed.

Definition cons_sub x (s : nat -> term) n := match n with 0 => x | S k => s k end.

Lemma instantiate_substitution s b x :
  instantiate (substitute (up_sub s) b) x = substitute (cons_sub x s) b.
Proof.
  rewrite instantiate_as_substitute, substitute_comp.
  apply substitute_ext; intros [|n]; cbn [up_sub single cons_sub substitute]; [reflexivity|].
  rewrite substitute_after_rename.
  transitivity (substitute (fun n => tVar n) (s n)); [apply substitute_ext; reflexivity|apply substitute_id].
Qed.

Theorem arity_reducibility sg ctx t tau : arity_typing sg ctx t tau ->
  forall sub, (forall n sigma, nth_error ctx n = Some sigma -> reducible sigma (sub n)) ->
  reducible tau (substitute sub t).
Proof.
  intros T; induction T; intros sub ENV; cbn [substitute].
  - apply reducible_neutral; [intros; discriminate|intros u R; inversion R].
  - eapply ENV; eauto.
  - apply reducible_const.
  - cbn [reducible]; apply sn_pi.
    + apply IHT1; exact ENV.
    + apply (sn_substitution_reflect (substitute (up_sub sub) b) (single (tConst 0))).
      rewrite <- instantiate_as_substitute, instantiate_substitution.
      apply IHT2; intros [|n] sigma LOOK; cbn in LOOK; cbn [cons_sub].
      * inversion LOOK; subst; apply reducible_const.
      * eapply ENV; eauto.
  - apply reducible_lambda.
    + exact (IHT1 sub ENV).
    + intros x X; rewrite instantiate_substitution.
      apply IHT2; intros [|n] sigma LOOK; cbn in LOOK; cbn [cons_sub].
      * inversion LOOK; subst; exact X.
      * eapply ENV; eauto.
  - exact (proj2 (IHT1 sub ENV) _ (IHT2 sub ENV)).
Qed.

Theorem arity_strong_normalization sg ctx t tau : arity_typing sg ctx t tau ->
  strongly_normalizing t.
Proof.
  intros T; rewrite <- (substitute_id t).
  apply (reducible_sn tau); eapply arity_reducibility; [exact T|].
  intros; apply reducible_var.
Qed.
