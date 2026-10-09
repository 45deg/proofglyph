From Stdlib Require Import List.
From Tinyprover.Proofglyph Require Import Syntax Substitution EvaluationSpec.

Inductive parallel : term -> term -> Prop :=
| par_type : parallel tType tType
| par_kind : parallel tKind tKind
| par_var : forall n, parallel (tVar n) (tVar n)
| par_const : forall n, parallel (tConst n) (tConst n)
| par_pi : forall a a' b b', parallel a a' -> parallel b b' -> parallel (tPi a b) (tPi a' b')
| par_lam : forall a a' b b', parallel a a' -> parallel b b' -> parallel (tLam a b) (tLam a' b')
| par_app : forall f f' x x', parallel f f' -> parallel x x' -> parallel (tApp f x) (tApp f' x')
| par_beta : forall a b b' x x', parallel b b' -> parallel x x' ->
    parallel (tApp (tLam a b) x) (instantiate b' x').

Lemma parallel_refl t : parallel t t.
Proof. induction t; constructor; auto. Qed.

Lemma parallel_rename a b r : parallel a b -> parallel (rename r a) (rename r b).
Proof.
  intros H; revert r; induction H; intros r; cbn [rename]; try (constructor; auto; fail).
  rewrite rename_beta; constructor; auto.
Qed.

Lemma parallel_up s q : (forall n, parallel (s n) (q n)) ->
  forall n, parallel (up_sub s n) (up_sub q n).
Proof. intros E [|n]; cbn [up_sub]; [constructor|apply parallel_rename; apply E]. Qed.

Lemma parallel_substitute a b s q : parallel a b ->
  (forall n, parallel (s n) (q n)) -> parallel (substitute s a) (substitute q b).
Proof.
  intros H; revert s q; induction H; intros s q E; cbn [substitute];
    eauto using parallel, parallel_up.
  rewrite substitute_beta; constructor; eauto using parallel_up.
Qed.

Lemma parallel_instantiate a b x y : parallel a b -> parallel x y ->
  parallel (instantiate a x) (instantiate b y).
Proof.
  intros A X; rewrite !instantiate_as_substitute; apply parallel_substitute; [exact A|].
  intros [|n]; cbn [single]; [exact X|constructor].
Qed.

Fixpoint develop t :=
  match t with
  | tPi a b => tPi (develop a) (develop b)
  | tLam a b => tLam (develop a) (develop b)
  | tApp f x => match f with
      | tLam a b => instantiate (develop b) (develop x)
      | _ => tApp (develop f) (develop x)
      end
  | _ => t
  end.

Theorem parallel_develop a b : parallel a b -> parallel b (develop a).
Proof.
  intros H; induction H; cbn [develop]; try (constructor; auto; fail).
  - destruct f; try (apply par_app; auto; fail).
    inversion H; subst. inversion IHparallel1; subst. apply par_beta; auto.
  - apply parallel_instantiate; auto.
Qed.

Theorem parallel_diamond a b c : parallel a b -> parallel a c ->
  exists d, parallel b d /\ parallel c d.
Proof. intros B C; exists (develop a); split; apply parallel_develop; assumption. Qed.

Inductive steps : term -> term -> Prop :=
| steps_refl : forall a, steps a a
| steps_cons : forall a b c, parallel a b -> steps b c -> steps a c.

Lemma steps_trans a b c : steps a b -> steps b c -> steps a c.
Proof. intros H; induction H; intros C; eauto using steps. Qed.

Lemma parallel_strip a b c : steps a c -> parallel a b ->
  exists d, steps b d /\ parallel c d.
Proof.
  intros H; revert b; induction H; intros z P.
  - exists z; split; [constructor|exact P].
  - destruct (parallel_diamond _ _ _ H P) as [w [BW ZW]].
    destruct (IHsteps _ BW) as [d [WD CD]].
    exists d; split; [econstructor; eauto|exact CD].
Qed.

Theorem steps_confluent a b c : steps a b -> steps a c ->
  exists d, steps b d /\ steps c d.
Proof.
  intros H; revert c; induction H; intros z AZ.
  - exists z; split; [exact AZ|constructor].
  - destruct (parallel_strip _ _ _ AZ H) as [w [BW ZW]].
    destruct (IHsteps _ BW) as [d [CD WD]].
    exists d; split; [exact CD|econstructor; eauto].
Qed.

Definition joins a b := exists c, steps a c /\ steps b c.

Lemma joins_refl a : joins a a.
Proof. exists a; split; constructor. Qed.
Lemma joins_sym a b : joins a b -> joins b a.
Proof. intros [c [A B]]; exists c; auto. Qed.
Lemma joins_trans a b c : joins a b -> joins b c -> joins a c.
Proof.
  intros [x [AX BX]] [y [BY CY]].
  destruct (steps_confluent _ _ _ BX BY) as [z [XZ YZ]].
  exists z; split; eapply steps_trans; eauto.
Qed.

Lemma steps_congruence (f : term -> term) :
  (forall a b, parallel a b -> parallel (f a) (f b)) ->
  forall a b, steps a b -> steps (f a) (f b).
Proof. intros F a b H; induction H; [constructor|econstructor; eauto]. Qed.

Lemma joins_binary (f : term -> term -> term) :
  (forall a a' b b', parallel a a' -> parallel b b' -> parallel (f a b) (f a' b')) ->
  forall a a' b b', joins a a' -> joins b b' -> joins (f a b) (f a' b').
Proof.
  intros F a a' b b' [x [AX AX']] [y [BY BY']].
  exists (f x y); split.
  - eapply steps_trans with (b := f x b).
    + eapply (steps_congruence (fun z => f z b)); [intros; apply F; [eauto|apply parallel_refl]|exact AX].
    + eapply (steps_congruence (f x)); [intros; apply F; [apply parallel_refl|eauto]|exact BY].
  - eapply steps_trans with (b := f x b').
    + eapply (steps_congruence (fun z => f z b')); [intros; apply F; [eauto|apply parallel_refl]|exact AX'].
    + eapply (steps_congruence (f x)); [intros; apply F; [apply parallel_refl|eauto]|exact BY'].
Qed.

Theorem conv_joins a b : conv a b -> joins a b.
Proof.
  intros H; induction H; eauto using joins_refl, joins_sym, joins_trans.
  - apply joins_binary; eauto using par_pi.
  - apply joins_binary; eauto using par_lam.
  - apply joins_binary; eauto using par_app.
  - exists (instantiate b x); split; [|constructor].
    econstructor; [apply par_beta; apply parallel_refl|constructor].
Qed.

Inductive normal_form : term -> Prop :=
| nf_type : normal_form tType
| nf_kind : normal_form tKind
| nf_var : forall n, normal_form (tVar n)
| nf_const : forall n, normal_form (tConst n)
| nf_pi : forall a b, normal_form a -> normal_form b -> normal_form (tPi a b)
| nf_lam : forall a b, normal_form a -> normal_form b -> normal_form (tLam a b)
| nf_app : forall f x, normal_form f -> normal_form x ->
    (forall a b, f <> tLam a b) -> normal_form (tApp f x).

Lemma evaluates_normal_form t u : evaluates t u -> normal_form u.
Proof. intros H; induction H; eauto using normal_form. Qed.

Lemma parallel_normal_form a b : parallel a b -> normal_form a -> a = b.
Proof.
  intros H; induction H; intros N; inversion N; subst; try reflexivity;
    try (f_equal; auto; fail).
  exfalso; apply (H5 a b); reflexivity.
Qed.

Lemma steps_normal_form a b : steps a b -> normal_form a -> a = b.
Proof.
  intros H; induction H; intros N; [reflexivity|].
  pose proof (parallel_normal_form _ _ H N); subst; auto.
Qed.

Theorem normal_forms_unique a b : conv a b -> normal_form a -> normal_form b -> a = b.
Proof.
  intros C A B; destruct (conv_joins _ _ C) as [d [AD BD]].
  transitivity d; [eapply steps_normal_form; eauto|symmetry; eapply steps_normal_form; eauto].
Qed.

Theorem convertible_evaluations_agree a b u v :
  conv a b -> evaluates a u -> evaluates b v -> u = v.
Proof.
  intros C A B.
  apply normal_forms_unique; eauto using evaluates_normal_form.
  eapply cv_trans; [apply cv_sym; eapply evaluation_conv; exact A|].
  eapply cv_trans; [exact C|eapply evaluation_conv; exact B].
Qed.

Lemma parallel_conv a b : parallel a b -> conv a b.
Proof.
  intros H; induction H; eauto using conv.
Qed.

Lemma steps_conv a b : steps a b -> conv a b.
Proof. intros H; induction H; eauto using cv_refl, cv_trans, parallel_conv. Qed.

Lemma steps_pi_inv t u : steps t u -> forall a b, t = tPi a b ->
  exists a' b', u = tPi a' b' /\ steps a a' /\ steps b b'.
Proof.
  intros H; induction H; intros x y E; subst.
  - exists x, y; repeat split; constructor.
  - inversion H; subst.
    destruct (IHsteps _ _ eq_refl) as [x' [y' [U [X Y]]]].
    exists x', y'; repeat split; eauto using steps.
Qed.

Theorem conv_pi_injective a b c d : conv (tPi a b) (tPi c d) ->
  conv a c /\ conv b d.
Proof.
  intros H; destruct (conv_joins _ _ H) as [u [L R]].
  destruct (steps_pi_inv _ _ L _ _ eq_refl) as [a' [b' [U [A B]]]].
  destruct (steps_pi_inv _ _ R _ _ eq_refl) as [c' [d' [V [C D]]]].
  subst u; inversion V; subst.
  split; eapply cv_trans; [eapply steps_conv; eauto|apply cv_sym; eapply steps_conv; eauto
    |eapply steps_conv; eauto|apply cv_sym; eapply steps_conv; eauto].
Qed.
