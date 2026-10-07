From Stdlib Require Import List Arith.Wf_nat.
From Rocq4pa Require Import Syntax Substitution Kernel Evaluation Confluence Preservation.

(** Accessibility is oriented towards reducts. It includes reductions inside
    annotations and under binders, just like [normal]. *)
Definition strongly_normalizing t := Acc (fun u t => reduces t u) t.

Inductive beta_plus : term -> term -> Prop :=
| plus_one : forall t u, reduces t u -> beta_plus t u
| plus_more : forall t u v, reduces t u -> beta_plus u v -> beta_plus t v.

Lemma beta_steps_plus t u v : beta_steps t u -> beta_plus u v -> beta_plus t v.
Proof. intros H; induction H; eauto using beta_plus. Qed.

Lemma beta_plus_congruence f :
  (forall t u, reduces t u -> reduces (f t) (f u)) ->
  forall t u, beta_plus t u -> beta_plus (f t) (f u).
Proof. intros F t u H; induction H; eauto using beta_plus. Qed.

Lemma strongly_normalizing_step t u : strongly_normalizing t -> reduces t u ->
  strongly_normalizing u.
Proof. intros H R; exact (Acc_inv H R). Qed.

Lemma strongly_normalizing_plus t : strongly_normalizing t ->
  Acc (fun u t => beta_plus t u) t.
Proof.
  intros H; induction H as [t NEXT IH]. constructor; intros u R.
  inversion R; subst; [apply IH; assumption|].
  eapply Acc_inv; [apply IH; eassumption|eassumption].
Qed.

Lemma evaluates_pi_parts a b u : evaluates (tPi a b) u ->
  (exists a', evaluates a a') /\ (exists b', evaluates b b').
Proof. intros H; inversion H; subst; split; eauto. Qed.
Lemma evaluates_lam_parts a b u : evaluates (tLam a b) u ->
  (exists a', evaluates a a') /\ (exists b', evaluates b b').
Proof. intros H; inversion H; subst; split; eauto. Qed.
Lemma evaluates_app_parts f x u : evaluates (tApp f x) u ->
  (exists f', evaluates f f') /\ (exists x', evaluates x x').
Proof. intros H; inversion H; subst; split; eauto. Qed.

Lemma parallel_steps_beta_steps t u : steps t u -> beta_steps t u.
Proof. intros H; induction H; eauto using beta_refl, beta_trans, parallel_beta_steps. Qed.

Lemma evaluation_from_reducts t :
  (forall u, beta_plus t u -> exists v, evaluates u v) ->
  exists v, evaluates t v.
Proof.
  induction t as [| |n|n|a IHA b IHB|a IHA b IHB|f IHF x IHX]; intros IH.
  - exists tType; constructor.
  - exists tKind; constructor.
  - exists (tVar n); constructor.
  - exists (tConst n); constructor.
  - destruct IHA as [a' A].
    { intros u R. destruct (IH (tPi u b)) as [v E].
      - eapply (beta_plus_congruence (fun z => tPi z b)); [intros; apply red_pi_domain; eassumption|exact R].
      - exact (proj1 (evaluates_pi_parts _ _ _ E)). }
    destruct IHB as [b' B].
    { intros u R. destruct (IH (tPi a u)) as [v E].
      - eapply (beta_plus_congruence (tPi a)); [intros; apply red_pi_body; eassumption|exact R].
      - exact (proj2 (evaluates_pi_parts _ _ _ E)). }
    exists (tPi a' b'); constructor; assumption.
  - destruct IHA as [a' A].
    { intros u R. destruct (IH (tLam u b)) as [v E].
      - eapply (beta_plus_congruence (fun z => tLam z b)); [intros; apply red_lam_domain; eassumption|exact R].
      - exact (proj1 (evaluates_lam_parts _ _ _ E)). }
    destruct IHB as [b' B].
    { intros u R. destruct (IH (tLam a u)) as [v E].
      - eapply (beta_plus_congruence (tLam a)); [intros; apply red_lam_body; eassumption|exact R].
      - exact (proj2 (evaluates_lam_parts _ _ _ E)). }
    exists (tLam a' b'); constructor; assumption.
  - destruct IHF as [f' F].
    { intros u R. destruct (IH (tApp u x)) as [v E].
      - eapply (beta_plus_congruence (fun z => tApp z x)); [intros; apply red_app_function; eassumption|exact R].
      - exact (proj1 (evaluates_app_parts _ _ _ E)). }
    destruct IHX as [x' X].
    { intros u R. destruct (IH (tApp f u)) as [v E].
      - eapply (beta_plus_congruence (tApp f)); [intros; apply red_app_argument; eassumption|exact R].
      - exact (proj2 (evaluates_app_parts _ _ _ E)). }
    destruct f' as [| |n|n|a b|a b|g y];
      try (eexists; apply ev_app; [exact F|exact X|intros; discriminate]).
    destruct (IH (instantiate b x')) as [v E].
    + eapply beta_steps_plus; [|apply plus_one; apply red_beta].
      eapply beta_binary; [intros; apply red_app_function; eassumption|
        intros; apply red_app_argument; eassumption| |].
      * apply parallel_steps_beta_steps; apply evaluates_steps; exact F.
      * apply parallel_steps_beta_steps; apply evaluates_steps; exact X.
    + exists v; eapply ev_beta; eauto.
Qed.

Theorem strongly_normalizing_evaluates t : strongly_normalizing t ->
  exists u, evaluates t u.
Proof.
  intros H; pose proof (strongly_normalizing_plus _ H) as A. clear H.
  induction A as [t NEXT IH]. apply evaluation_from_reducts; exact IH.
Qed.
