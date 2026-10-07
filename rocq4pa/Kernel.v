From Stdlib Require Import List Bool.
From Rocq4pa Require Import Syntax.
Import ListNotations.

Definition bind {A B} (x : option A) (f : A -> option B) : option B :=
  match x with Some a => f a | None => None end.
Notation "x <- c ;; f" := (bind c (fun x => f))
  (at level 100, c at next level, right associativity).

(** Fuel bounds recursion depth, not total work. Exhaustion never succeeds. *)
Fixpoint normal (fuel : nat) (t : term) : option term :=
  match fuel with
  | 0 => None
  | S n =>
    match t with
    | tPi a b => a' <- normal n a ;; b' <- normal n b ;; Some (tPi a' b')
    | tLam a b => a' <- normal n a ;; b' <- normal n b ;; Some (tLam a' b')
    | tApp f x =>
      f' <- normal n f ;; x' <- normal n x ;;
      match f' with
      | tLam a b => normal n (instantiate b x')
      | _ => Some (tApp f' x')
      end
    | _ => Some t
    end
  end.

Ltac split_options :=
  unfold bind in *;
  repeat match goal with
  | H : context [match ?x with Some _ => _ | None => _ end] |- _ =>
      destruct x eqn:?; cbn [bind] in H; try discriminate
  | H : context [if ?b then _ else _] |- _ =>
      let T := type of b in unify T bool;
      destruct b eqn:?; cbn [bind] in H; try discriminate
  end.

Theorem normal_sound fuel t u : normal fuel t = Some u -> conv t u.
Proof.
  revert t u; induction fuel as [|n IH]; intros t u H; [discriminate|].
  destruct t as [| |i|i|a b|a b|f x]; cbn [normal bind] in H.
  - inversion H; constructor.
  - inversion H; constructor.
  - inversion H; constructor.
  - inversion H; constructor.
  - split_options; inversion H; subst; apply cv_pi; eauto.
  - split_options; inversion H; subst; apply cv_lam; eauto.
  - destruct (normal n f) as [f'|] eqn:F; try discriminate.
    cbn [bind] in H.
    destruct (normal n x) as [x'|] eqn:X; try discriminate.
    cbn [bind] in H.
    pose proof (IH _ _ F) as CF.
    pose proof (IH _ _ X) as CX.
    destruct f'; try (inversion H; subst; apply cv_app; auto).
    eapply cv_trans; [apply cv_app; eauto|].
    eapply cv_trans; [apply cv_beta|eapply IH; eauto].
Qed.

Definition equal (fuel : nat) (a b : term) : bool :=
  match normal fuel a, normal fuel b with
  | Some a', Some b' => if term_eq_dec a' b' then true else false
  | _, _ => false
  end.

Theorem equal_sound fuel a b : equal fuel a b = true -> conv a b.
Proof.
  unfold equal; intros H; split_options.
  destruct (term_eq_dec t t0); try discriminate; subst.
  eapply cv_trans; [eapply normal_sound; eauto|].
  apply cv_sym; eapply normal_sound; eauto.
Qed.

Definition as_sort fuel a : option term :=
  s <- normal fuel a ;; if sortb s then Some s else None.

Lemma as_sort_sound fuel a s : as_sort fuel a = Some s -> conv a s /\ is_sort s.
Proof.
  unfold as_sort; intros H; cbn [bind] in H; split_options.
  destruct (sortb t) eqn:E; try discriminate.
  inversion H; subst; split; [eapply normal_sound; eauto|apply sortb_sound; auto].
Qed.

Fixpoint infer (fuel : nat) (sg ctx : list term) (t : term) : option term :=
  match fuel with
  | 0 => None
  | S n =>
    match t with
    | tType => Some tKind
    | tKind => None
    | tVar i => a <- nth_error ctx i ;; Some (shift (S i) 0 a)
    | tConst i => nth_error sg i
    | tPi a b =>
      aty <- infer n sg ctx a ;;
      if equal n aty tType then
        bt <- infer n sg (a :: ctx) b ;; as_sort n bt
      else None
    | tLam a b =>
      aty <- infer n sg ctx a ;;
      if equal n aty tType then
        bt <- infer n sg (a :: ctx) b ;;
        pt <- infer n sg ctx (tPi a bt) ;;
        s <- as_sort n pt ;; Some (tPi a bt)
      else None
    | tApp f x =>
      ft <- infer n sg ctx f ;; p <- normal n ft ;;
      match p with
      | tPi a b => xt <- infer n sg ctx x ;;
          if equal n xt a then Some (instantiate b x) else None
      | _ => None
      end
    end
  end.

Theorem infer_sound fuel sg ctx t a :
  infer fuel sg ctx t = Some a -> typing sg ctx t a.
Proof.
  revert sg ctx t a; induction fuel as [|n IH]; intros sg ctx t a H;
    [discriminate|].
  destruct t; cbn [infer bind] in H.
  - inversion H; constructor.
  - discriminate.
  - split_options; inversion H; subst; apply ty_var; auto.
  - apply ty_const; auto.
  - split_options. apply as_sort_sound in H as [C S].
    eapply ty_pi; [eapply ty_conv; [eapply IH; eauto|eapply equal_sound; eauto]| |exact S].
    eapply ty_conv; [eapply IH; eauto|exact C].
  - split_options. inversion H; subst.
    match goal with Q : as_sort _ _ = Some _ |- _ =>
      apply as_sort_sound in Q as [C S] end.
    eapply ty_lam; [eapply ty_conv; [eapply IH; eauto|eapply equal_sound; eauto]
      |eapply IH; eauto| |exact S].
    eapply ty_conv; [eapply IH; eauto|exact C].
  - split_options;
    destruct t0; try discriminate; cbn [bind] in H; split_options.
    inversion H; subst. eapply ty_app.
    + eapply ty_conv; [eapply IH; eauto|eapply normal_sound; eauto].
    + eapply ty_conv; [eapply IH; eauto|eapply equal_sound; eauto].
Qed.

Definition check fuel sg t a : bool :=
  match infer fuel sg [] a, infer fuel sg [] t with
  | Some aty, Some actual =>
      match as_sort fuel aty with
      | Some _ => equal fuel actual a
      | None => false
      end
  | _, _ => false
  end.

Theorem check_sound fuel sg t a : check fuel sg t a = true ->
  typing sg [] t a /\ exists s, typing sg [] a s /\ is_sort s.
Proof.
  unfold check; intros H; split_options.
  match goal with Q : as_sort _ _ = Some _ |- _ =>
    apply as_sort_sound in Q as [C S] end.
  split.
  - eapply ty_conv; [eapply infer_sound; eauto|eapply equal_sound; eauto].
  - eexists; split; [eapply ty_conv; [eapply infer_sound; eauto|exact C]|exact S].
Qed.
