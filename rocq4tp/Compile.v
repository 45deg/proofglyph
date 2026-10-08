From Stdlib Require Import List String Arith.
From Rocq4pa Require Import Syntax Program WellFormed Checker.
From Rocq4tp Require Import Surface Resolve.
Import ListNotations.

Definition lower_decl (gs : globals) (d : source_decl) : option declaration :=
  match resolve gs [] (decl_type d) with
  | None => None
  | Some a => match decl_body d with
      | None => Some (Assume a)
      | Some b => option_map (Prove a) (resolve gs [] b)
      end
  end.

Fixpoint lower (gs : globals) (src : list source_decl) : option (list declaration) :=
  match src with
  | [] => Some []
  | d :: rest =>
      if in_dec string_dec (decl_name d) gs then None else
      match lower_decl gs d, lower (gs ++ [decl_name d]) rest with
      | Some d', Some rest' => Some (d' :: rest') | _, _ => None end
  end.

Inductive translates_decl (gs : globals) : source_decl -> declaration -> Prop :=
| translates_assume : forall n a a',
    resolves gs [] a a' -> translates_decl gs (Decl n a None) (Assume a')
| translates_prove : forall n a b a' b',
    resolves gs [] a a' -> resolves gs [] b b' ->
    translates_decl gs (Decl n a (Some b)) (Prove a' b').

(** Source order, declaration kinds and the preceding-name environment are
    part of the specification, rather than inferred from checker acceptance. *)
Inductive translates : globals -> list source_decl -> list declaration -> Prop :=
| translates_nil : forall gs, translates gs [] []
| translates_cons : forall gs d rest d' rest',
    ~ In (decl_name d) gs -> translates_decl gs d d' ->
    translates (gs ++ [decl_name d]) rest rest' ->
    translates gs (d :: rest) (d' :: rest').

Lemma lower_decl_sound gs d d' : lower_decl gs d = Some d' -> translates_decl gs d d'.
Proof.
  destruct d as [n a [b|]]; unfold lower_decl; cbn.
  - destruct (resolve gs [] a) eqn:A; [|discriminate].
    destruct (resolve gs [] b) eqn:B; cbn; intros H; inversion H; subst.
    constructor; apply resolve_sound; assumption.
  - destruct (resolve gs [] a) eqn:A; intros H; inversion H; subst.
    constructor; apply resolve_sound; assumption.
Qed.

Lemma lower_decl_complete gs d d' : translates_decl gs d d' -> lower_decl gs d = Some d'.
Proof.
  intros H; destruct H; unfold lower_decl; cbn;
    rewrite (resolve_complete _ _ _ _ H); try rewrite (resolve_complete _ _ _ _ H0); reflexivity.
Qed.

Theorem lower_sound gs src ds : lower gs src = Some ds -> translates gs src ds.
Proof.
  revert gs ds; induction src as [|d rest IH]; intros gs ds H; cbn in H.
  - inversion H; constructor.
  - destruct (in_dec string_dec (decl_name d) gs); [discriminate|].
    destruct (lower_decl gs d) eqn:D; [|discriminate].
    destruct (lower (gs ++ [decl_name d]) rest) eqn:R; inversion H; subst.
    constructor; auto using lower_decl_sound.
Qed.

Theorem lower_complete gs src ds : translates gs src ds -> lower gs src = Some ds.
Proof.
  intros H; induction H; cbn; [reflexivity|].
  destruct (in_dec string_dec (decl_name d) gs); [contradiction|].
  rewrite (lower_decl_complete _ _ _ H0), IHtranslates; reflexivity.
Qed.

Theorem lower_correct gs src ds : lower gs src = Some ds <-> translates gs src ds.
Proof. split; [apply lower_sound|apply lower_complete]. Qed.

Theorem translates_unique gs src ds es : translates gs src ds -> translates gs src es -> ds = es.
Proof. intros A B; apply lower_complete in A; apply lower_complete in B; congruence. Qed.

Definition core_is_assumption d := match d with Assume _ => true | Prove _ _ => false end.

Theorem translates_kinds gs src ds :
  translates gs src ds -> map is_assumption src = map core_is_assumption ds.
Proof.
  intros H; induction H; cbn; [reflexivity|].
  rewrite IHtranslates; destruct H0; reflexivity.
Qed.

Theorem translates_length gs src ds : translates gs src ds -> List.length src = List.length ds.
Proof. intros H; induction H; cbn; congruence. Qed.

Lemma translates_fresh gs src ds : translates gs src ds ->
  forall n, In n gs -> ~ In n (map decl_name src).
Proof.
  intros H; induction H; intros n IN; cbn; [tauto|].
  intros [E|TAIL].
  - subst; contradiction.
  - apply (IHtranslates n); [apply in_or_app; left; exact IN|exact TAIL].
Qed.

Theorem translates_distinct gs src ds : translates gs src ds -> NoDup (map decl_name src).
Proof.
  intros H; induction H; cbn; constructor; [|assumption].
  eapply translates_fresh; [exact H1|].
  apply in_or_app; right; cbn; auto.
Qed.

Definition source_permitted allow src :=
  Forall (fun d => match decl_body d with None => allow = true | Some _ => True end) src.

Theorem translates_policy allow gs src ds : translates gs src ds ->
  (source_permitted allow src <-> permitted_declarations allow ds).
Proof.
  intros H; induction H; unfold source_permitted, permitted_declarations in *.
  - split; intros; constructor.
  - rewrite !Forall_cons_iff, <- IHtranslates; destruct H0; reflexivity.
Qed.

Fixpoint scoped_declarations (n : nat) (ds : list declaration) : Prop :=
  match ds with
  | [] => True
  | d :: rest => scoped n 0 (declared_type d) /\
      (match d with Assume _ => True | Prove _ b => scoped n 0 b end) /\
      scoped_declarations (S n) rest
  end.

Theorem translates_scoped gs src ds :
  translates gs src ds -> scoped_declarations (List.length gs) ds.
Proof.
  intros H; induction H; cbn; [exact I|].
  rewrite length_app in IHtranslates; cbn in IHtranslates.
  rewrite Nat.add_1_r in IHtranslates.
  destruct H0; cbn; repeat split; auto;
    eapply resolves_scoped with (ls := []); eauto.
Qed.

Definition compile (fuel : nat) (allow : bool) (src : list source_decl)
  : option (list declaration * list term) :=
  match lower [] src with
  | None => None
  | Some ds => match check_program fuel allow [] ds with
      | None => None | Some sg => Some (ds, sg) end
  end.

Theorem compile_sound fuel allow src ds sg : compile fuel allow src = Some (ds, sg) ->
  translates [] src ds /\ valid_program [] ds sg /\
  permitted_declarations allow ds /\ wf_signature sg.
Proof.
  unfold compile; destruct (lower [] src) eqn:L; [|discriminate].
  destruct (check_program fuel allow [] l) eqn:C; intros H; inversion H; subst.
  assert (W : wf_signature []) by constructor.
  split; [apply lower_sound; exact L|].
  split; [eapply check_program_sound; eauto|].
  split.
  - destruct (proj1 (program_correct allow [] ds sg W) (ex_intro _ fuel C)) as [P _].
    exact P.
  - eapply accepted_program_wf; eauto.
Qed.

Theorem compile_complete allow src ds sg :
  translates [] src ds -> permitted_declarations allow ds -> valid_program [] ds sg ->
  exists bound, forall fuel, bound <= fuel -> compile fuel allow src = Some (ds, sg).
Proof.
  intros T P V.
  destruct (empty_signature_program_complete _ _ _ P V) as [bound B].
  exists bound; intros fuel LE; unfold compile.
  rewrite (lower_complete _ _ _ T), (B fuel LE); reflexivity.
Qed.

Theorem compile_monotone n m allow src ds sg : n <= m ->
  compile n allow src = Some (ds, sg) -> compile m allow src = Some (ds, sg).
Proof.
  intros LE; unfold compile; destruct (lower [] src); [|discriminate].
  destruct (check_program n allow [] l) eqn:C; intros H; inversion H; subst.
  rewrite (program_monotone _ _ _ _ _ _ LE C); reflexivity.
Qed.

Theorem compile_correct allow src ds sg :
  (exists fuel, compile fuel allow src = Some (ds, sg)) <->
  translates [] src ds /\ source_permitted allow src /\ valid_program [] ds sg.
Proof.
  split.
  - intros [fuel H]; destruct (compile_sound _ _ _ _ _ H) as [T [V [P W]]].
    split; [exact T|]; split; [apply (proj2 (translates_policy _ _ _ _ T)); exact P|exact V].
  - intros [T [P V]].
    apply (proj1 (translates_policy _ _ _ _ T)) in P.
    destruct (compile_complete _ _ _ _ T P V) as [bound B].
    exists bound; apply B; reflexivity.
Qed.
