From Stdlib Require Import List String Arith Lia.
From Proofglyph.Language Require Import Evaluation Codec CachedChecker.
From Proofglyph.Hieratic Require Import Desugar Compile HieraticImports FileCompile ProofglyphCompile.
Import ListNotations.
Open Scope list_scope.

(** Closed, already-expanded definition bodies, indexed by registration order.
    Assumptions and opaque theorems have no macro body. *)
Definition definitions := list (option term).
Fixpoint expand_constants (env : definitions) (t : term) : term :=
  match t with
  | tConst n => match nth_error env n with Some (Some b) => b | _ => t end
  | tPi a b => tPi (expand_constants env a) (expand_constants env b)
  | tLam a b => tLam (expand_constants env a) (expand_constants env b)
  | tApp f x => tApp (expand_constants env f) (expand_constants env x)
  | _ => t end.

(** A relational macro-expansion specification, separate from the traversal. *)
Inductive macro_expands (env : definitions) : term -> term -> Prop :=
| mx_type : macro_expands env tType tType
| mx_kind : macro_expands env tKind tKind
| mx_var : forall n, macro_expands env (tVar n) (tVar n)
| mx_defined : forall n b, nth_error env n = Some (Some b) -> macro_expands env (tConst n) b
| mx_opaque : forall n, (nth_error env n = None \/ nth_error env n = Some None) ->
    macro_expands env (tConst n) (tConst n)
| mx_pi : forall a b a' b', macro_expands env a a' -> macro_expands env b b' ->
    macro_expands env (tPi a b) (tPi a' b')
| mx_lam : forall a b a' b', macro_expands env a a' -> macro_expands env b b' ->
    macro_expands env (tLam a b) (tLam a' b')
| mx_app : forall f x f' x', macro_expands env f f' -> macro_expands env x x' ->
    macro_expands env (tApp f x) (tApp f' x').
Theorem expand_constants_correct env t u : expand_constants env t = u <-> macro_expands env t u.
Proof.
  split.
  - intros <-; induction t; cbn; try solve [constructor; auto].
    destruct (nth_error env n) as [[b|]|] eqn:E; eauto using mx_defined, mx_opaque.
  - intros H; induction H; cbn; try rewrite H; try rewrite IHmacro_expands1, IHmacro_expands2; auto.
    destruct H as [H|H]; rewrite H; reflexivity.
Qed.
Definition expand_declaration env d := match d with
  | Assume a => Assume (expand_constants env a)
  | Prove a b => Prove (expand_constants env a) (expand_constants env b) end.
Inductive macro_declaration env : declaration -> declaration -> Prop :=
| md_assume : forall a a', macro_expands env a a' -> macro_declaration env (Assume a) (Assume a')
| md_prove : forall a b a' b', macro_expands env a a' -> macro_expands env b b' ->
    macro_declaration env (Prove a b) (Prove a' b').
Lemma expand_declaration_correct env d out : expand_declaration env d = out <-> macro_declaration env d out.
Proof.
  split.
  - intros <-; destruct d; constructor; apply expand_constants_correct; reflexivity.
  - intros H; destruct H; cbn; f_equal; apply expand_constants_correct; assumption.
Qed.
Definition normalize_declaration fuel d := match d with
  | Assume a => option_map Assume (normal fuel a)
  | Prove a b => match normal fuel a, normal fuel b with
      | Some a', Some b' => Some (Prove a' b') | _, _ => None end end.
Inductive normalizes_declaration : declaration -> declaration -> Prop :=
| nd_assume : forall a a', evaluates a a' -> normalizes_declaration (Assume a) (Assume a')
| nd_prove : forall a b a' b', evaluates a a' -> evaluates b b' ->
    normalizes_declaration (Prove a b) (Prove a' b').
Lemma normalize_declaration_sound fuel d out : normalize_declaration fuel d = Some out -> normalizes_declaration d out.
Proof.
  destruct d; cbn; destruct (normal fuel a) eqn:A; try discriminate.
  - intros H; inversion H; constructor; eauto using normal_evaluates.
  - destruct (normal fuel proof) eqn:B; intros H; inversion H; constructor; eauto using normal_evaluates.
Qed.
Lemma normalize_declaration_complete d out : normalizes_declaration d out ->
  eventually (fun fuel => normalize_declaration fuel d = Some out).
Proof.
  intros H; destruct H.
  - destruct (normal_complete _ _ H) as [k K]; exists k; intros n LE; cbn; rewrite (K n LE); reflexivity.
  - destruct (eventually_and _ _ (normal_complete _ _ H) (normal_complete _ _ H0)) as [k K].
    exists k; intros n LE; destruct (K n LE) as [A B]; cbn; rewrite A,B; reflexivity.
Qed.
Definition extend_definitions env d out := env ++
  [if raw_transparent d then match out with Prove _ b => Some b | _ => None end else None].

(** The source relation preserves fresh names, macro expansion before beta
    reduction, and the normalized body only for a transparent def. *)
Inductive elaborates : globals -> definitions -> list raw_declaration -> list declaration -> list declaration -> Prop :=
| el_nil : forall gs env, elaborates gs env [] [] []
| el_cons : forall gs env d rest resolved raw out raws outs,
    ~ In (raw_name d) gs ->
    translates_decl gs (desugar_declaration d) resolved ->
    macro_declaration env resolved raw -> normalizes_declaration raw out ->
    elaborates (gs ++ [raw_name d]) (extend_definitions env d out) rest raws outs ->
    elaborates gs env (d::rest) (raw::raws) (out::outs).
Fixpoint elaborate_lower fuel gs env src : option (list declaration * list declaration) :=
  match src with
  | [] => Some ([],[])
  | d::rest => if in_dec string_dec (raw_name d) gs then None else
    match lower_decl gs (desugar_declaration d) with
    | None => None
    | Some resolved => let raw := expand_declaration env resolved in
      match normalize_declaration fuel raw with
      | None => None
      | Some out => match elaborate_lower fuel (gs ++ [raw_name d]) (extend_definitions env d out) rest with
          | Some (raws,outs) => Some (raw::raws,out::outs) | None => None end
      end
    end
  end.
Theorem elaborate_lower_sound fuel gs env src raws outs :
  elaborate_lower fuel gs env src = Some (raws,outs) -> elaborates gs env src raws outs.
Proof.
  revert gs env raws outs; induction src as [|d rest IH]; intros gs env raws outs H; cbn in H.
  - inversion H; constructor.
  - destruct (in_dec string_dec (raw_name d) gs); [discriminate|].
    destruct (lower_decl gs (desugar_declaration d)) eqn:R; [|discriminate].
    destruct (normalize_declaration fuel (expand_declaration env d0)) eqn:N; [|discriminate].
    destruct (elaborate_lower fuel (gs ++ [raw_name d]) (extend_definitions env d d1) rest) as [[rs os]|] eqn:L;
      inversion H; subst.
    econstructor; eauto using lower_decl_sound, normalize_declaration_sound.
    apply expand_declaration_correct; reflexivity.
Qed.
Theorem elaborate_lower_complete gs env src raws outs : elaborates gs env src raws outs ->
  eventually (fun fuel => elaborate_lower fuel gs env src = Some (raws,outs)).
Proof.
  intros H; induction H.
  - exists 0; reflexivity.
  - destruct (eventually_and _ _ (normalize_declaration_complete _ _ H2) IHelaborates) as [k K].
    exists k; intros n LE; destruct (K n LE) as [N L]; cbn.
    destruct (in_dec string_dec (raw_name d) gs); [contradiction|].
    rewrite (lower_decl_complete _ _ _ H0), (proj2 (expand_declaration_correct _ _ _) H1), N,L; reflexivity.
Qed.
Definition compile_elaborated fuel allow src :=
  match elaborate_lower fuel [] [] src with
  | None => None
  | Some (raws,outs) => match check_program fuel allow [] raws, check_program fuel allow [] outs with
    | Some _, Some sg => Some (outs,sg) | _, _ => None end end.
Theorem compile_elaborated_sound fuel allow src outs sg : compile_elaborated fuel allow src = Some (outs,sg) ->
  exists raws raw_sg, elaborates [] [] src raws outs /\ valid_program [] raws raw_sg /\
    valid_program [] outs sg /\ permitted_declarations allow outs /\ wf_signature sg.
Proof.
  unfold compile_elaborated; destruct (elaborate_lower fuel [] [] src) as [[rs os]|] eqn:L; [|discriminate].
  destruct (check_program fuel allow [] rs) eqn:R; [|discriminate].
  destruct (check_program fuel allow [] os) eqn:O; intros H; inversion H; subst.
  destruct (proj1 (program_correct allow [] rs l ltac:(constructor)) (ex_intro _ fuel R)) as [PR VR].
  destruct (proj1 (program_correct allow [] outs sg ltac:(constructor)) (ex_intro _ fuel O)) as [PO VO].
  exists rs,l; repeat split; auto.
  - eapply elaborate_lower_sound; exact L.
  - eapply valid_program_preserves_wf; [constructor|exact VO].
Qed.
Definition compile_files_elaborated fuel allow resolve inputs entry :=
  match prepare_files resolve inputs with
  | Some files => match load_hieratic files entry with
      | Some src => compile_elaborated fuel allow src | None => None end
  | None => None end.
Definition compile_files_elaborated_proofglyph fuel allow resolve inputs entry :=
  match compile_files_elaborated fuel allow resolve inputs entry with
  | Some (ds,sg) => Some (encode_proofglyph ds,sg) | None => None end.
Theorem compile_files_elaborated_sound fuel allow resolve inputs entry outs sg :
  compile_files_elaborated fuel allow resolve inputs entry = Some (outs,sg) ->
  exists files src raws raw_sg, parsed_files resolve inputs files /\ imports_program files entry src /\
    elaborates [] [] src raws outs /\ valid_program [] raws raw_sg /\ valid_program [] outs sg /\
    permitted_declarations allow outs /\ wf_signature sg.
Proof.
  unfold compile_files_elaborated; destruct (prepare_files resolve inputs) as [files|] eqn:F; [|discriminate].
  destruct (load_hieratic files entry) as [src|] eqn:L; [|discriminate].
  intros C; destruct (compile_elaborated_sound _ _ _ _ _ C) as [rs [rsg [E [R [V [P W]]]]]].
  exists files,src,rs,rsg; repeat split; auto.
  - apply prepare_files_correct; exact F.
  - apply load_hieratic_correct; exact L.
Qed.
Theorem compile_files_elaborated_recheck fuel allow resolve inputs entry bytes sg :
  compile_files_elaborated_proofglyph fuel allow resolve inputs entry = Some (bytes,sg) ->
  check_proofglyph fuel allow bytes = Some sg.
Proof.
  unfold compile_files_elaborated_proofglyph, compile_files_elaborated, compile_elaborated.
  destruct (prepare_files resolve inputs); [|discriminate].
  destruct (load_hieratic h entry); [|discriminate].
  destruct (elaborate_lower fuel [] [] l) as [[rs os]|]; [|discriminate].
  destruct (check_program fuel allow [] rs); [|discriminate].
  destruct (check_program fuel allow [] os) eqn:C; intros H; inversion H; subst.
  unfold check_proofglyph; rewrite proofglyph_roundtrip; exact C.
Qed.

Theorem compile_elaborated_complete allow src raws outs raw_sg sg :
  elaborates [] [] src raws outs ->
  permitted_declarations allow raws -> valid_program [] raws raw_sg ->
  permitted_declarations allow outs -> valid_program [] outs sg ->
  eventually (fun fuel => compile_elaborated fuel allow src = Some (outs,sg)).
Proof.
  intros E RP RV OP OV.
  destruct (elaborate_lower_complete _ _ _ _ _ E) as [l L].
  destruct (empty_signature_program_complete _ _ _ RP RV) as [r R].
  destruct (empty_signature_program_complete _ _ _ OP OV) as [o O].
  exists (Nat.max l (Nat.max r o)); intros n LE; unfold compile_elaborated.
  rewrite (L n ltac:(lia)), (R n ltac:(lia)), (O n ltac:(lia)); reflexivity.
Qed.
Theorem compile_files_elaborated_complete allow resolve inputs entry files src raws outs raw_sg sg :
  parsed_files resolve inputs files -> imports_program files entry src ->
  elaborates [] [] src raws outs ->
  permitted_declarations allow raws -> valid_program [] raws raw_sg ->
  permitted_declarations allow outs -> valid_program [] outs sg ->
  eventually (fun fuel => compile_files_elaborated_proofglyph fuel allow resolve inputs entry =
    Some (encode_proofglyph outs,sg)).
Proof.
  intros F I E RP RV OP OV.
  destruct (compile_elaborated_complete _ _ _ _ _ _ E RP RV OP OV) as [k K].
  exists k; intros n LE; unfold compile_files_elaborated_proofglyph, compile_files_elaborated.
  rewrite (proj2 (prepare_files_correct _ _ _) F), (proj2 (load_hieratic_correct _ _ _) I), (K n LE); reflexivity.
Qed.

Lemma scoped_mono n m d e t : n <= m -> d <= e -> scoped n d t -> scoped m e t.
Proof.
  revert d e; induction t; intros d e NM DE S; cbn in *; try tauto; try lia.
  - destruct S as [S1 S2]; split.
    + exact (IHt1 d e NM DE S1).
    + exact (IHt2 (Datatypes.S d) (Datatypes.S e) NM ltac:(lia) S2).
  - destruct S as [S1 S2]; split.
    + exact (IHt1 d e NM DE S1).
    + exact (IHt2 (Datatypes.S d) (Datatypes.S e) NM ltac:(lia) S2).
  - destruct S as [S1 S2]; split; [exact (IHt1 d e NM DE S1) | exact (IHt2 d e NM DE S2)].
Qed.
(** Replacing a constant with a closed definition cannot capture a local binder. *)
Theorem expand_constants_scoped env n d t :
  (forall i b, nth_error env i = Some (Some b) -> scoped n 0 b) ->
  scoped n d t -> scoped n d (expand_constants env t).
Proof.
  intros CLOSED; revert d; induction t; intros d S; cbn in *; try tauto.
  - destruct (nth_error env n0) as [[b|]|] eqn:E; auto.
    exact (scoped_mono n n 0 d b (Nat.le_refl n) (Nat.le_0_l d) (CLOSED _ _ E)).
  - destruct S; split; auto.
  - destruct S; split; auto.
  - destruct S; split; auto.
Qed.
