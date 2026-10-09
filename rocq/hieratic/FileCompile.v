From Stdlib Require Import List String.
From Proofglyph.Language Require Import Codec.
From Proofglyph.Hieratic Require Export FileImpl.
From Proofglyph.Hieratic Require Import HieraticSyntax HieraticImports Desugar Compile SurfaceCompile ProofglyphCompile.
Import ListNotations.

Theorem canonicalize_correct resolve origin items canonical :
  canonicalize_items resolve origin items = Some canonical <-> canonical_items resolve origin items canonical.
Proof.
  split.
  - revert canonical; induction items as [|[d|spelling] rest IH]; intros canonical H; cbn in H.
    + inversion H; constructor.
    + destruct (canonicalize_items resolve origin rest) eqn:R; inversion H; subst.
      constructor; apply IH; reflexivity.
    + destruct (resolve origin spelling) eqn:T; [|discriminate].
      destruct (canonicalize_items resolve origin rest) eqn:R; inversion H; subst.
      constructor; [exact T|apply IH; reflexivity].
  - intros H; induction H; cbn; try rewrite H; try rewrite IHcanonical_items; reflexivity.
Qed.
Theorem prepare_files_correct resolve inputs files :
  prepare_files resolve inputs = Some files <-> parsed_files resolve inputs files.
Proof.
  split.
  - revert files; induction inputs as [|[path bytes] rest IH]; intros files H; cbn [prepare_files] in H.
    + inversion H; constructor.
    + destruct (parse_hieratic bytes) as [items|] eqn:P; [|discriminate].
      destruct (canonicalize_items resolve path items) as [canonical|] eqn:C; [|discriminate].
      destruct (prepare_files resolve rest) eqn:R; inversion H; subst.
      econstructor; [apply parse_hieratic_correct; exact P|apply canonicalize_correct; exact C|apply IH; reflexivity].
  - intros H; induction H; cbn [prepare_files]; [reflexivity|].
    rewrite (proj2 (parse_hieratic_correct _ _) H), (proj2 (canonicalize_correct _ _ _ _) H0), IHparsed_files; reflexivity.
Qed.
Theorem compile_files_proofglyph_sound fuel allow resolve inputs entry bytes sg :
  compile_files_proofglyph fuel allow resolve inputs entry = Some (bytes,sg) ->
  files_spec resolve inputs entry allow bytes sg /\ wf_signature sg.
Proof.
  unfold compile_files_proofglyph; destruct (prepare_files resolve inputs) as [files|] eqn:F; [|discriminate].
  destruct (load_hieratic files entry) as [raw|] eqn:L; [|discriminate].
  intros C; destruct (compile_surface_proofglyph_sound _ _ _ _ _ C)
    as [src [ds [E [B [D [T [P [V W]]]]]]]].
  split; [|exact W]; exists files,raw,src,ds; repeat split; auto.
  - apply prepare_files_correct; exact F.
  - apply load_hieratic_correct; exact L.
  - apply decode_proofglyph_correct; exact D.
Qed.
(** Completeness returns canonical output; valid noncanonical input proofglyph bytes
    in files_spec denote the same declarations but need not be reproduced. *)
Theorem compile_files_proofglyph_complete allow resolve inputs entry files raw src ds sg :
  parsed_files resolve inputs files -> imports_program files entry raw ->
  expands_program raw src -> translates [] src ds -> source_permitted allow src ->
  valid_program [] ds sg -> exists bound, forall fuel, bound <= fuel ->
  compile_files_proofglyph fuel allow resolve inputs entry = Some (encode_proofglyph ds,sg).
Proof.
  intros F L E T P V.
  destruct (compile_surface_proofglyph_complete _ _ _ _ _ E T P V) as [bound C].
  exists bound; intros fuel LE; unfold compile_files_proofglyph.
  rewrite (proj2 (prepare_files_correct _ _ _) F), (proj2 (load_hieratic_correct _ _ _) L); apply C; exact LE.
Qed.
Theorem compile_files_proofglyph_recheck fuel allow resolve inputs entry bytes sg :
  compile_files_proofglyph fuel allow resolve inputs entry = Some (bytes,sg) ->
  check_proofglyph fuel allow bytes = Some sg.
Proof.
  unfold compile_files_proofglyph; destruct (prepare_files resolve inputs) as [files|]; [|discriminate].
  destruct (load_hieratic files entry); [|discriminate]; apply compile_surface_proofglyph_recheck.
Qed.

Theorem compile_files_sound fuel allow resolve inputs entry ds sg :
  compile_files fuel allow resolve inputs entry = Some (ds,sg) ->
  exists files raw src,
    parsed_files resolve inputs files /\ imports_program files entry raw /\
    expands_program raw src /\ translates [] src ds /\ source_permitted allow src /\
    valid_program [] ds sg /\ wf_signature sg.
Proof.
  unfold compile_files; destruct (prepare_files resolve inputs) as [files|] eqn:F; [|discriminate].
  destruct (load_hieratic files entry) as [raw|] eqn:L; [|discriminate].
  unfold compile_surface; intros C.
  destruct (compile_sound _ _ _ _ _ C) as [T [V [P W]]].
  exists files,raw,(desugar_program raw); repeat split; auto.
  - apply prepare_files_correct; exact F.
  - apply load_hieratic_correct; exact L.
  - apply desugar_program_correct; reflexivity.
  - apply (proj2 (translates_policy _ _ _ _ T)); exact P.
Qed.
Theorem compile_files_complete allow resolve inputs entry files raw src ds sg :
  parsed_files resolve inputs files -> imports_program files entry raw ->
  expands_program raw src -> translates [] src ds -> source_permitted allow src ->
  valid_program [] ds sg -> exists bound, forall fuel, bound <= fuel ->
  compile_files fuel allow resolve inputs entry = Some (ds,sg).
Proof.
  intros F L E T P V; apply desugar_program_correct in E; subst src.
  apply (proj1 (translates_policy _ _ _ _ T)) in P.
  destruct (compile_complete _ _ _ _ T P V) as [bound C].
  exists bound; intros fuel LE; unfold compile_files.
  rewrite (proj2 (prepare_files_correct _ _ _) F), (proj2 (load_hieratic_correct _ _ _) L).
  apply C; exact LE.
Qed.
Theorem compile_files_correct allow resolve inputs entry ds sg :
  (exists fuel, compile_files fuel allow resolve inputs entry = Some (ds,sg)) <->
  exists files raw src,
    parsed_files resolve inputs files /\ imports_program files entry raw /\
    expands_program raw src /\ translates [] src ds /\ source_permitted allow src /\ valid_program [] ds sg.
Proof.
  split.
  - intros [fuel C]; destruct (compile_files_sound _ _ _ _ _ _ _ C) as [files [raw [src [F [L [E [T [P [V W]]]]]]]]].
    exists files,raw,src; repeat split; assumption.
  - intros [files [raw [src [F [L [E [T [P V]]]]]]]].
    destruct (compile_files_complete _ _ _ _ _ _ _ _ _ F L E T P V) as [bound C].
    exists bound; apply C; reflexivity.
Qed.
