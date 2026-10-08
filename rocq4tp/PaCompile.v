From Stdlib Require Import List String.
From Rocq4pa Require Import Syntax Program WellFormed Checker.
From Rocq4tp Require Import Surface Compile PaCodec.
Import ListNotations.

Definition compile_pa fuel allow src : option (string * list term) :=
  match compile fuel allow src with
  | Some (ds, sg) => Some (encode_pa ds, sg)
  | None => None
  end.

Definition check_pa fuel allow bytes : option (list term) :=
  match decode_pa bytes with
  | Some ds => check_program fuel allow [] ds
  | None => None
  end.

Theorem compile_pa_sound fuel allow src bytes sg :
  compile_pa fuel allow src = Some (bytes, sg) ->
  exists ds, bytes = encode_pa ds /\ decode_pa bytes = Some ds /\
    translates [] src ds /\ source_permitted allow src /\
    valid_program [] ds sg /\ wf_signature sg.
Proof.
  unfold compile_pa; destruct (compile fuel allow src) as [[ds final]|] eqn:C;
    intros H; inversion H; subst.
  destruct (compile_sound _ _ _ _ _ C) as [T [V [P W]]].
  exists ds; split; [reflexivity|]; split; [apply pa_roundtrip|].
  split; [exact T|]; split.
  - apply (proj2 (translates_policy _ _ _ _ T)); exact P.
  - auto.
Qed.

Theorem compile_pa_complete allow src ds sg :
  translates [] src ds -> source_permitted allow src -> valid_program [] ds sg ->
  exists bound, forall fuel, bound <= fuel ->
    compile_pa fuel allow src = Some (encode_pa ds, sg).
Proof.
  intros T P V; apply (proj1 (translates_policy _ _ _ _ T)) in P.
  destruct (compile_complete _ _ _ _ T P V) as [bound B].
  exists bound; intros fuel LE; unfold compile_pa; rewrite (B fuel LE); reflexivity.
Qed.

Theorem compile_pa_recheck fuel allow src bytes sg :
  compile_pa fuel allow src = Some (bytes, sg) -> check_pa fuel allow bytes = Some sg.
Proof.
  unfold compile_pa, compile; destruct (lower [] src) as [ds|] eqn:L; [|discriminate].
  destruct (check_program fuel allow [] ds) eqn:C; intros H; inversion H; subst.
  unfold check_pa; rewrite pa_roundtrip; exact C.
Qed.

Theorem check_pa_sound fuel allow bytes sg : check_pa fuel allow bytes = Some sg ->
  exists ds, decode_pa bytes = Some ds /\ permitted_declarations allow ds /\
    valid_program [] ds sg /\ wf_signature sg.
Proof.
  unfold check_pa; destruct (decode_pa bytes) as [ds|] eqn:D; [|discriminate].
  intros C; assert (W : wf_signature []) by constructor.
  destruct (proj1 (program_correct allow [] ds sg W) (ex_intro _ fuel C)) as [P V].
  exists ds; split; [reflexivity|]; split; [exact P|]; split; [exact V|].
  eapply accepted_program_wf; eauto.
Qed.

Theorem compile_pa_monotone n m allow src bytes sg : n <= m ->
  compile_pa n allow src = Some (bytes, sg) -> compile_pa m allow src = Some (bytes, sg).
Proof.
  intros LE; unfold compile_pa; destruct (compile n allow src) as [[ds final]|] eqn:C;
    intros H; inversion H; subst.
  rewrite (compile_monotone _ _ _ _ _ _ LE C); reflexivity.
Qed.
