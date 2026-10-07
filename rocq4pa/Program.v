From Stdlib Require Import List Bool.
From Rocq4pa Require Import Syntax Kernel.
Import ListNotations.

Inductive declaration :=
| Assume (a : term)
| Prove (a proof : term).

Definition declared_type d := match d with Assume a | Prove a _ => a end.

Definition valid_declaration sg d : Prop :=
  (exists s, typing sg [] (declared_type d) s /\ is_sort s) /\
  match d with Assume _ => True | Prove a t => typing sg [] t a end.

Definition check_declaration fuel (allow_axioms : bool) sg d : bool :=
  match d with
  | Assume a =>
      if allow_axioms then
        match infer fuel sg [] a with
        | Some aty => match as_sort fuel aty with Some _ => true | None => false end
        | None => false
        end
      else false
  | Prove a t => check fuel sg t a
  end.

Theorem check_declaration_sound fuel allow sg d :
  check_declaration fuel allow sg d = true -> valid_declaration sg d.
Proof.
  destruct d; cbn [check_declaration valid_declaration declared_type]; intros H.
  - destruct allow; try discriminate; split_options.
    match goal with Q : as_sort _ _ = Some _ |- _ =>
      apply as_sort_sound in Q as [C S] end.
    split; [eexists; split; [eapply ty_conv; [eapply infer_sound; eauto|exact C]|exact S]|exact I].
  - apply check_sound in H as [T W].
    unfold valid_declaration; cbn [declared_type]; auto.
Qed.

Fixpoint check_program fuel allow sg ds : option (list term) :=
  match ds with
  | [] => Some sg
  | d :: rest => if check_declaration fuel allow sg d then
      check_program fuel allow (sg ++ [declared_type d]) rest else None
  end.

(** Each declaration is justified using only the preceding signature. *)
Inductive valid_program : list term -> list declaration -> list term -> Prop :=
| vp_nil : forall sg, valid_program sg [] sg
| vp_cons : forall sg d ds final,
    valid_declaration sg d ->
    valid_program (sg ++ [declared_type d]) ds final ->
    valid_program sg (d :: ds) final.

Theorem check_program_sound fuel allow sg ds final :
  check_program fuel allow sg ds = Some final -> valid_program sg ds final.
Proof.
  revert sg; induction ds as [|d ds IH]; intros sg H; cbn [check_program] in H.
  - inversion H; constructor.
  - destruct (check_declaration fuel allow sg d) eqn:E; try discriminate.
    constructor; [eapply check_declaration_sound; eauto|apply IH; auto].
Qed.

Theorem no_axioms fuel sg ds final :
  check_program fuel false sg ds = Some final ->
  Forall (fun d => match d with Prove _ _ => True | Assume _ => False end) ds.
Proof.
  revert sg; induction ds as [|d ds IH]; intros sg H; [constructor|].
  destruct d; cbn [check_program check_declaration] in H; try discriminate.
  destruct (check fuel sg proof a); try discriminate.
  constructor; [exact I|eapply IH; eauto].
Qed.
