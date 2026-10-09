From Stdlib Require Import List Bool.
From Tinyprover.Proofglyph Require Import Syntax.
Import ListNotations.

Inductive declaration :=
| Assume (a : term)
| Prove (a proof : term).

Definition declared_type d := match d with Assume a | Prove a _ => a end.

Definition valid_declaration sg d : Prop :=
  (exists s, typing sg [] (declared_type d) s /\ is_sort s) /\
  match d with Assume _ => True | Prove a t => typing sg [] t a end.

(** Each declaration is justified using only the preceding signature. *)
Inductive valid_program : list term -> list declaration -> list term -> Prop :=
| vp_nil : forall sg, valid_program sg [] sg
| vp_cons : forall sg d ds final,
    valid_declaration sg d ->
    valid_program (sg ++ [declared_type d]) ds final ->
    valid_program sg (d :: ds) final.
