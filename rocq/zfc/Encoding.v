From Stdlib Require Import List.
From Tinyprover.Proofglyph Require Import Syntax Kernel Program WellFormed Checker.
From Tinyprover.Zfc Require Import Formula.
Import ListNotations.

(** A deep syntax encoding. Formula binders are object-level constructors,
    not LF binders. Index is a datatype represented by opaque constructors. *)
Definition index_type := tConst 0.
Definition formula_type := tConst 3.
Definition syntax_prelude : list declaration :=
  [Assume tType;                              (* 0: Index *)
   Assume index_type;                         (* 1: zero *)
   Assume (tPi index_type index_type);        (* 2: succ *)
   Assume tType;                              (* 3: Formula *)
   Assume formula_type;                       (* 4: bottom *)
   Assume (tPi index_type (tPi index_type formula_type)); (* 5: eq *)
   Assume (tPi index_type (tPi index_type formula_type)); (* 6: mem *)
   Assume (tPi formula_type (tPi formula_type formula_type)); (* 7: imp *)
   Assume (tPi formula_type formula_type)].   (* 8: all *)
Definition syntax_signature := map declared_type syntax_prelude.

Example syntax_prelude_accepted :
  check_program 32 true [] syntax_prelude = Some syntax_signature.
Proof. vm_compute; reflexivity. Qed.
Theorem syntax_signature_wf : wf_signature syntax_signature.
Proof. eapply accepted_program_wf; [constructor|exact syntax_prelude_accepted]. Qed.

Fixpoint encode_index n := match n with
  | 0 => tConst 1 | S n => tApp (tConst 2) (encode_index n) end.
Fixpoint decode_index t := match t with
  | tConst 1 => Some 0
  | tApp (tConst 2) x => option_map S (decode_index x)
  | _ => None end.

Fixpoint encode p := match p with
  | Bot => tConst 4
  | Equal x y => tApp (tApp (tConst 5) (encode_index x)) (encode_index y)
  | Member x y => tApp (tApp (tConst 6) (encode_index x)) (encode_index y)
  | Implies p q => tApp (tApp (tConst 7) (encode p)) (encode q)
  | Forall p => tApp (tConst 8) (encode p)
  end.
Definition pair_options {A B C} (f : A -> B -> C) (a : option A) (b : option B) :=
  match a,b with Some a,Some b => Some (f a b) | _,_ => None end.
Fixpoint decode t := match t with
  | tConst 4 => Some Bot
  | tApp (tApp (tConst 5) x) y => pair_options Equal (decode_index x) (decode_index y)
  | tApp (tApp (tConst 6) x) y => pair_options Member (decode_index x) (decode_index y)
  | tApp (tApp (tConst 7) p) q => pair_options Implies (decode p) (decode q)
  | tApp (tConst 8) p => option_map Forall (decode p)
  | _ => None end.

Theorem index_roundtrip n : decode_index (encode_index n) = Some n.
Proof. induction n; cbn; [reflexivity|rewrite IHn; reflexivity]. Qed.
Theorem formula_roundtrip p : decode (encode p) = Some p.
Proof.
  induction p; cbn [encode decode];
    repeat rewrite index_roundtrip; try rewrite IHp; try rewrite IHp1; try rewrite IHp2; reflexivity.
Qed.
Theorem encode_injective p q : encode p = encode q -> p = q.
Proof.
  intros H; apply (f_equal decode) in H; rewrite !formula_roundtrip in H; congruence.
Qed.

Lemma index_typed n : typing syntax_signature [] (encode_index n) index_type.
Proof.
  induction n; cbn [encode_index].
  - apply ty_const; reflexivity.
  - change (typing syntax_signature [] (tApp (tConst 2) (encode_index n))
      (instantiate index_type (encode_index n))).
    eapply ty_app; [apply ty_const; reflexivity|exact IHn].
Qed.

Lemma binary_typed k a b domain :
  nth_error syntax_signature k = Some (tPi domain (tPi domain formula_type)) ->
  typing syntax_signature [] a domain -> typing syntax_signature [] b domain ->
  (forall x, instantiate (tPi domain formula_type) x = tPi domain formula_type) ->
  typing syntax_signature [] (tApp (tApp (tConst k) a) b) formula_type.
Proof.
  intros K A B Closed.
  change (typing syntax_signature [] (tApp (tApp (tConst k) a) b) (instantiate formula_type b)).
  eapply ty_app; [|exact B].
  rewrite <- (Closed a).
  eapply ty_app; [apply ty_const; exact K|exact A].
Qed.

Theorem encode_typed p : typing syntax_signature [] (encode p) formula_type.
Proof.
  induction p; cbn [encode].
  - apply ty_const; reflexivity.
  - eapply binary_typed with (domain := index_type); try reflexivity; apply index_typed.
  - eapply binary_typed with (domain := index_type); try reflexivity; apply index_typed.
  - eapply binary_typed with (domain := formula_type); try reflexivity; assumption.
  - change (typing syntax_signature [] (tApp (tConst 8) (encode p))
      (instantiate formula_type (encode p))).
    eapply ty_app; [apply ty_const; reflexivity|exact IHp].
Qed.

Print Assumptions formula_roundtrip.
Print Assumptions encode_injective.
Print Assumptions encode_typed.
Print Assumptions syntax_signature_wf.
