From Stdlib Require Import List.
From Tinyprover.Proofglyph Require Import Syntax Kernel Program WellFormed Checker.
From Tinyprover.Zfc Require Import Formula Axioms Deduction Encoding Certificates.
From Tinyprover.ZfcDeep Require Import Artifact.
Import ListNotations.

Definition zfc_signature := map declared_type prelude.
Definition final_signature := zfc_signature ++ map declared_type proofs.
Definition proof_type p :=
  tApp (tApp (tApp (tConst 72) (encode_index 0)) (tConst 53)) (encode p).

Example prelude_accepted : check_program 128 true [] prelude = Some zfc_signature.
Proof. vm_compute; reflexivity. Qed.
Example certificates_accepted :
  check_program 128 false zfc_signature proofs = Some final_signature.
Proof. vm_compute; reflexivity. Qed.
Theorem zfc_signature_wf : wf_signature zfc_signature.
Proof. eapply accepted_program_wf; [constructor|exact prelude_accepted]. Qed.
Theorem certificates_have_types : valid_program zfc_signature proofs final_signature.
Proof. eapply check_program_sound; [exact zfc_signature_wf|exact certificates_accepted]. Qed.
Theorem certificates_add_no_axioms :
  List.Forall (fun d => match d with Prove _ _ => True | Assume _ => False end) proofs.
Proof.
  pose proof (check_program_no_axioms _ _ _ _ certificates_accepted) as H.
  eapply Forall_impl; [|exact H].
  intros [a|a t]; simpl; [discriminate|auto].
Qed.

(** Check the actual exported AST against the independent formula encoding. *)
Example syntax_prefix : firstn 9 prelude = syntax_prelude.
Proof. vm_compute; reflexivity. Qed.
Example signature_prefix : zfc_signature = syntax_signature ++ skipn 9 zfc_signature.
Proof. vm_compute; reflexivity. Qed.
Definition zax p := tApp (tConst 61) p.
Example fixed_axioms_match :
  map declared_type (firstn 8 (skipn 62 prelude)) =
  map (fun p => zax (encode p))
    [extensionality; empty_set; pairing; union; power_set; infinity; foundation; choice].
Proof. vm_compute; reflexivity. Qed.

Definition scoped_type n p := tApp (tApp (tConst 12) n) p.
Definition rename_type r p q := tApp (tApp (tApp (tConst 43) r) p) q.
Definition close_type n p q := tApp (tApp (tApp (tConst 49) n) p) q.
Definition code_imp p q := tApp (tApp (tConst 7) p) q.
Definition code_all p := tApp (tConst 8) p.
Definition code_neg p := code_imp p (tConst 4).
Definition code_and p q := code_neg (code_imp p (code_neg q)).
Definition code_exists p := code_neg (code_all (code_neg p)).
Definition code_iff p q := code_and (code_imp p q) (code_imp q p).
Definition code_separation_body r := code_all (code_exists (code_all
  (code_iff (encode (Member 0 1)) (code_and (encode (Member 0 2)) r)))).
Definition code_replacement_body v u i := code_all (code_imp
  (code_all (code_imp (encode (Member 0 1)) (code_exists
    (code_and v (code_all (code_imp u (encode (Equal 0 1))))))))
  (code_exists (code_all (code_iff (encode (Member 0 1))
    (code_exists (code_and (encode (Member 0 3)) i)))))).
Lemma separation_body_matches p : code_separation_body (encode p) = encode (separation_body p).
Proof. reflexivity. Qed.
Lemma replacement_body_matches v u i :
  code_replacement_body (encode v) (encode u) (encode i) = encode (replacement_body v u i).
Proof. reflexivity. Qed.

Example separation_rule_matches : nth_error zfc_signature 70 = Some
  (tPi index_type (tPi formula_type (tPi formula_type (tPi formula_type
    (tPi (scoped_type (tApp (tConst 2) (tVar 3)) (tVar 2))
      (tPi (rename_type (tConst 22) (tVar 3) (tVar 2))
        (tPi (close_type (tVar 5) (code_separation_body (tVar 3)) (tVar 2))
          (zax (tVar 3))))))))).
Proof. vm_compute; reflexivity. Qed.
Example replacement_rule_matches : nth_error zfc_signature 71 = Some
  (tPi index_type (tPi formula_type (tPi formula_type (tPi formula_type
    (tPi formula_type (tPi formula_type
      (tPi (scoped_type (tApp (tConst 2) (tApp (tConst 2) (tVar 5))) (tVar 4))
        (tPi (rename_type (tConst 23) (tVar 5) (tVar 4))
          (tPi (rename_type (tConst 24) (tVar 6) (tVar 4))
            (tPi (rename_type (tConst 25) (tVar 7) (tVar 4))
              (tPi (close_type (tVar 9)
                (code_replacement_body (tVar 7) (tVar 6) (tVar 5)) (tVar 4))
                (zax (tVar 5))))))))))))).
Proof. vm_compute; reflexivity. Qed.

Lemma typing_extend sg ctx t a extra : typing sg ctx t a -> typing (sg ++ extra) ctx t a.
Proof.
  intros H; induction H; eauto using typing.
  apply ty_const; rewrite nth_error_app1; [assumption|].
  apply nth_error_Some; rewrite H; discriminate.
Qed.
Lemma formula_code_typed p : typing zfc_signature [] (encode p) formula_type.
Proof. rewrite signature_prefix; apply typing_extend; apply encode_typed. Qed.
Theorem proof_type_sorted p : sorted_type zfc_signature [] (proof_type p).
Proof.
  exists tType; split; [|left; reflexivity].
  unfold proof_type.
  change (typing zfc_signature []
    (tApp (tApp (tApp (tConst 72) (encode_index 0)) (tConst 53)) (encode p))
    (instantiate tType (encode p))).
  eapply ty_app; [|apply formula_code_typed].
  change (typing zfc_signature [] (tApp (tApp (tConst 72) (encode_index 0)) (tConst 53))
    (instantiate (tPi formula_type tType) (tConst 53))).
  eapply ty_app; [|apply ty_const; reflexivity].
  change (typing zfc_signature [] (tApp (tConst 72) (encode_index 0))
    (instantiate (tPi (tConst 52) (tPi formula_type tType)) (encode_index 0))).
  eapply ty_app; [apply ty_const; reflexivity|].
  apply ty_const; reflexivity.
Qed.

(** Translation.v and Reflection.v build on these concrete checker obligations
    to prove translation and inverse adequacy for arbitrary LF terms. *)
Print Assumptions zfc_signature_wf.
Print Assumptions fixed_axioms_match.
Print Assumptions separation_rule_matches.
Print Assumptions replacement_rule_matches.
Print Assumptions proof_type_sorted.
