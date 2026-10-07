From Stdlib Require Import List.
From Rocq4pa Require Import Syntax Kernel Program.
Import ListNotations.

(** Declaration types must themselves be types/kinds in the preceding
    signature. This permits axioms; it does not require logical consistency,
    a proof of each axiom, normalization, or successful execution of a checker. *)
Inductive wf_signature : list term -> Prop :=
| wf_signature_nil : wf_signature []
| wf_signature_snoc : forall sg a s,
    wf_signature sg -> typing sg [] a s -> is_sort s ->
    wf_signature (sg ++ [a]).

(** Local bindings are stored newest first, relative to their older context. *)
Inductive wf_context (sg : list term) : list term -> Prop :=
| wf_context_nil : wf_context sg []
| wf_context_cons : forall ctx a,
    wf_context sg ctx -> typing sg ctx a tType -> wf_context sg (a :: ctx).

Definition sorted_type sg ctx a := exists s, typing sg ctx a s /\ is_sort s.

(** --no-axioms is a policy, independent of whether a declaration is valid. *)
Definition permitted_declarations allow ds :=
  Forall (fun d => match d with Assume _ => allow = true | Prove _ _ => True end) ds.

Lemma valid_declaration_extends_wf sg d : wf_signature sg ->
  valid_declaration sg d -> wf_signature (sg ++ [declared_type d]).
Proof.
  intros W [[s [T S]] _]; eapply wf_signature_snoc; eauto.
Qed.

Theorem valid_program_preserves_wf sg ds final : wf_signature sg ->
  valid_program sg ds final -> wf_signature final.
Proof.
  intros W V; induction V; [exact W|].
  apply IHV; eapply valid_declaration_extends_wf; eauto.
Qed.

Theorem accepted_program_preserves_wf fuel allow sg ds final :
  wf_signature sg -> check_program fuel allow sg ds = Some final -> wf_signature final.
Proof.
  intros W H; eapply valid_program_preserves_wf; [exact W|].
  eapply check_program_sound; eauto.
Qed.

Corollary accepted_prelude_wf fuel ds sg :
  check_program fuel true [] ds = Some sg -> wf_signature sg.
Proof. intros H; eapply accepted_program_preserves_wf; [constructor|exact H]. Qed.

Lemma wf_signature_last sg a : wf_signature (sg ++ [a]) ->
  wf_signature sg /\ sorted_type sg [] a.
Proof.
  intros W; inversion W as [|prefix ty s WP T S E].
  - destruct sg; discriminate.
  - apply app_inj_tail in E as [E1 E2]; subst.
    split; [assumption|exists s; auto].
Qed.

Lemma kind_has_no_type sg ctx a : ~ typing sg ctx tKind a.
Proof.
  intros H; remember tKind as t eqn:E; induction H; inversion E; subst; auto.
Qed.

Lemma kind_domain_has_no_type sg ctx body a : ~ typing sg ctx (tLam tKind body) a.
Proof.
  intros H; remember (tLam tKind body) as t eqn:E; induction H; inversion E; subst; auto.
  eapply kind_has_no_type; eauto.
Qed.

Lemma kind_domain_application_has_no_type sg ctx body arg a :
  ~ typing sg ctx (tApp (tLam tKind body) arg) a.
Proof.
  intros H; remember (tApp (tLam tKind body) arg) as t eqn:E;
    induction H; inversion E; subst; auto.
  eapply kind_domain_has_no_type; eauto.
Qed.
