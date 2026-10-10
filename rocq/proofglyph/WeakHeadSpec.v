From Stdlib Require Import List.
From Proofglyph.Language Require Export Syntax Program.
Import ListNotations.

(** Finite executions of the OCaml weak-head strategy, without a fuel
    parameter. Inductive derivations describe terminating executions only;
    no termination claim is made for arbitrary untyped terms. *)
Inductive weak_head : term -> term -> Prop :=
| wh_type : weak_head tType tType
| wh_kind : weak_head tKind tKind
| wh_var : forall n, weak_head (tVar n) (tVar n)
| wh_const : forall n, weak_head (tConst n) (tConst n)
| wh_pi : forall a b, weak_head (tPi a b) (tPi a b)
| wh_lam : forall a b, weak_head (tLam a b) (tLam a b)
| wh_app : forall f x f', weak_head f f' ->
    (forall a b, f' <> tLam a b) ->
    weak_head (tApp f x) (tApp f' x)
| wh_beta : forall f x a body u, weak_head f (tLam a body) ->
    weak_head (instantiate body x) u -> weak_head (tApp f x) u.

(** Successful recursive comparisons. An identical term succeeds directly.
    Otherwise, expose both heads and compare every child, including binder
    annotations. This is stronger than comparing only outer constructors. *)
Inductive weak_compare : term -> term -> Prop :=
| wc_refl : forall t, weak_compare t t
| wc_heads : forall a b u v,
    weak_head a u -> weak_head b v -> weak_components u v ->
    weak_compare a b
with weak_components : term -> term -> Prop :=
| wc_same : forall t, weak_components t t
| wc_pi : forall a b c d, weak_compare a c -> weak_compare b d ->
    weak_components (tPi a b) (tPi c d)
| wc_lam : forall a b c d, weak_compare a c -> weak_compare b d ->
    weak_components (tLam a b) (tLam c d)
| wc_app : forall a b c d, weak_compare a c -> weak_compare b d ->
    weak_components (tApp a b) (tApp c d).

Scheme weak_compare_ind' := Induction for weak_compare Sort Prop
with weak_components_ind' := Induction for weak_components Sort Prop.
Combined Scheme weak_comparison_ind from weak_compare_ind', weak_components_ind'.

Definition weak_sort t s := weak_head t s /\ is_sort s.

(** Finite successful inference executions. The lambda rule deliberately
    models the OCaml check [body_type <> Kind], without rechecking its Pi. *)
Inductive weak_infer (sg : list term) : list term -> term -> term -> Prop :=
| wi_type : forall ctx, weak_infer sg ctx tType tKind
| wi_var : forall ctx n a, nth_error ctx n = Some a ->
    weak_infer sg ctx (tVar n) (shift (S n) 0 a)
| wi_const : forall ctx n a, nth_error sg n = Some a ->
    weak_infer sg ctx (tConst n) a
| wi_pi : forall ctx a b aty bt s,
    weak_infer sg ctx a aty -> weak_sort aty tType ->
    weak_infer sg (a :: ctx) b bt -> weak_sort bt s ->
    weak_infer sg ctx (tPi a b) s
| wi_lam : forall ctx a b aty bt,
    weak_infer sg ctx a aty -> weak_sort aty tType ->
    weak_infer sg (a :: ctx) b bt -> bt <> tKind ->
    weak_infer sg ctx (tLam a b) (tPi a bt)
| wi_app : forall ctx f x ft a b xt,
    weak_infer sg ctx f ft -> weak_head ft (tPi a b) ->
    weak_infer sg ctx x xt -> weak_compare xt a ->
    weak_infer sg ctx (tApp f x) (instantiate b x).

Definition weak_check sg t a := exists aty actual s,
  weak_infer sg [] a aty /\ weak_sort aty s /\
  weak_infer sg [] t actual /\ weak_compare actual a.

Definition weak_check_declaration (allow : bool) sg d :=
  match d with
  | Assume a => allow = true /\ exists aty s,
      weak_infer sg [] a aty /\ weak_sort aty s
  | Prove a t => weak_check sg t a
  end.

Inductive weak_check_program (allow : bool) :
    list term -> list declaration -> list term -> Prop :=
| wcp_nil : forall sg, weak_check_program allow sg [] sg
| wcp_cons : forall sg d ds final,
    weak_check_declaration allow sg d ->
    weak_check_program allow (sg ++ [declared_type d]) ds final ->
    weak_check_program allow sg (d :: ds) final.

(** Each inference-cache entry contains the entire local context and term.
    Validity is relative to one signature: clear the cache on registration,
    as OCaml does, rather than reusing this invariant for a new signature. *)
Definition inference_cache := list (list term * term * term).
Definition inference_cache_valid sg (cache : inference_cache) :=
  forall ctx t a, In (ctx, t, a) cache -> weak_infer sg ctx t a.

Inductive cached_infer sg (cache : inference_cache) ctx t a : Prop :=
| ci_compute : weak_infer sg ctx t a -> cached_infer sg cache ctx t a
| ci_hit : In (ctx, t, a) cache -> cached_infer sg cache ctx t a.
