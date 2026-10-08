From Stdlib Require Import List String.
From Rocq4tp Require Import Surface.
Import ListNotations.

(** Groups retain their spelling and order. A group always has at least one
    name. Empty parameter sequences represent declarations without arguments. *)
Inductive raw_expr :=
| RName (x : string) | RType | RKind
| RApply (f x : raw_expr)
| RArrow (a b : raw_expr)
| RForall (ps : parameters) (body : raw_expr)
| RLambda (ps : parameters) (body : raw_expr)
with parameters :=
| PNil
| PGroup (first : string) (others : list string) (typ : raw_expr) (rest : parameters).

Scheme raw_expr_mut := Induction for raw_expr Sort Prop
with parameters_mut := Induction for parameters Sort Prop.
Combined Scheme raw_mutind from raw_expr_mut, parameters_mut.

Definition bindings := list (string * expr).

Fixpoint bind_products (ps : bindings) (body : expr) : expr :=
  match ps with [] => body | (x, a) :: rest => Product (Some x) a (bind_products rest body) end.
Fixpoint bind_lambdas (ps : bindings) (body : expr) : expr :=
  match ps with [] => body | (x, a) :: rest => Lambda x a (bind_lambdas rest body) end.

Fixpoint desugar (e : raw_expr) : expr :=
  match e with
  | RName x => Name x | RType => Universe | RKind => Top
  | RApply f x => Apply (desugar f) (desugar x)
  | RArrow a b => Product None (desugar a) (desugar b)
  | RForall ps b => bind_products (desugar_parameters ps) (desugar b)
  | RLambda ps b => bind_lambdas (desugar_parameters ps) (desugar b)
  end
with desugar_parameters (ps : parameters) : bindings :=
  match ps with
  | PNil => []
  | PGroup x xs a rest =>
      map (fun n => (n, desugar a)) (x :: xs) ++ desugar_parameters rest
  end.

(** Relational specifications are independent of the executable folds. Each
    copied annotation is resolved later in its own sequential binder scope. *)
Inductive products : bindings -> expr -> expr -> Prop :=
| products_nil : forall b, products [] b b
| products_cons : forall x a ps b out,
    products ps b out -> products ((x, a) :: ps) b (Product (Some x) a out).

Inductive lambdas : bindings -> expr -> expr -> Prop :=
| lambdas_nil : forall b, lambdas [] b b
| lambdas_cons : forall x a ps b out,
    lambdas ps b out -> lambdas ((x, a) :: ps) b (Lambda x a out).

Lemma products_sound ps b : products ps b (bind_products ps b).
Proof. induction ps as [|[x a] ps IH]; cbn; constructor; assumption. Qed.
Lemma lambdas_sound ps b : lambdas ps b (bind_lambdas ps b).
Proof. induction ps as [|[x a] ps IH]; cbn; constructor; assumption. Qed.
Lemma products_complete ps b out : products ps b out -> bind_products ps b = out.
Proof. intros H; induction H; cbn; congruence. Qed.
Lemma lambdas_complete ps b out : lambdas ps b out -> bind_lambdas ps b = out.
Proof. intros H; induction H; cbn; congruence. Qed.

Inductive expands : raw_expr -> expr -> Prop :=
| expands_name : forall x, expands (RName x) (Name x)
| expands_type : expands RType Universe
| expands_kind : expands RKind Top
| expands_apply : forall f x f' x',
    expands f f' -> expands x x' -> expands (RApply f x) (Apply f' x')
| expands_arrow : forall a b a' b',
    expands a a' -> expands b b' -> expands (RArrow a b) (Product None a' b')
| expands_forall : forall ps b ps' b' out,
    expands_parameters ps ps' -> expands b b' -> products ps' b' out ->
    expands (RForall ps b) out
| expands_lambda : forall ps b ps' b' out,
    expands_parameters ps ps' -> expands b b' -> lambdas ps' b' out ->
    expands (RLambda ps b) out
with expands_parameters : parameters -> bindings -> Prop :=
| expands_pnil : expands_parameters PNil []
| expands_group : forall x xs a rest a' rest',
    expands a a' -> expands_parameters rest rest' ->
    expands_parameters (PGroup x xs a rest) (map (fun n => (n, a')) (x :: xs) ++ rest').

Scheme expands_mut := Induction for expands Sort Prop
with expands_parameters_mut := Induction for expands_parameters Sort Prop.
Combined Scheme expansion_mutind from expands_mut, expands_parameters_mut.

Lemma desugar_sound_mutual :
  (forall e, expands e (desugar e)) /\
  (forall ps, expands_parameters ps (desugar_parameters ps)).
Proof.
  apply raw_mutind; cbn; intros; econstructor; eauto using products_sound, lambdas_sound.
Qed.

Lemma desugar_complete_mutual :
  (forall e out, expands e out -> desugar e = out) /\
  (forall ps out, expands_parameters ps out -> desugar_parameters ps = out).
Proof.
  apply expansion_mutind; cbn; intros; subst; eauto using products_complete, lambdas_complete.
Qed.

Theorem desugar_correct e out : desugar e = out <-> expands e out.
Proof.
  split; [intros <-; apply desugar_sound_mutual|apply desugar_complete_mutual].
Qed.

Theorem desugar_parameters_correct ps out :
  desugar_parameters ps = out <-> expands_parameters ps out.
Proof.
  split; [intros <-; apply desugar_sound_mutual|apply desugar_complete_mutual].
Qed.

Theorem expansion_unique e a b : expands e a -> expands e b -> a = b.
Proof. intros A B; apply desugar_correct in A; apply desugar_correct in B; congruence. Qed.

(** Splitting a group into adjacent groups preserves its sequential meaning,
    even when an earlier name shadows a free name in the annotation. *)
Theorem split_parameter_group x y xs a rest :
  desugar_parameters (PGroup x (y :: xs) a rest) =
  desugar_parameters (PGroup x [] a (PGroup y xs a rest)).
Proof. reflexivity. Qed.

Record raw_declaration := RawDecl {
  raw_name : string;
  raw_type : raw_expr;
  raw_body : option raw_expr
}.

Definition desugar_declaration d :=
  Decl (raw_name d) (desugar (raw_type d)) (option_map desugar (raw_body d)).
Definition desugar_program := map desugar_declaration.

Inductive expands_declaration : raw_declaration -> source_decl -> Prop :=
| expands_assumption : forall n a a', expands a a' ->
    expands_declaration (RawDecl n a None) (Decl n a' None)
| expands_proof : forall n a b a' b', expands a a' -> expands b b' ->
    expands_declaration (RawDecl n a (Some b)) (Decl n a' (Some b')).

Definition expands_program := Forall2 expands_declaration.

Lemma desugar_declaration_sound d : expands_declaration d (desugar_declaration d).
Proof.
  destruct d as [n a [b|]]; cbn; constructor; apply desugar_sound_mutual.
Qed.
Lemma desugar_declaration_complete d out :
  expands_declaration d out -> desugar_declaration d = out.
Proof.
  intros H; destruct H; unfold desugar_declaration; cbn.
  - rewrite (proj2 (desugar_correct _ _) H); reflexivity.
  - rewrite (proj2 (desugar_correct _ _) H), (proj2 (desugar_correct _ _) H0); reflexivity.
Qed.

Theorem desugar_program_correct src out : desugar_program src = out <-> expands_program src out.
Proof.
  split.
  - intros <-; induction src; cbn; constructor; auto using desugar_declaration_sound.
  - intros H; induction H; cbn; [reflexivity|].
    rewrite (desugar_declaration_complete _ _ H), IHForall2; reflexivity.
Qed.

Theorem desugar_names src : map decl_name (desugar_program src) = map raw_name src.
Proof. induction src; cbn; congruence. Qed.

Theorem desugar_kinds src : map is_assumption (desugar_program src) =
  map (fun d => match raw_body d with None => true | Some _ => false end) src.
Proof.
  induction src as [|[n a [b|]] src IH]; cbn; try rewrite IH; reflexivity.
Qed.
