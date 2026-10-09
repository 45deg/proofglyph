From Stdlib Require Import List String Arith Lia.
Import ListNotations.
From Proofglyph.Hieratic Require Export Surface.

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

Inductive products : bindings -> expr -> expr -> Prop :=
| products_nil : forall b, products [] b b
| products_cons : forall x a ps b out,
    products ps b out -> products ((x, a) :: ps) b (Product (Some x) a out).

Inductive lambdas : bindings -> expr -> expr -> Prop :=
| lambdas_nil : forall b, lambdas [] b b
| lambdas_cons : forall x a ps b out,
    lambdas ps b out -> lambdas ((x, a) :: ps) b (Lambda x a out).

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

Record raw_declaration := RawDecl {
  raw_name : string;
  raw_type : raw_expr;
  raw_body : option raw_expr
}.

Inductive expands_declaration : raw_declaration -> source_decl -> Prop :=
| expands_assumption : forall n a a', expands a a' ->
    expands_declaration (RawDecl n a None) (Decl n a' None)
| expands_proof : forall n a b a' b', expands a a' -> expands b b' ->
    expands_declaration (RawDecl n a (Some b)) (Decl n a' (Some b')).

Definition expands_program := Forall2 expands_declaration.


Lemma products_unique ps body a b : products ps body a -> products ps body b -> a = b.
Proof. intros A; revert b; induction A; intros other B; inversion B; subst; f_equal; auto. Qed.
Lemma lambdas_unique ps body a b : lambdas ps body a -> lambdas ps body b -> a = b.
Proof. intros A; revert b; induction A; intros other B; inversion B; subst; f_equal; auto. Qed.
Lemma expansion_unique_mutual :
  (forall e a b, expands e a -> expands e b -> a = b) /\
  (forall ps a b, expands_parameters ps a -> expands_parameters ps b -> a = b).
Proof.
  apply raw_mutind; intros;
    repeat match goal with H : expands ?e _ |- _ => tryif is_var e then fail 0 else (inversion H; clear H; subst) end;
    repeat match goal with H : expands_parameters ?ps _ |- _ => tryif is_var ps then fail 0 else (inversion H; clear H; subst) end;
    repeat match goal with
    | IH : forall a b, expands ?e a -> expands ?e b -> a = b,
      A : expands ?e ?x, B : expands ?e ?y |- _ =>
        tryif constr_eq x y then fail 0 else (let E := fresh in pose proof (IH x y A B) as E; subst y)
    | IH : forall a b, expands_parameters ?ps a -> expands_parameters ?ps b -> a = b,
      A : expands_parameters ?ps ?x, B : expands_parameters ?ps ?y |- _ =>
        tryif constr_eq x y then fail 0 else (let E := fresh in pose proof (IH x y A B) as E; subst y)
    end; eauto using products_unique, lambdas_unique; f_equal; auto.
Qed.
Theorem expansion_unique e a b : expands e a -> expands e b -> a = b.
Proof. apply expansion_unique_mutual. Qed.
