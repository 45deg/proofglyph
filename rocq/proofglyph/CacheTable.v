From Stdlib Require Import List.
From Proofglyph.Language Require Export CacheTableImpl.
Import ListNotations.

Definition table_valid {K V} (P : K -> V -> Prop) (t : table K V) :=
  match t with Table entries => forall k v, In (k, v) entries -> P k v end.
Lemma table_empty_valid {K V} (P : K -> V -> Prop) : table_valid P (table_empty tt).
Proof. intros k v H; inversion H. Qed.
Lemma table_lookup_valid {K V} eq (P : K -> V -> Prop) t k v :
  table_valid P t -> table_lookup eq k t = Some v -> P k v.
Proof.
  destruct t as [entries]; cbn; intros VALID; induction entries as [|[key value] rest IH];
    cbn; [discriminate|].
  destruct (eq k key) as [E|E].
  - subst key; intros H; inversion H; subst value; apply VALID; left; reflexivity.
  - apply IH; intros a b H; apply VALID; right; exact H.
Qed.
Lemma table_insert_valid {K V} (P : K -> V -> Prop) t k v :
  table_valid P t -> P k v -> table_valid P (table_insert k v t).
Proof.
  destruct t as [entries]; cbn; intros VALID NEW a b [E|H].
  - inversion E; subst; exact NEW.
  - apply VALID; exact H.
Qed.
Lemma table_lookup_insert_same {K V} eq (t : table K V) k v :
  table_lookup eq k (table_insert k v t) = Some v.
Proof. destruct t; cbn; destruct (eq k k); congruence. Qed.
Lemma table_lookup_insert_other {K V} eq (t : table K V) k other v :
  k <> other -> table_lookup eq k (table_insert other v t) = table_lookup eq k t.
Proof. destruct t; cbn; intros N; destruct (eq k other); congruence. Qed.
