From Stdlib Require Import List.
From Proofglyph.Language Require Import CachedChecker.
Import ListNotations.

Definition type_cache : inference_table :=
  table_insert ([], tType) (1, tKind) (table_empty tt).
Example cache_hit : infer 1 [] [] tType type_cache = Some (tKind, type_cache).
Proof. vm_compute; reflexivity. Qed.
Example zero_fuel_still_fails : infer 0 [] [] tType type_cache = None.
Proof. reflexivity. Qed.
Example insufficient_hit_bound_recomputes :
  let cache : inference_table := table_insert ([], tType) (20, tKind) (table_empty tt) in
  option_map fst (infer 1 [] [] tType cache) = Some tKind.
Proof. vm_compute; reflexivity. Qed.
Example full_context_key :
  let cache : inference_table := table_insert ([tType], tVar 0) (1, tType) (table_empty tt) in
  option_map fst (infer 1 [] [tKind] (tVar 0) cache) = Some tKind.
Proof. vm_compute; reflexivity. Qed.
Example no_failure_inserted : infer 20 [] [] tKind (table_empty tt) = None.
Proof. vm_compute; reflexivity. Qed.
Example signature_reset :
  check_program 20 true [] [Assume tType; Assume (tConst 0); Assume (tConst 1)] = None.
Proof. vm_compute; reflexivity. Qed.
