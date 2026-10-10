From Stdlib Require Import Extraction ExtrOcamlBasic.
From Proofglyph.Language Require Import CacheTableImpl.

(** A trusted extraction refinement of the proved persistent-table API.
    The runtime uses immutable keys and persistent versions of hash buckets.
    Its lookup uses the extracted decision procedure, including Zarith numeric
    equality. Hashing must respect equality on the canonical extracted keys.
    This mapping adds no Rocq axiom; runtime correspondence is tested, not proved. *)
Extract Inductive table => "Persistent_hash.t" ["Persistent_hash.of_list"].
Extract Constant table_empty => "Persistent_hash.empty".
Extract Constant table_lookup => "Persistent_hash.find_opt".
Extract Constant table_insert => "Persistent_hash.add".
