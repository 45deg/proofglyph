From Stdlib Require Import List.
From Proofglyph.Language Require Import Syntax.
From Proofglyph.Calculi Require Import Calculi.
Import ListNotations.

Fixpoint encode_index i := match i with
| 0 => tConst 1 | S i => tApp (tConst 2) (encode_index i)
end.
Fixpoint decode_index t := match t with
| tConst 1 => Some 0
| tApp (tConst 2) u => option_map S (decode_index u)
| _ => None
end.
Definition code_binary i a b := tApp (tApp (tConst i) a) b.
Fixpoint encode f := match f with
| Atom i => tApp (tConst 4) (encode_index i)
| Bottom => tConst 5 | Top => tConst 6
| Imp a b => code_binary 7 (encode a) (encode b)
| Conj a b => code_binary 8 (encode a) (encode b)
| Disj a b => code_binary 9 (encode a) (encode b)
| Neg a => tApp (tConst 10) (encode a)
end.
Definition decode_binary (c : formula -> formula -> formula) (a b : option formula) := match a,b with
| Some a,Some b => Some (c a b) | _,_ => None
end.
Fixpoint decode t := match t with
| tApp (tConst 4) i => option_map Atom (decode_index i)
| tConst 5 => Some Bottom | tConst 6 => Some Top
| tApp (tApp (tConst 7) a) b => decode_binary Imp (decode a) (decode b)
| tApp (tApp (tConst 8) a) b => decode_binary Conj (decode a) (decode b)
| tApp (tApp (tConst 9) a) b => decode_binary Disj (decode a) (decode b)
| tApp (tConst 10) a => option_map Neg (decode a)
| _ => None
end.
Fixpoint encode_context g := match g with
| [] => tConst 12 | a :: g => code_binary 13 (encode a) (encode_context g)
end.
Fixpoint decode_context t := match t with
| tConst 12 => Some []
| tApp (tApp (tConst 13) a) g => match decode a,decode_context g with
  | Some a,Some g => Some (a :: g) | _,_ => None end
| _ => None
end.

Lemma index_roundtrip i : decode_index (encode_index i) = Some i.
Proof. induction i; simpl; [reflexivity|rewrite IHi; reflexivity]. Qed.
Theorem formula_roundtrip f : decode (encode f) = Some f.
Proof.
  induction f; simpl; try rewrite index_roundtrip;
    try rewrite IHf; try rewrite IHf1, IHf2; reflexivity.
Qed.
Theorem context_roundtrip g : decode_context (encode_context g) = Some g.
Proof. induction g; simpl; [reflexivity|rewrite formula_roundtrip, IHg; reflexivity]. Qed.
Corollary encode_injective a b : encode a = encode b -> a = b.
Proof.
  intros E; apply (f_equal decode) in E; rewrite !formula_roundtrip in E; congruence.
Qed.
Print Assumptions formula_roundtrip.
Print Assumptions context_roundtrip.
Print Assumptions encode_injective.
