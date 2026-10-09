From Stdlib Require Import List String Arith Lia.
Import ListNotations.
From Proofglyph.Language Require Import CheckerImpl.
From Proofglyph.Hieratic Require Export CompileSpec ResolveImpl.

Definition lower_decl (gs : globals) (d : source_decl) : option declaration :=
  match resolve gs [] (decl_type d) with
  | None => None
  | Some a => match decl_body d with
      | None => Some (Assume a)
      | Some b => option_map (Prove a) (resolve gs [] b)
      end
  end.

Fixpoint lower (gs : globals) (src : list source_decl) : option (list declaration) :=
  match src with
  | [] => Some []
  | d :: rest =>
      if in_dec string_dec (decl_name d) gs then None else
      match lower_decl gs d, lower (gs ++ [decl_name d]) rest with
      | Some d', Some rest' => Some (d' :: rest') | _, _ => None end
  end.

Definition compile (fuel : nat) (allow : bool) (src : list source_decl)
  : option (list declaration * list term) :=
  match lower [] src with
  | None => None
  | Some ds => match check_program fuel allow [] ds with
      | None => None | Some sg => Some (ds, sg) end
  end.

