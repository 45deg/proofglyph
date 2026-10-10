From Stdlib Require Import List String.
Import ListNotations.
From Proofglyph.Language Require Export Syntax CodecImpl WeakCheckerImpl.
From Proofglyph.Hieratic Require Export CompileImpl.

Definition compile_proofglyph fuel allow src : option (string * list term) :=
  match compile fuel allow src with
  | Some (ds, sg) => Some (encode_proofglyph ds, sg)
  | None => None
  end.

Definition check_proofglyph fuel allow bytes : option (list term) :=
  match decode_proofglyph bytes with
  | Some ds => check_program fuel allow [] ds
  | None => None
  end.

