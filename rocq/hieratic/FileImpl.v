From Stdlib Require Import List String.
From Proofglyph.Hieratic Require Export FileSpec.
From Proofglyph.Hieratic Require Import HieraticSyntaxImpl HieraticImportsImpl SurfaceCompileImpl.
Import ListNotations.

Fixpoint canonicalize_items (resolve : path_resolver) origin items :=
  match items with
  | [] => Some []
  | HieraticDeclaration d::rest => option_map (cons (HieraticDeclaration d)) (canonicalize_items resolve origin rest)
  | HieraticImport spelling::rest => match resolve origin spelling, canonicalize_items resolve origin rest with
      | Some target, Some canonical => Some (HieraticImport target::canonical) | _, _ => None end
  end.
Fixpoint prepare_files (resolve : path_resolver) (inputs : file_inputs) : option hieratic_files :=
  match inputs with
  | [] => Some []
  | (path,bytes)::rest => match parse_hieratic bytes with
    | None => None
    | Some items => match canonicalize_items resolve path items, prepare_files resolve rest with
      | Some canonical, Some files => Some ((path,canonical)::files) | _, _ => None end
    end
  end.
Definition compile_files fuel allow resolve inputs entry :=
  match prepare_files resolve inputs with
  | Some files => match load_hieratic files entry with
    | Some raw => compile_surface fuel allow raw | None => None end
  | None => None end.
Definition compile_files_proofglyph fuel allow resolve inputs entry :=
  match prepare_files resolve inputs with
  | Some files => match load_hieratic files entry with
    | Some raw => compile_surface_proofglyph fuel allow raw | None => None end
  | None => None end.
