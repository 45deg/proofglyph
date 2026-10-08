From Stdlib Require Import List String.
From Tinyprover.Tp Require Export FileSpec.
From Tinyprover.Tp Require Import TpSyntaxImpl TpImportsImpl SurfaceCompileImpl.
Import ListNotations.

Fixpoint canonicalize_items (resolve : path_resolver) origin items :=
  match items with
  | [] => Some []
  | TpDeclaration d::rest => option_map (cons (TpDeclaration d)) (canonicalize_items resolve origin rest)
  | TpImport spelling::rest => match resolve origin spelling, canonicalize_items resolve origin rest with
      | Some target, Some canonical => Some (TpImport target::canonical) | _, _ => None end
  end.
Fixpoint prepare_files (resolve : path_resolver) (inputs : file_inputs) : option tp_files :=
  match inputs with
  | [] => Some []
  | (path,bytes)::rest => match parse_tp bytes with
    | None => None
    | Some items => match canonicalize_items resolve path items, prepare_files resolve rest with
      | Some canonical, Some files => Some ((path,canonical)::files) | _, _ => None end
    end
  end.
Definition compile_files fuel allow resolve inputs entry :=
  match prepare_files resolve inputs with
  | Some files => match load_tp files entry with
    | Some raw => compile_surface fuel allow raw | None => None end
  | None => None end.
Definition compile_files_pa fuel allow resolve inputs entry :=
  match prepare_files resolve inputs with
  | Some files => match load_tp files entry with
    | Some raw => compile_surface_pa fuel allow raw | None => None end
  | None => None end.
