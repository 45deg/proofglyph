From Proofglyph.Hieratic Require Import Resolve Compile ProofglyphCodec ProofglyphCompile.
From Proofglyph.Hieratic Require Import Desugar SurfaceCompile.

Print Assumptions resolve_correct.
Print Assumptions resolves_unique.
Print Assumptions resolves_extend_globals.
Print Assumptions resolve_scoped.
Print Assumptions lower_correct.
Print Assumptions translates_unique.
Print Assumptions translates_kinds.
Print Assumptions translates_length.
Print Assumptions translates_distinct.
Print Assumptions translates_policy.
Print Assumptions translates_scoped.
Print Assumptions compile_sound.
Print Assumptions compile_complete.
Print Assumptions compile_monotone.
Print Assumptions compile_correct.
Print Assumptions lex_instructions_roundtrip.
Print Assumptions term_code_correct.
Print Assumptions program_code_correct.
Print Assumptions proofglyph_roundtrip.
Print Assumptions encode_proofglyph_injective.
Print Assumptions proofglyph_canonical_roundtrip.
Print Assumptions compile_proofglyph_sound.
Print Assumptions compile_proofglyph_complete.
Print Assumptions compile_proofglyph_recheck.
Print Assumptions check_proofglyph_sound.
Print Assumptions compile_proofglyph_monotone.
Print Assumptions desugar_correct.
Print Assumptions desugar_parameters_correct.
Print Assumptions expansion_unique.
Print Assumptions split_parameter_group.
Print Assumptions desugar_program_correct.
Print Assumptions desugar_names.
Print Assumptions desugar_kinds.
Print Assumptions compile_surface_proofglyph_sound.
Print Assumptions compile_surface_proofglyph_complete.
Print Assumptions compile_surface_proofglyph_recheck.

From Proofglyph.Hieratic Require Import HieraticImports.
Print Assumptions load_hieratic_correct.
Print Assumptions imports_complete.

From Proofglyph.Hieratic Require Import HieraticSyntax FileCompile.
Print Assumptions lex_hieratic_correct.
Print Assumptions parse_hieratic_correct.
Print Assumptions parse_hieratic_unique.
Print Assumptions syntax_complete.
Print Assumptions items_parser_complete.
Print Assumptions prepare_files_correct.
Print Assumptions compile_files_proofglyph_sound.
Print Assumptions compile_files_proofglyph_complete.
Print Assumptions compile_files_proofglyph_recheck.

Print Assumptions compile_files_sound.
Print Assumptions compile_files_complete.
Print Assumptions compile_files_correct.

From Proofglyph.Hieratic Require Import Elaboration.
Print Assumptions expand_constants_correct.
Print Assumptions elaborate_lower_sound.
Print Assumptions elaborate_lower_complete.
Print Assumptions compile_elaborated_sound.
Print Assumptions compile_files_elaborated_sound.
Print Assumptions compile_files_elaborated_recheck.
Print Assumptions compile_elaborated_complete.
Print Assumptions compile_files_elaborated_complete.
Print Assumptions expand_constants_scoped.
