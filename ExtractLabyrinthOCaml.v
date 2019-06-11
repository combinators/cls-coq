From mathcomp Require Import all_ssreflect.
Require Import Labyrinth.

Module ExtractedLabyrinthOCaml.
  Require Import Coq.extraction.ExtrOcamlBasic.
  Require Import Coq.extraction.ExtrOcamlNatInt.
  Extract Inductive simpl_fun => "(->)" ["(fun f -> f)"].
  Extract Constant simpl_pred "'a" => "'a -> bool".
  Extract Inlined Constant fun_of_simpl => "(fun f -> f)".
  Extract Inlined Constant pred_of_simpl => "(fun f -> f)".
  Extract Inlined Constant predT => "(fun x -> true)".

  Example small_grammar := (result_grammar small_free small_goal small_start).
  Example small_upto10 := (result_terms_mapped small_free small_goal small_start 10). 

  Example big_grammar (x: unit) := (result_grammar big_free big_goal big_start).
  Example big_upto10 (x: unit) := (result_terms_mapped big_free big_goal big_start 10). 
End ExtractedLabyrinthOCaml.

Extraction Language OCaml.
Extraction "extracted/ExtractedLabyrinth.ml" ExtractedLabyrinthOCaml.