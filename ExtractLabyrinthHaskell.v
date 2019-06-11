From mathcomp Require Import all_ssreflect.
Require Import Labyrinth.

Module ExtractedLabyrinthHaskell.
  Require Import Coq.extraction.ExtrHaskellBasic.
  Require Import Coq.extraction.ExtrHaskellNatInteger.
  Extract Inlined Constant fst => "(Prelude.fst)".
  Extract Inlined Constant snd => "(Prelude.snd)".
  Extract Inlined Constant proj1_sig => "(Prelude.id)".
  Extract Inductive sigT => "(,)" [ "(,)" ].
  Extract Inlined Constant projT1 => "(Prelude.fst)".
  Extract Inlined Constant projT2 => "(Prelude.snd)".
  Extract Inlined Constant cat => "(Prelude.++)".
  Extract Inlined Constant zip => "(Prelude.zip)".
  Extract Inlined Constant map => "(Prelude.map)".

  Example small_grammar := (result_grammar small_free small_goal small_start).
  Example small_upto10 := (result_terms_mapped small_free small_goal small_start 10). 

  Example big_grammar := (result_grammar big_free big_goal big_start).
  Example big_upto10 := (result_terms_mapped big_free big_goal big_start 10). 
End ExtractedLabyrinthHaskell.

Extraction Language Haskell.
Extraction "extracted/ExtractedLabyrinth.hs" ExtractedLabyrinthHaskell.
