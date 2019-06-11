Testing Haskell:

ghci ExtractedLabyrinth.hs
:force small_grammar
:force small_upto10

or for the benchmark (warning: this takes a long time!)
:force big_grammar
:force big_upto10

Testing OCaml:
with Coq 8.8 you need to patch line

1503       (Obj.magic mixin_base (assert false (* Proj Args *)) c.mixin) }
to
1503       (Obj.magic mixin_base (assert true (* Proj Args *)) c.mixin) }

this is a known bug in the Coq extraction plugin

https://github.com/coq/coq/issues/7348

After the patch you can run
ocaml
#use "ExtractedLabyrinth.ml"
ExtractedLabyrinthOCaml.small_grammar;;

or for the benchmark (warning: this takes a long time!)

ExtractedLabyrinthOCaml.big_grammar();;

Unfortunately, the result lists are not displayed by the interpreter, so all there is to see is [<poly>; ...].
In future, a to string function should be implemented.


