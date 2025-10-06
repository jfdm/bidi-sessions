# Sessions Typed Bidirectionally

A look at typing multiparty sessions using multiparty session types and bidirectional typing.

This work originated from Capable, developed as part of the DSbD AppControl project.

This work provides/will provide proof that the ideas of bidirectionally typed multiparty sessions are sound and complete.


A constant work in progress.....

## Status

+ [X] Soundness
  + [X] Subtyping local types
  + [X] Full merge for synthesis
  + [X] Full merge for projection
  + [X] Elaboration of an AST to terms

+ [ ] Completeness

  + [X] Subtyping local types
  + [X] Full merge for synthesis
  + [X] Full merge for projection

  + [ ] Elaboration of an AST to terms
    Most of the issues with completeness for elaboration come with evidence that certain error cases *will* provide void.
    The issue is not with the theory but demonstrating to the compiler that we can find void when dealing with computations that arise when discharging proof obligations...

    + [X] Synthesis of local types from terms describing local types is unique
    + [X] When annotations fail we get void
    + [ ] When subsets fails we get void
    + [ ] When merging fails we get void
