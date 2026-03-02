# eqwalizer

This is a type-checker for Erlang implemented in Scala. It's part of bigger project - ELP (Erlang language Platform).
Parsing and error report is orchestrated by ELP - and is communicated via ICP (in ELPProxy.scala).

The main modules needed for the current work:

- Subtype.scala - subtyping
- Constraints.scala - constraint generation and solving in spirit of Local Type Inference (Pierce and Turner)
- ElabApply.scala - elaboration of function applications (with probably forall's), which uses constraint inference.
