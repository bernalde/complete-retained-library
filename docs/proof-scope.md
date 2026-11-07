# Proof and review scope

The source library formalizes selected statements, assumptions, examples and
repairs associated with Chapters 1–10 and Appendix A. The published reader
provides the chapter context, correction comparisons and result-dependency map:
https://bernalde.github.io/thesis_ai_remake/

The snapshot preserves all 599 qualified compiler inputs byte for byte: 596
Lean modules and the toolchain, Lake configuration and dependency manifest.
The private migration qualification covers the complete 591-module baseline
and its additional compatibility and comparison modules. The historical proof
checks covered 595 safe modules. No new mathematical result or review is
claimed by copying those sources into this snapshot.

## Comparison challenge

`MkCSChallenge.lean` deliberately contains a proof placeholder for an independent
statement comparison. It is not a certified result, is not a default build
target and must not enter the import closure of the solution or proved
libraries. `MkCSStatement.lean` and `MkCSSolution.lean` use the shared Chapter 9
library. Successful compilation of the challenge alone would not prove its
placeholder. Exclude it from any proof-completeness or axiom report.

The snapshot identity checker checks local import closure and this isolation.
It does not replace the Lean compiler, statement comparison or a transitive
axiom check.

## Interpreting the formalization

Read the Lean hypotheses and conclusion for the exact result being used. An
algebraic witness, finite control example or conditional algorithm model has
its own scope. It does not automatically establish an unrestricted analytic
theorem, historical implementation behavior or solver performance. Historical
computational experiments were retained, not rerun during this preparation.

Accepted certificates exclude `sorryAx` and unproved research-specific axioms.
The standard logical foundations `propext`, `Classical.choice` and `Quot.sound`
are disclosed. Where a result uses an external computation or oracle, its
individual trust scope must also be consulted. A successful build by itself
does not establish those source correspondences or every trust claim.

The private audit contains the detailed source comparisons, reviews, build and
axiom receipts, and kernel-replay records. Those records are not included in
this public source payload. The public reader exposes selected scope summaries.
This snapshot supports examination and rebuilding of the formal source; it
does not make the complete private audit publicly reproducible.
