# Theorem 9.3.2 through single-conflict deletion

This companion proves the original strict nonlinear Chapter 9 theorem by the
procedure used in the manuscript. For a finite simple graph and a positive
number of colors, penalties c1 > 1 and c2 > 1 give the maximum k-colorable
subgraph value; every maximizing selection is feasible and has that value.
The complete Lean theorem type matches `Chapter09.Source.theorem_9_3_2`.

The source is the original thesis, Theorem 9.3.2 and its proof, printed pages
348–349 (original PDF pages 386–387). This software documentation summarizes the
argument; it does not reproduce publisher text or original PDF pages.

| Manuscript procedure | Lean checkpoint |
| --- | --- |
| Choose an active conflict in an allegedly infeasible maximizer. | `strict_optimizer_feasible_by_single_deletion` |
| Delete one occupied vertex/color slot. | `S.erase e.1` |
| Lose one reward unit, save a conflict penalty, introduce no new conflicts. | `score_erase_gain` |
| A conflict weight greater than one gives strict improvement, contradicting maximality. | `score_erase_strict` |
| A feasible maximizer has zero penalty and maximum feasible cardinality. | `nonlinear_optimizer_by_single_deletion` |
| Finite attainment supplies the value equality as well as the optimizer claim. | `theorem_9_3_2_from_text` |

The nonlinear objective counts ordered same-vertex color pairs. Its exact
unordered conflict weight is **2*c2**. The proof retains that factor and repairs
the arithmetic in printed equation (9.22). It does not certify the defective
linear slack update (9.11). The accepted simultaneous-cover proof remains
available; the companion does not depend on its conclusion or repair bounds.
The source Algorithm 12 sequential scan is a separate formalization.

## Build and check

Build the baseline library first, following the package README. Then, from
`lean-modern/`, run:

```sh
lake env lean --root=../companions/ch09-source-procedure -j2 -M4096 -DautoImplicit=false -o /tmp/Chapter09SourceProcedure.olean ../companions/ch09-source-procedure/Chapter09SourceProcedure.lean
LEAN_PATH="/tmp:$(lake env printenv LEAN_PATH)" lake env lean -j2 -M4096 ../companions/ch09-source-procedure/CheckSourceProcedure.lean
```

Use a fresh task-owned output directory in place of `/tmp` when builds may run
concurrently. These commands set Lean's heap/thread limits; they do not impose
an operating-system memory limit. The recorded check ran under an 8 GiB cgroup
with swap disabled and reused qualified baseline objects. It was not another
fresh full-library build.

The source prints transitive axioms for six proof targets. Only `propext`,
`Classical.choice` and `Quot.sound` occur. `CheckSourceProcedure.lean` checks the
complete theorem type and traverses Chapter09 project dependencies to exclude
the old theorem and simultaneous-repair route. Upstream proofs are covered by
the axiom report, not expanded by that project-only dependency traversal.

`build.json` binds the source and checker hashes to the separate compilation,
checks and independent source-first review. The frozen 599 baseline compiler
inputs, historical 595-module build and dependency map remain separate. This is
an alternative formal proof of an existing result, with explicit arithmetic
repair; it adds no new original theorem credit.

Project-owned proof code and accompanying software documentation use Apache-2.0.
