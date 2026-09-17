# JSP-000673 — equal-degree endpoints of a three-edge path (high minimum degree case)

Lean 4 / Mathlib formalization related to problem **JSP-000673** of the
[Justin Sun Prize problem bank](https://github.com/TheJustinSunPrize/awards),
posed by Erdős and Hajnal (1991):

> Must a dense graph of odd order have two equal-degree vertices joined by a
> three-edge path?

## Scope of this package

This package proves the **high minimum degree case only**, by a short
elementary argument:

**Theorem** (`JSP000673.exists_equal_degree_three_edge_path`). Let `n` be a
natural number and `G` a simple graph on `2 * n + 1` vertices in which every
vertex has degree at least `n + 2`. Then there exist four distinct vertices
`u, x, y, v` such that `u – x – y – v` is a path (three edges) and
`G.degree u = G.degree v`.

Two facts combine:

1. *Pigeonhole.* Every degree lies in the interval `[n + 2, 2 * n]` of
   `n - 1` values, while the graph has `2 * n + 1` vertices; hence two
   distinct vertices `u ≠ v` of equal degree exist.
2. *Path construction.* Given `u ≠ v` of equal degree and any neighbor `y` of
   `v` with `y ≠ u`, the sets `G.neighborFinset u ∩ G.neighborFinset y` and
   `G.neighborFinset v ∩ G.neighborFinset y` have sizes summing to at least
   `n + 2 ≥ 3`, so some `x ≠ v` is adjacent to both `u` and `y`, and
   `u – x – y – v` is a three-edge path with equal-degree endpoints.

The full problem was resolved by **Kaizhe Chen and Jie Ma**, *A problem of
Erdős and Hajnal on paths with equal-degree endpoints*
([arXiv:2503.19569](https://arxiv.org/abs/2503.19569)): for every `n ≥ 600`,
each graph on `2 * n + 1` vertices with at least `n ^ 2 + n + 1` edges
contains two distinct vertices of equal degree connected by a path of length
three, and this edge bound is sharp. The theorem above is an elementary
special case (a graph with minimum degree at least `n + 2` has more than
`n ^ 2 + n + 1` edges); it is proved here from first principles, independently
of the Chen–Ma argument. **The full Chen–Ma theorem is not claimed.**

No novelty on the mathematical side is claimed beyond the formalization
itself; no entitlement to an award is asserted. Submitted for intake and
eligibility review of the formalization component. Formalizer:
@sweetsky123 (identity confirmation pending).

## Contents

- `JSP673/Main.lean` — the theorem and its complete proof.
- `JSP673.lean` — root import file.
- `Audit.lean` — restates the theorem as a typed `example` against the
  library and prints its axiom dependencies:
  `propext`, `Classical.choice`, `Quot.sound` only (no `sorry`, no custom
  axioms, no `native_decide`).
- `verification.txt` — recorded local build and audit runs.
- `lakefile.toml`, `lake-manifest.json`, `lean-toolchain` — pinned
  toolchain `v4.33.1` and Mathlib revision `0df444a3`.

## Reproducing

```
lake env lean --version    # Lean (version 4.33.1, ...)
lake build                 # Build completed successfully (3015 jobs)
lake env lean Audit.lean   # axioms: [propext, Classical.choice, Quot.sound]
```

`lake build` fetches the pinned dependencies itself; an existing Mathlib
cache at the same revision is reused if present.
