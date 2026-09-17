/-
Copyright 2026 sweetsky123
Released under the MIT License.
-/
import Mathlib.Tactic
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Order.Interval.Finset.Nat

/-!
# JSP-000673 (high minimum degree case): equal degrees at the ends of a 3-edge path

This file formalizes a partial result toward problem **JSP-000673** of the
Justin Sun Prize problem bank:

> "Must a dense graph of odd order have two equal-degree vertices joined by a
> three-edge path?"

The problem was posed by Erdős and Hajnal in 1991.  The full statement was
resolved by [ChMa25] (arXiv:2503.19569): for every `n ≥ 600`, each graph on
`2 * n + 1` vertices with at least `n ^ 2 + n + 1` edges contains two distinct
vertices of equal degree connected by a path of length three, and the edge
bound is sharp (witnessed by the complete bipartite graph `K(n, n + 1)`).

Here we formalize the **high minimum degree case**, which has a short
elementary argument: on `2 * n + 1` vertices, minimum degree at least `n + 2`
already forces two equal-degree vertices joined by a path of length three.
Note that minimum degree `n + 2` forces at least `(2 * n + 1) * (n + 2) / 2`
edges, which is more than `n ^ 2 + n + 1` for `n ≥ 1`, so this is a genuine
partial result toward the (much harder) sharp statement of [ChMa25].

The argument, in full: degrees take at most `n - 1` distinct values between
`n + 2` and `2 * n`, while there are `2 * n + 1` vertices, so two distinct
vertices `u ≠ v` have equal degree.  Moreover any two distinct vertices are
joined by a path of length three: pick `y` adjacent to `v` with `y ≠ u`; then
`|N(u) ∩ N(y)| ≥ (n + 2) + (n + 2) - (2 * n + 1) = 3`, so some common neighbor
`x` of `u` and `y` differs from `v`, and `u – x – y – v` is a path.
-/

namespace JSP000673

open Finset

/-- **JSP-000673, high minimum degree case.** Every graph on `2 * n + 1`
vertices with minimum degree at least `n + 2` contains two distinct vertices
of equal degree that are connected by a path of length three; the four
vertices `u, x, y, v` below are pairwise distinct and the edges `u–x`, `x–y`,
`y–v` are present. -/
theorem exists_equal_degree_three_edge_path {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (n : ℕ) (hcard : Fintype.card V = 2 * n + 1)
    (hδ : ∀ v : V, n + 2 ≤ G.degree v) :
    ∃ u v x y : V, u ≠ v ∧ x ≠ u ∧ x ≠ y ∧ y ≠ v ∧ y ≠ u ∧ x ≠ v ∧
      G.degree u = G.degree v ∧ G.Adj u x ∧ G.Adj x y ∧ G.Adj y v := by
  -- Every degree is at most `2 * n` (a vertex is not its own neighbor).
  have hdeg_le : ∀ v : V, G.degree v ≤ 2 * n := by
    intro v
    have hdg := G.card_neighborFinset_eq_degree v
    have hsub : G.neighborFinset v ⊆ (Finset.univ.erase v) := by
      intro w hw
      rw [mem_erase]
      exact ⟨fun h => absurd (h ▸ hw) (G.notMem_neighborFinset_self v), mem_univ w⟩
    have h1 := (G.neighborFinset v).card_le_card hsub
    rw [Finset.card_erase_of_mem (Finset.mem_univ v), Finset.card_univ, hcard] at h1
    omega
  -- Pigeonhole: two distinct vertices of equal degree.
  obtain ⟨u, _, v, _, huv, hdeg⟩ := Finset.exists_ne_map_eq_of_card_lt_of_maps_to
    (s := (Finset.univ : Finset V)) (t := Finset.Ico (n + 2) (2 * n + 1))
    (by rw [Nat.card_Ico, Finset.card_univ, hcard]; omega)
    (fun w _ => mem_Ico.2 ⟨hδ w, by have := hdeg_le w; omega⟩)
  -- Choose `y` adjacent to `v` with `y ≠ u`.
  obtain ⟨y, hy, hyu⟩ : ∃ y : V, G.Adj v y ∧ y ≠ u := by
    by_contra hcon
    push Not at hcon
    have hsub2 : G.neighborFinset v ⊆ {u} := by
      intro w hw
      simp only [mem_singleton]
      exact hcon w ((G.mem_neighborFinset v w).1 hw)
    have h2 : (G.neighborFinset v).card ≤ 1 := by
      simpa using Finset.card_le_card hsub2
    rw [G.card_neighborFinset_eq_degree v] at h2
    have h3 := hδ v
    omega
  -- The common neighborhood of `u` and `y` has at least `3` elements.
  have h6 : 3 ≤ (G.neighborFinset u ∩ G.neighborFinset y).card := by
    have hadd := Finset.card_union_add_card_inter (G.neighborFinset u) (G.neighborFinset y)
    have hunion : (G.neighborFinset u ∪ G.neighborFinset y).card ≤ 2 * n + 1 := by
      have h5 := (G.neighborFinset u ∪ G.neighborFinset y).card_le_card
        (Finset.subset_univ _)
      simpa [Finset.card_univ, hcard] using h5
    rw [G.card_neighborFinset_eq_degree u, G.card_neighborFinset_eq_degree y] at hadd
    have huδ := hδ u
    have hyδ := hδ y
    omega
  -- Choose `x`, a common neighbor of `u` and `y` with `x ≠ v`.
  obtain ⟨x, hx, hxv⟩ : ∃ x ∈ G.neighborFinset u ∩ G.neighborFinset y, x ≠ v := by
    by_contra hcon
    push Not at hcon
    have hsub3 : G.neighborFinset u ∩ G.neighborFinset y ⊆ {v} := by
      intro w hw
      simp only [mem_singleton]
      exact hcon w hw
    have h7 : (G.neighborFinset u ∩ G.neighborFinset y).card ≤ 1 := by
      simpa using Finset.card_le_card hsub3
    omega
  -- Assemble the path `u – x – y – v`.
  have hux : G.Adj u x := (G.mem_neighborFinset u x).1 (mem_inter.1 hx).1
  have hxy : G.Adj x y := ((G.mem_neighborFinset y x).1 (mem_inter.1 hx).2).symm
  have hyv : G.Adj y v := hy.symm
  exact ⟨u, v, x, y, huv, hux.ne', hxy.ne, hyv.ne, hyu, hxv, hdeg, hux, hxy, hyv⟩

end JSP000673
