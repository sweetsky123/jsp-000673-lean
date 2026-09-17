import JSP673

#print axioms JSP000673.exists_equal_degree_three_edge_path

/-- Restated as a typed `example`: on `2 * n + 1` vertices with minimum degree at least
`n + 2`, some two distinct vertices of equal degree are joined by a three-edge path. -/
example {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (n : ℕ) (hcard : Fintype.card V = 2 * n + 1) (hδ : ∀ v : V, n + 2 ≤ G.degree v) :
    ∃ u v x y : V, u ≠ v ∧ x ≠ u ∧ x ≠ y ∧ y ≠ v ∧ y ≠ u ∧ x ≠ v ∧
      G.degree u = G.degree v ∧ G.Adj u x ∧ G.Adj x y ∧ G.Adj y v :=
  JSP000673.exists_equal_degree_three_edge_path G n hcard hδ
