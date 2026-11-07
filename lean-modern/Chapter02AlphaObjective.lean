module

public import Chapter02

@[expose] public section

/-! Exact equal-height objective optimality under an explicit safe height floor. -/
noncomputable section
namespace Chapter02

/-- The full reduced pair set: original feasibility, nonlinear objective cutoff,
safe lower height bound, upper height bound, and every same-level objective cut.
The new height is real. No epigraph inequality `f p ≤ μ` is inserted. -/
def alphaObjectiveHeightSet
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {I : Type*}
    (S : Set E) (f : E → ℝ) (G : E → E →L[ℝ] ℝ)
    (a : I → E) (b v : ℝ) : Set (E × ℝ) :=
  {z | z.1 ∈ S ∧ f z.1 ≤ v ∧ b ≤ z.2 ∧ z.2 ≤ v ∧
    ∀ i, v + G (a i) (z.1 - a i) ≤ z.2}

/-- A qualified exact interpretation of WP2002's printed271 equal-height
theorem (Eqs42–46), with explicit ambient derivatives and safe height floor.
The proof constructs a simultaneous lower-height lift for every improving
point. It uses the strict all-pairs law at all finite same-level anchors;
differentiability scopes G as the actual derivative rather than supplying a
global support inequality. Attainment of the full reduced minimum is assumed,
not inferred from compactness, a solver status, or a feasible-only solve. -/
theorem alpha_objective_equal_height_optimal
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {I : Type*} [Fintype I] [Nonempty I]
    (U S : Set E) (f : E → ℝ) (G : E → E →L[ℝ] ℝ)
    (a : I → E) (b v : ℝ) (q : E)
    (hSU : S ⊆ U) (hanchors : ∀ i, a i ∈ U)
    (_hderiv : ∀ x ∈ U, HasFDerivAt f (G x) x)
    (hpseudo : ∀ x ∈ U, ∀ y ∈ U, f y < f x → G x (y - x) < 0)
    (hlevel : ∀ i, f (a i) = v)
    (hfloor : ∀ p ∈ S, b ≤ f p)
    (hmin : IsMinimizer (alphaObjectiveHeightSet S f G a b v) Prod.snd (q, v)) :
    f q = v ∧ IsMinimizer S f q := by
  classical
  have hbound : ∀ p ∈ S, v ≤ f p := by
    intro p hp
    by_contra! himprove
    let H : I → ℝ := fun i => v + G (a i) (p - a i)
    have hH : ∀ i, H i < v := by
      intro i
      have hnegative := hpseudo (a i) (hanchors i) p (hSU hp)
        (by simpa only [hlevel i] using himprove)
      dsimp [H]
      linarith
    let m : ℝ := Finset.univ.sup' Finset.univ_nonempty H
    have hm : m < v := by
      exact (Finset.sup'_lt_iff Finset.univ_nonempty).2 (fun i _ => hH i)
    let t : ℝ := max b m
    have ht : t < v := max_lt ((hfloor p hp).trans_lt himprove) hm
    have hlift : (p, t) ∈ alphaObjectiveHeightSet S f G a b v := by
      refine ⟨hp, himprove.le, le_max_left b m, ht.le, ?_⟩
      intro i
      exact (Finset.le_sup' H (Finset.mem_univ i)).trans (le_max_right b m)
    exact (not_le_of_gt ht) (hmin.2 (p, t) hlift)
  have hq : q ∈ S := hmin.1.1
  have hvalue : f q = v := le_antisymm hmin.1.2.1 (hbound q hq)
  exact ⟨hvalue, hq, fun p hp => hvalue.symm ▸ hbound p hp⟩

#print axioms alpha_objective_equal_height_optimal

end Chapter02
