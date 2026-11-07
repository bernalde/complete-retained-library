module

public import Chapter02OAHistory
public import Mathlib.Data.Set.Finite.Lemmas

@[expose] public section

/-! The static finite attained-fiber window used in Chapter4's finite-attainment
argument, with exact fixed-NLP polishing. The objective is the model's actual
c1·x+c2·y. No uniqueness of integer fibers or continuous optimizers is asserted.
This module gives no cutting-plane history, radius or algorithm theorem. -/

noncomputable section
namespace Chapter04.CenterCut
open Chapter02

/-- A positive window separates the fixed global value from every strictly
suboptimal attained integer-fiber value. Only nonempty feasible fibers receive
a selected optimizer; the conclusion covers every actual optimizer. -/
theorem source_attained_fiber_value_gap {n m l k : ℕ}
    (d : ModelData n m l k)
    (hg : ∀ j, Continuous (d.g j))
    (hcompact : IsCompact (d.linearRegion ∩ IntegerCylinder (n := n) d.lo d.hi))
    (pStar : Point n m)
    (hmin : IsMinimizer (d.feasibleOn Set.univ) d.objective pStar) :
    ∃ ε : ℝ, 0 < ε ∧
      ∀ y ∈ IntegerBox d.lo d.hi, ∀ p : Point n m,
        IsMinimizer (d.fixedNonlinearFiber (oaIntCast y)) d.objective p →
        d.objective p = d.objective pStar ∨
          d.objective pStar + ε < d.objective p := by
  classical
  let T : Set (IntVector m) :=
    {y | y ∈ IntegerBox d.lo d.hi ∧ (d.fixedNonlinearFiber (oaIntCast y)).Nonempty}
  have hTfinite : T.Finite := (integerBox_finite d.lo d.hi).subset (fun _ hy => hy.1)
  letI : Finite T := hTfinite.to_subtype
  have hattained : ∀ y : T, ∃ p,
      IsMinimizer (d.fixedNonlinearFiber (oaIntCast y.1)) d.objective p := by
    intro y
    exact source_fixedNLP_minimum_attained d y.1 y.2.1 hcompact y.2.2 hg
  choose point hpoint using hattained
  have hfeasible : ∀ y ∈ IntegerBox d.lo d.hi, ∀ p : Point n m,
      p ∈ d.fixedNonlinearFiber (oaIntCast y) → p ∈ d.feasibleOn Set.univ := by
    intro y hy p hp
    obtain ⟨hpL, hpY, hpG⟩ := (mem_fixedNonlinearFiber d _ _).mp hp
    exact (source_feasible_iff d Set.univ p).mpr
      ⟨Set.mem_univ _, hpG, hpL, y, hy, hpY⟩
  have hvalue : ∀ y : T, ∀ p : Point n m,
      IsMinimizer (d.fixedNonlinearFiber (oaIntCast y.1)) d.objective p →
      d.objective p = d.objective (point y) := by
    intro y p hp
    exact le_antisymm (hp.2 _ (hpoint y).1) ((hpoint y).2 _ hp.1)
  let B : Set T := {y | d.objective pStar < d.objective (point y)}
  by_cases hB : B.Nonempty
  · obtain ⟨y0, hy0, hleast⟩ :=
      Set.exists_min_image B (fun y => d.objective (point y)) (Set.toFinite B) hB
    change d.objective pStar < d.objective (point y0) at hy0
    refine ⟨(d.objective (point y0) - d.objective pStar) / 2, by linarith, ?_⟩
    intro y hy p hp
    let yt : T := ⟨y, hy, p, hp.1⟩
    have hpval : d.objective p = d.objective (point yt) := hvalue yt p hp
    have hlo : d.objective pStar ≤ d.objective p := hmin.2 p (hfeasible y hy p hp.1)
    by_cases heq : d.objective p = d.objective pStar
    · exact Or.inl heq
    · right
      have hgt : d.objective pStar < d.objective p := lt_of_le_of_ne hlo (Ne.symm heq)
      have hyt : yt ∈ B := by
        change d.objective pStar < d.objective (point yt)
        rw [← hpval]
        exact hgt
      have hbound := hleast yt hyt
      linarith
  · refine ⟨1, zero_lt_one, ?_⟩
    intro y hy p hp
    left
    by_contra heq
    let yt : T := ⟨y, hy, p, hp.1⟩
    have hpval : d.objective p = d.objective (point yt) := hvalue yt p hp
    have hlo : d.objective pStar ≤ d.objective p := hmin.2 p (hfeasible y hy p hp.1)
    have hgt : d.objective pStar < d.objective p := lt_of_le_of_ne hlo (Ne.symm heq)
    apply hB
    refine ⟨yt, ?_⟩
    change d.objective pStar < d.objective (point yt)
    rw [← hpval]
    exact hgt

/-- Every original feasible point in one closed near-optimal objective window
has an attained fixed-NLP minimum, and every exact optimizer of that fiber is
globally optimal. The original point itself need not be optimal. -/
theorem source_near_optimal_fiber_polishing {n m l k : ℕ}
    (d : ModelData n m l k)
    (hg : ∀ j, Continuous (d.g j))
    (hcompact : IsCompact (d.linearRegion ∩ IntegerCylinder (n := n) d.lo d.hi))
    (pStar : Point n m)
    (hmin : IsMinimizer (d.feasibleOn Set.univ) d.objective pStar) :
    ∃ ε : ℝ, 0 < ε ∧
      ∀ q : Point n m, q ∈ d.feasibleOn Set.univ →
        d.objective q ≤ d.objective pStar + ε →
        (∃ p : Point n m, IsMinimizer (d.fixedNonlinearFiber q.2) d.objective p) ∧
        ∀ p : Point n m, IsMinimizer (d.fixedNonlinearFiber q.2) d.objective p →
          IsMinimizer (d.feasibleOn Set.univ) d.objective p ∧
          d.objective p = d.objective pStar := by
  obtain ⟨ε, hε, hgap⟩ := source_attained_fiber_value_gap d hg hcompact pStar hmin
  refine ⟨ε, hε, ?_⟩
  intro q hq hnear
  obtain ⟨_, hqG, hqL, y, hy, hqY⟩ := (source_feasible_iff d Set.univ q).mp hq
  have hqY' : q.2 = oaIntCast y := hqY
  have hqFiber : q ∈ d.fixedNonlinearFiber (oaIntCast y) :=
    (mem_fixedNonlinearFiber d _ _).mpr ⟨hqL, hqY', hqG⟩
  constructor
  · obtain ⟨p, hp⟩ := source_fixedNLP_minimum_attained d y hy hcompact ⟨q, hqFiber⟩ hg
    refine ⟨p, ?_⟩
    rw [hqY']
    exact hp
  · intro p hp
    have hpFiber : IsMinimizer (d.fixedNonlinearFiber (oaIntCast y)) d.objective p := by
      simpa only [hqY', oaIntCast] using hp
    have hpq : d.objective p ≤ d.objective q := hpFiber.2 q hqFiber
    have heq : d.objective p = d.objective pStar := by
      rcases hgap y hy p hpFiber with h | h
      · exact h
      · exact False.elim (not_lt_of_ge (hpq.trans hnear) h)
    obtain ⟨hpL, hpY, hpG⟩ := (mem_fixedNonlinearFiber d _ _).mp hpFiber.1
    have hpFeasible : p ∈ d.feasibleOn Set.univ :=
      (source_feasible_iff d Set.univ p).mpr
        ⟨Set.mem_univ _, hpG, hpL, y, hy, hpY⟩
    refine ⟨⟨hpFeasible, ?_⟩, heq⟩
    intro w hw
    rw [heq]
    exact hmin.2 w hw

end Chapter04.CenterCut
