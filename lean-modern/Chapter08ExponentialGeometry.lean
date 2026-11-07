module

public import Chapter08
public import Mathlib.Analysis.Convex.Basic
public import Mathlib.Topology.MetricSpace.Pseudo.Constructions

@[expose] public section

noncomputable section
namespace Chapter08.Exponential

/-- Coordinates are (epigraph height, perspective scale, exponential argument). -/
abbrev Space := ℝ × ℝ × ℝ

def cone : Set Space := {q | ExpCone q.1 q.2.1 q.2.2}

def positive : Set Space :=
  {q | 0 < q.2.1 ∧ q.2.1 * Real.exp (q.2.2 / q.2.1) ≤ q.1}

theorem exp_tangent (a z : ℝ) :
    Real.exp a * (1 + z - a) ≤ Real.exp z := by
  calc
    Real.exp a * (1 + z - a) = Real.exp a * ((z-a)+1) := by ring
    _ ≤ Real.exp a * Real.exp (z-a) :=
      mul_le_mul_of_nonneg_left (Real.add_one_le_exp (z-a)) (Real.exp_pos a).le
    _ = Real.exp z := by rw [← Real.exp_add]; congr 1; ring

/-- The closed predicate is exactly an intersection of affine halfspaces. -/
theorem halfspace_iff (u v w : ℝ) :
    ExpCone u v w ↔ 0 ≤ u ∧ 0 ≤ v ∧
      ∀ a : ℝ, Real.exp a * (w + (1-a)*v) ≤ u := by
  constructor
  · rintro (⟨hv, h⟩ | ⟨rfl, hu, hw⟩)
    · refine ⟨le_trans (mul_nonneg hv.le (Real.exp_pos _).le) h, hv.le, ?_⟩
      intro a
      calc
        Real.exp a * (w+(1-a)*v) = v*(Real.exp a*(1+w/v-a)) := by
          field_simp; ring
        _ ≤ v * Real.exp (w/v) := mul_le_mul_of_nonneg_left (exp_tangent a _) hv.le
        _ ≤ u := h
    · refine ⟨hu, le_rfl, ?_⟩
      intro a
      simpa using le_trans (mul_nonpos_of_nonneg_of_nonpos (Real.exp_pos a).le hw) hu
  · rintro ⟨hu, hv, h⟩
    rcases eq_or_lt_of_le hv with hz | hp
    · have vz : v = 0 := hz.symm
      subst v
      refine Or.inr ⟨rfl, hu, ?_⟩
      by_contra hn
      have hw : 0 < w := lt_of_not_ge hn
      have hh := h (Real.log ((u+1)/w))
      have hq : 0 < (u+1)/w := div_pos (by linarith) hw
      rw [Real.exp_log hq] at hh
      have he : (u+1)/w * (w+(1-Real.log ((u+1)/w))*0) = u+1 := by
        field_simp <;> ring
      rw [he] at hh
      linarith
    · refine Or.inl ⟨hp, ?_⟩
      have hh := h (w/v)
      have he : Real.exp (w/v)*(w+(1-w/v)*v) = v*Real.exp (w/v) := by
        field_simp; ring
      rwa [he] at hh

theorem cone_convex : Convex ℝ cone := by
  intro x hx y hy a b ha hb hab
  obtain ⟨hxu, hxv, hxh⟩ := (halfspace_iff _ _ _).mp hx
  obtain ⟨hyu, hyv, hyh⟩ := (halfspace_iff _ _ _).mp hy
  change ExpCone (a*x.1+b*y.1) (a*x.2.1+b*y.2.1) (a*x.2.2+b*y.2.2)
  apply (halfspace_iff _ _ _).mpr
  refine ⟨add_nonneg (mul_nonneg ha hxu) (mul_nonneg hb hyu),
    add_nonneg (mul_nonneg ha hxv) (mul_nonneg hb hyv), ?_⟩
  intro c
  calc
    Real.exp c * (a*x.2.2+b*y.2.2+(1-c)*(a*x.2.1+b*y.2.1)) =
      a*(Real.exp c*(x.2.2+(1-c)*x.2.1)) +
      b*(Real.exp c*(y.2.2+(1-c)*y.2.1)) := by ring
    _ ≤ a*x.1+b*y.1 := add_le_add
      (mul_le_mul_of_nonneg_left (hxh c) ha)
      (mul_le_mul_of_nonneg_left (hyh c) hb)

theorem cone_closed : IsClosed cone := by
  have he : cone = {q : Space | 0 ≤ q.1} ∩ {q : Space | 0 ≤ q.2.1} ∩
      ⋂ a : ℝ, {q : Space | Real.exp a * (q.2.2+(1-a)*q.2.1) ≤ q.1} := by
    ext q
    simp only [cone, Set.mem_setOf_eq, Set.mem_inter_iff, Set.mem_iInter]
    exact (halfspace_iff _ _ _).trans and_assoc.symm
  rw [he]
  refine ((isClosed_le continuous_const continuous_fst).inter
    (isClosed_le continuous_const (continuous_fst.comp continuous_snd))).inter ?_
  apply isClosed_iInter
  intro a
  exact isClosed_le
    (continuous_const.mul ((continuous_snd.comp continuous_snd).add
      (continuous_const.mul (continuous_fst.comp continuous_snd)))) continuous_fst

theorem zero_approximation (u w δ : ℝ) (hu : 0 ≤ u) (hw : w ≤ 0) (hδ : 0 < δ) :
    (u+δ, δ, w) ∈ positive := by
  refine ⟨hδ, ?_⟩
  have he : Real.exp (w/δ) ≤ 1 := by
    rw [← Real.exp_zero]
    exact Real.exp_le_exp.mpr (div_nonpos_of_nonpos_of_nonneg hw hδ.le)
  calc
    δ * Real.exp (w/δ) ≤ δ*1 := mul_le_mul_of_nonneg_left he hδ.le
    _ ≤ u+δ := by linarith

/-- Positive scales are dense in precisely the accepted closed exponential cone. -/
theorem closure_positive : closure positive = cone := by
  apply Set.Subset.antisymm
  · apply closure_minimal
    · intro q hq
      exact Or.inl hq
    · exact cone_closed
  · rintro ⟨u,v,w⟩ (⟨hv,h⟩ | ⟨rfl,hu,hw⟩)
    · exact subset_closure ⟨hv,h⟩
    · apply Metric.mem_closure_iff.mpr
      intro ε hε
      have hδ : 0 < ε/2 := by linarith
      refine ⟨(u+ε/2, ε/2, w), zero_approximation u w (ε/2) hu hw hδ, ?_⟩
      have hd : dist (u, (0:ℝ), w) (u+ε/2, ε/2, w) = ε/2 := by
        simp [Prod.dist_eq, Real.dist_eq, abs_of_nonneg hδ.le, abs_of_pos hε,
          show u-(u+ε/2) = -(ε/2) by ring, max_eq_left hδ.le]
      rw [hd]
      linarith

end Chapter08.Exponential
