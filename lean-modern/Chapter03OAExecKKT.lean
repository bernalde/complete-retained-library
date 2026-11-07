module

public import Chapter03OAExecHistory

@[expose] public section

/-! A retained feasible certificate bounds the whole master, not just its
own fiber. Finite integer bounds then rule out an unbounded height objective.
No joint initializer KKT, compact continuous master, or progress assumption. -/
noncomputable section
open scoped BigOperators
open Chapter02 Chapter03.OAKKT
namespace Chapter03.OAExec
variable {n m l r k : ℕ}

def fullKKTFunctional {d : ModelData n m l r} {f : Point n m → ℝ}
    {x : RealVector n} {y : RealVector m} (K : FixedKKT d f x y) :
    Point n m →L[ℝ] ℝ :=
  K.Df + (∑ j, K.lambda j • K.Dg j) +
    ∑ i, K.mu i • linearFormCLM (d.A i) (d.B i)

theorem fullKKTFunctional_continuous_zero {d : ModelData n m l r}
    {f : Point n m → ℝ} {x : RealVector n} {y : RealVector m}
    (K : FixedKKT d f x y) (v : RealVector n) : fullKKTFunctional K (v,0) = 0 := by
  have hh := congrArg (fun D : RealVector n →L[ℝ] ℝ => D v) K.stationarity
  simpa only [fullKKTFunctional,ContinuousLinearMap.add_apply,
    ContinuousLinearMap.sum_apply,ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.zero_apply,restrict_apply,fiberLinearRow_apply,
    linearFormCLM_apply] using hh

theorem fullKKTFunctional_y {d : ModelData n m l r}
    {f : Point n m → ℝ} {x : RealVector n} {y : RealVector m}
    (K : FixedKKT d f x y) (q : Point n m) :
    fullKKTFunctional K (q-(x,y)) = fullKKTFunctional K (0,q.2-y) := by
  have he : q-(x,y) = (q.1-x,0)+(0,q.2-y) := by ext <;> simp
  rw [he,map_add,fullKKTFunctional_continuous_zero,zero_add]

theorem hard_full_tangent (d : ModelData n m l r) (i : Fin r)
    (a q : Point n m) :
    linearResidual d i a + linearFormCLM (d.A i) (d.B i) (q-a) =
      linearResidual d i q := by
  rw [map_sub]
  simp only [linearFormCLM_apply,linearResidual]
  ring

theorem history_cross_lower {d : ModelData n m l r} {f : Point n m → ℝ}
    {N : Set (Fin l)} {c : TangentFamily n m l k}
    {df : Fin k → Point n m →L[ℝ] ℝ} {x : RealVector n} {y : RealVector m}
    (H : History d f N c df x y) (K : FixedKKT d f x y)
    {z : Point n m × ℝ} (hz : z ∈ Chapter06.EpigraphMaster d f c df Set.univ) :
    f (x,y) + fullKKTFunctional K (0,z.1.2-y) ≤ z.2 := by
  have hsoft : (∑ j, K.lambda j * K.Dg j (z.1-(x,y))) ≤ 0 := by
    apply Finset.sum_nonpos
    intro j _
    by_cases hj : K.lambda j = 0
    · simp [hj]
    · have ht := H.supported_tangent K.Dg K.derivative_g hz.1 j
        (le_of_eq (K.supported_residual j hj).symm)
      have hw := mul_le_mul_of_nonneg_left ht (K.lambda_nonneg j)
      have hc := K.soft_compl j
      change K.lambda j * d.g j (x,y) = 0 at hc
      nlinarith
  have hhard : (∑ i, K.mu i * linearFormCLM (d.A i) (d.B i) (z.1-(x,y))) ≤ 0 := by
    apply Finset.sum_nonpos
    intro i _
    have ht := hard_full_tangent d i (x,y) z.1
    have hq : linearResidual d i z.1 ≤ 0 := sub_nonpos.mpr (hz.1.1.2 i)
    have hw := mul_le_mul_of_nonneg_left hq (K.mu_nonneg i)
    have hc := K.hard_compl i
    change K.mu i * linearResidual d i (x,y) = 0 at hc
    rw [← ht] at hw
    nlinarith
  have ho := H.objective_tangent K.Df K.derivative_f hz
  rw [← fullKKTFunctional_y K z.1]
  simp only [fullKKTFunctional,ContinuousLinearMap.add_apply,
    ContinuousLinearMap.sum_apply,ContinuousLinearMap.smul_apply,smul_eq_mul]
  linarith

theorem event_cross_lower {d : Data n m l r} (a : Analytic d)
    {seed : Point n m} {H : List (Event d)} (hH : ValidHistory d seed H)
    {e : Event d} (he : e ∈ H) (K : FixedKKT d.model d.f e.x (intCast e.target))
    {z : Point n m × ℝ} (hz : z ∈ master d seed H) :
    d.f e.anchor + fullKKTFunctional K (0,z.1.2-intCast e.target) ≤ z.2 := by
  obtain ⟨i,rfl⟩ := List.mem_iff_get.mp he
  exact history_cross_lower (eventHistory d a seed H hH i) K hz.1

theorem event_master_bddBelow {d : Data n m l r} (a : Analytic d)
    {seed : Point n m} {H : List (Event d)} (hH : ValidHistory d seed H)
    {e : Event d} (he : e ∈ H) (hn : e.restoration = none) :
    BddBelow (Prod.snd '' master d seed H) := by
  obtain ⟨K⟩ := event_fixed_kkt (hH.2 e he) hn
  let value : IntVector m → ℝ := fun y =>
    d.f e.anchor + fullKKTFunctional K (0,intCast y-intCast e.target)
  obtain ⟨b,hb⟩ := ((integerBox_finite d.model.lo d.model.hi).image value).bddBelow
  refine ⟨b,?_⟩
  rintro z ⟨q,hq,rfl⟩
  obtain ⟨y,hy,hqy⟩ := master_integer hq
  have hlo : b ≤ value y := hb ⟨y,hy,rfl⟩
  have hhi := event_cross_lower a hH he K hq
  rw [hqy] at hhi
  exact hlo.trans hhi

theorem unbounded_no_feasible_event {d : Data n m l r} (a : Analytic d)
    {seed : Point n m} {H : List (Event d)} (hH : ValidHistory d seed H)
    (hu : ¬ BddBelow (Prod.snd '' master d seed H)) :
    ∀ e ∈ H, e.restoration ≠ none := by
  intro e he hn
  exact hu (event_master_bddBelow a hH he hn)

end Chapter03.OAExec

#print axioms Chapter03.OAExec.history_cross_lower
#print axioms Chapter03.OAExec.event_master_bddBelow
