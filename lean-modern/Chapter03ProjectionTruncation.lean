module

public import Chapter03

@[expose] public section

/-! Exact real-arithmetic conditional control for coordinate dropping in the
recovered projection-cut constructor. This does not model C floating arithmetic,
solver statuses, reachability in a complete historical run, or performance.
The compensation theorem is a separately proposed mathematical repair. -/
noncomputable section
open scoped BigOperators InnerProductSpace
namespace Chapter03.ProjectionTruncation

section Compensation
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def fullRow (d p y : ι → ℝ) : ℝ := ∑ i, d i * (y i - p i)
def retainedRow (D : Finset ι) (d p y : ι → ℝ) : ℝ :=
  ∑ i ∈ Dᶜ, d i * (y i - p i)
def omittedRow (D : Finset ι) (d p y : ι → ℝ) : ℝ :=
  ∑ i ∈ D, d i * (y i - p i)
def compensation (D : Finset ι) (d p lo hi : ι → ℝ) : ℝ :=
  ∑ i ∈ D, max (d i * (lo i - p i)) (d i * (hi i - p i))

theorem row_decomposition (D : Finset ι) (d p y : ι → ℝ) :
    fullRow d p y = retainedRow D d p y + omittedRow D d p y := by
  simpa [fullRow, retainedRow, omittedRow, add_comm] using
    (Finset.sum_add_sum_compl D (fun i => d i * (y i - p i))).symm

theorem coordinate_contribution_bound (d p lo hi y : ℝ)
    (hlo : lo ≤ y) (hhi : y ≤ hi) :
    d * (y - p) ≤ max (d * (lo - p)) (d * (hi - p)) := by
  by_cases hd : 0 ≤ d
  · exact (mul_le_mul_of_nonneg_left (sub_le_sub_right hhi p) hd).trans
      (le_max_right _ _)
  · exact (mul_le_mul_of_nonpos_left (sub_le_sub_right hlo p) (le_of_not_ge hd)).trans
      (le_max_left _ _)

omit [Fintype ι] [DecidableEq ι] in
theorem omitted_contribution_bound (D : Finset ι) (d p lo hi y : ι → ℝ)
    (hbox : ∀ i ∈ D, lo i ≤ y i ∧ y i ≤ hi i) :
    omittedRow D d p y ≤ compensation D d p lo hi := by
  apply Finset.sum_le_sum
  intro i hiD
  exact coordinate_contribution_bound _ _ _ _ _ (hbox i hiD).1 (hbox i hiD).2

/-- Full-cut validity plus valid bounds on all omitted coordinates suffices.
There is no target-exclusion assertion in this statement. -/
theorem bounded_coordinate_compensation_valid (D : Finset ι)
    (d p lo hi y : ι → ℝ) (hfull : 0 ≤ fullRow d p y)
    (hbox : ∀ i ∈ D, lo i ≤ y i ∧ y i ≤ hi i) :
    -compensation D d p lo hi ≤ retainedRow D d p y := by
  have hsplit := row_decomposition D d p y
  have hbound := omitted_contribution_bound D d p lo hi y hbox
  linarith

end Compensation

abbrev E := EuclideanSpace ℝ (Fin 2)
def vec (a b : ℝ) : E := (WithLp.linearEquiv 2 ℝ (Fin 2 → ℝ)).symm ![a,b]
def u : E := 0
def p : E := vec (1/2147483648) (1/8192)
def q : E := vec 33 0
def K : Set E := {y | 0 ≤ y 0 ∧ y 0 ≤ 33 ∧ 0 ≤ y 1 ∧ y 1 ≤ 1 ∧
  ⟪p,p⟫_ℝ ≤ ⟪p,y⟫_ℝ}
def dropped : Finset (Fin 2) := {0}
def lo : Fin 2 → ℝ := fun _ => 0
def hi : Fin 2 → ℝ := ![33,1]

theorem inner_coordinates (x y : E) :
    ⟪x,y⟫_ℝ = x 0 * y 0 + x 1 * y 1 := by
  simp [PiLp.inner_apply, Fin.sum_univ_two, mul_comm]

theorem norm_squared_coordinates (x : E) : ‖x‖^2 = (x 0)^2 + (x 1)^2 := by
  rw [← real_inner_self_eq_norm_sq, inner_coordinates]
  ring

theorem p_dyadic : p 0 = 1/(2:ℝ)^31 ∧ p 1 = 1/(2:ℝ)^13 := by
  norm_num [p,vec]

theorem p_mem : p ∈ K := by
  norm_num [K,p,vec]

theorem K_convex : Convex ℝ K := by
  intro x hx y hy a b ha hb hab
  rcases hx with ⟨hx0,hx33,hx1,hy1,hxp⟩
  rcases hy with ⟨hy0,hy33,hyone,hyone',hyp⟩
  change 0 ≤ a*x 0+b*y 0 ∧ a*x 0+b*y 0 ≤ 33 ∧
    0 ≤ a*x 1+b*y 1 ∧ a*x 1+b*y 1 ≤ 1 ∧ _
  refine ⟨add_nonneg (mul_nonneg ha hx0) (mul_nonneg hb hy0),?_,
    add_nonneg (mul_nonneg ha hx1) (mul_nonneg hb hyone),?_,?_⟩
  · nlinarith [mul_le_mul_of_nonneg_left hx33 ha,mul_le_mul_of_nonneg_left hy33 hb]
  · nlinarith [mul_le_mul_of_nonneg_left hy1 ha,mul_le_mul_of_nonneg_left hyone' hb]
  · simp only [inner_add_right,inner_smul_right]
    have he : a*⟪p,p⟫_ℝ+b*⟪p,p⟫_ℝ = ⟪p,p⟫_ℝ := by
      rw [← add_mul,hab,one_mul]
    linarith [mul_le_mul_of_nonneg_left hxp ha,mul_le_mul_of_nonneg_left hyp hb]

/-- Universal Euclidean minimization, not only the rational point checks. -/
theorem p_is_projection : Chapter03.ProjectionMin K u p := by
  refine ⟨p_mem,?_⟩
  intro y hy
  have hpy := hy.2.2.2.2
  rw [real_inner_self_eq_norm_sq] at hpy
  have hid := norm_sub_sq_real p y
  have hn := sq_nonneg ‖p-y‖
  simp only [u,zero_sub,norm_neg]
  nlinarith

theorem q_mem : q ∈ K := by
  norm_num [K,p,q,vec,inner_coordinates,norm_squared_coordinates]

theorem q_integral : ∃ z : Fin 2 → ℤ, ∀ i, q i = (z i : ℝ) := by
  refine ⟨![33,0],?_⟩
  intro i; fin_cases i <;> norm_num [q,vec]

theorem u_integral : ∃ z : Fin 2 → ℤ, ∀ i, u i = (z i : ℝ) := by
  exact ⟨fun _ => 0,by simp [u]⟩

theorem p_ne_u : p ≠ u := by
  intro heq
  have h := congrArg (fun y : E => y 1) heq
  norm_num [p,u,vec] at h

theorem full_cut_valid : ∀ y ∈ K, 0 ≤ ⟪p-u,y-p⟫_ℝ :=
  Chapter03.projection_cut_valid K_convex p_is_projection

theorem full_cut_excludes : ⟪p-u,u-p⟫_ℝ < 0 :=
  Chapter03.projection_cut_excludes p_ne_u

theorem full_row_inner (y : E) :
    fullRow (fun i => (p-u) i) (fun i => p i) (fun i => y i) = ⟪p-u,y-p⟫_ℝ := by
  simp [fullRow,inner_coordinates,Fin.sum_univ_two,mul_comm]

theorem dropped_complement : droppedᶜ = {1} := by
  ext i; fin_cases i <;> norm_num [dropped]

theorem retained_row_formula (y : E) :
    retainedRow dropped (fun i => (p-u) i) (fun i => p i) (fun i => y i) =
      (1/8192:ℝ) * (y 1-1/8192) := by
  simp [retainedRow,dropped_complement,p,u,vec]

theorem distance_squared : ‖u-p‖^2 = (68719476737:ℝ)/4611686018427387904 := by
  norm_num [norm_squared_coordinates,u,p,vec]

/-- Exact rational analogues of the recovered strict branch thresholds.
The option default is 1e-4; the squared-distance skip threshold is 1e-8. -/
theorem strict_thresholds :
    |(p-u) 0| < (1:ℝ)/1000000000 ∧
    (1:ℝ)/1000000000 < |(p-u) 1| ∧
    ((1:ℝ)/10000)^2 < ‖u-p‖^2 := by
  rw [distance_squared]
  norm_num [p,u,vec,abs_div]

theorem full_margin_q : ⟪p-u,q-p⟫_ℝ = (2147483647:ℝ)/4611686018427387904 := by
  norm_num [inner_coordinates,p,u,q,vec]

theorem dropped_margin_q :
    retainedRow dropped (fun i => (p-u) i) (fun i => p i) (fun i => q i) =
      -(1:ℝ)/67108864 := by
  rw [retained_row_formula]
  norm_num [q,vec]

/-- A feasible integer point violates the dropped-coordinate row. -/
theorem dropped_cut_invalid : ¬ ∀ y ∈ K,
    0 ≤ retainedRow dropped (fun i => (p-u) i) (fun i => p i) (fun i => y i) := by
  intro h
  have hq := h q q_mem
  rw [dropped_margin_q] at hq
  norm_num at hq

theorem compensation_exact :
    compensation dropped (fun i => (p-u) i) (fun i => p i) lo hi =
      (70866960383:ℝ)/4611686018427387904 := by
  norm_num [compensation,dropped,p,u,vec,lo,hi]

theorem compensated_cut_valid : ∀ y ∈ K,
    -compensation dropped (fun i => (p-u) i) (fun i => p i) lo hi ≤
      retainedRow dropped (fun i => (p-u) i) (fun i => p i) (fun i => y i) := by
  intro y hy
  apply bounded_coordinate_compensation_valid
  · rw [full_row_inner]
    exact full_cut_valid y hy
  · intro i hiD
    have hi0 : i = 0 := by simpa [dropped] using hiD
    subst i
    exact ⟨hy.1,hy.2.1⟩

theorem compensated_target_margin :
    retainedRow dropped (fun i => (p-u) i) (fun i => p i) (fun i => u i) +
      compensation dropped (fun i => (p-u) i) (fun i => p i) lo hi =
        (2147483647:ℝ)/4611686018427387904 := by
  rw [retained_row_formula,compensation_exact]
  norm_num [u]

/-- The valid bounded repair strictly accepts this excluded target. Thus this
repair alone does not supply the target-exclusion premise for no-repeat. -/
theorem compensated_cut_accepts_target :
    -compensation dropped (fun i => (p-u) i) (fun i => p i) lo hi <
      retainedRow dropped (fun i => (p-u) i) (fun i => p i) (fun i => u i) := by
  have h := compensated_target_margin
  linarith

end Chapter03.ProjectionTruncation
