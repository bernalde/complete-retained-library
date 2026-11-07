module

public import Chapter02ConvexSubgradientSource
public import Chapter02CPDomainExamples
public import Mathlib.Analysis.Calculus.Deriv.Abs
public import Mathlib.Tactic

@[expose] public section

/-! One full nonsmooth mixed-model control, and one companion distinguishing
ambient support from the accepted relative derivative freedom. The auxiliary
two-piece family, the one original nonsmooth row and its singleton maximum are
explicitly distinct. All algebraic helper results are private and uncounted.
Candidate only; independent frozen source/type review remains required. -/

noncomputable section
open scoped BigOperators
open Chapter02
namespace Chapter02ConvexSubgradientExamples

abbrev P := Point 1 1
def point (x y : ℝ) : P := (fun _ => x, fun _ => y)
def coordX : P →L[ℝ] ℝ :=
  (ContinuousLinearMap.proj 0).comp
    (ContinuousLinearMap.fst ℝ (RealVector 1) (RealVector 1))
def coordY : P →L[ℝ] ℝ :=
  (ContinuousLinearMap.proj 0).comp
    (ContinuousLinearMap.snd ℝ (RealVector 1) (RealVector 1))
def row (p : P) : ℝ := |p.1 0| + p.2 0 - 1
def pieces : Fin 2 → P → ℝ :=
  ![fun p => p.1 0 + p.2 0 - 1, fun p => -p.1 0 + p.2 0 - 1]
def pieceNormals : Fin 2 → P →L[ℝ] ℝ := ![coordX + coordY, -coordX + coordY]
def weights (_ : Fin 2) : ℝ := 1/2
def trial : P := point 0 2

/-- The compact box is carried by K, and y's integer bounds by lo/hi.
There are no affine rows, exactly one nonlinear row, and one integer coordinate. -/
def model : ModelData 1 1 1 0 where
  g := fun _ => row
  A := fun i => Fin.elim0 i
  B := fun i => Fin.elim0 i
  rhs := fun i => Fin.elim0 i
  c1 := fun _ => 0
  c2 := fun _ => -1
  lo := fun _ => 0
  hi := fun _ => 2
def mixedRow (_ : Fin 1) (x : RealVector 1) (y : IntVector 1) : ℝ :=
  |x 0| + (y 0 : ℝ) - 1
def domain : Set P := Set.Icc (point (-2) 0) (point 2 2)
def origins (_ : Fin 1) : P := trial
def normals (_ : Fin 1) : P →L[ℝ] ℝ := coordY
def cuts : TangentFamily 1 1 1 1 := maximumNormalFamily origins normals

private lemma piece_convex (j : Fin 2) : ConvexOn ℝ Set.univ (pieces j) := by
  refine ⟨convex_univ, ?_⟩
  intro p hp q hq a b ha hb hab
  fin_cases j <;> dsimp [pieces] <;> nlinarith

private lemma pieces_max (p : P) : eshMaximum pieces p = row p := by
  apply le_antisymm
  · apply (eshMaximum_le_iff _ _ _).mpr
    intro j
    fin_cases j <;> simp [pieces, row] <;>
      linarith [le_abs_self (p.1 0), neg_le_abs (p.1 0)]
  · have h := (eshMaximum_le_iff pieces p (eshMaximum pieces p)).mp le_rfl
    rcases le_total 0 (p.1 0) with hp | hp
    · simpa [pieces, row, abs_of_nonneg hp] using h 0
    · simpa [pieces, row, abs_of_nonpos hp] using h 1

private lemma pieces_max_identity : eshMaximum pieces = row := funext pieces_max

private lemma piece_member (j : Fin 2) :
    pieceNormals j ∈ ambientConvexSubdiff (pieces j) trial := by
  intro p
  fin_cases j <;>
    simp [pieces, pieceNormals, trial, point, coordX, coordY,
      ContinuousLinearMap.comp_apply, ambientConvexSubdiff] <;> linarith

private lemma weighted_normal : (∑ j, weights j • pieceNormals j) = coordY := by
  apply ContinuousLinearMap.ext
  intro p
  simp [Fin.sum_univ_succ, weights, pieceNormals, coordX, coordY,
    ContinuousLinearMap.comp_apply]
  ring

private lemma actual_combination :
    ConvexOn ℝ Set.univ (eshMaximum pieces) ∧
      coordY ∈ ambientConvexSubdiff (eshMaximum pieces) trial := by
  have h := active_convex_subgradient_sum (g := pieces) (z := trial)
    piece_convex weights pieceNormals (by intro j; norm_num [weights])
    (by norm_num [weights, Fin.sum_univ_succ])
    (by intro j hj; rw [pieces_max]; fin_cases j <;> norm_num [pieces, row, trial, point])
    (by intro j hj; exact piece_member j)
  rw [weighted_normal] at h
  exact h

private lemma row_convex : ConvexOn ℝ Set.univ row := by
  rw [← pieces_max_identity]
  exact actual_combination.1

private lemma row_member : coordY ∈ ambientConvexSubdiff row trial := by
  rw [← pieces_max_identity]
  exact actual_combination.2

private lemma singleton_max (p : P) : eshMaximum model.g p = row p := by
  simp [eshMaximum, model, Finset.univ_unique]

private lemma singleton_max_identity : eshMaximum model.g = row := funext singleton_max

private lemma singleton_member :
    coordY ∈ ambientConvexSubdiff (eshMaximum model.g) trial := by
  rw [singleton_max_identity]
  exact row_member

private lemma not_piece (j : Fin 2) : coordY ≠ pieceNormals j := by
  intro h
  have he := congrArg (fun D : P →L[ℝ] ℝ => D (point 1 0)) h
  fin_cases j <;> norm_num [pieceNormals, coordX, coordY, point,
    ContinuousLinearMap.comp_apply] at he

private lemma genuinely_nondifferentiable : ¬ DifferentiableAt ℝ row trial := by
  intro h
  have hline : DifferentiableAt ℝ (fun t : ℝ => point t 2) 0 := by
    unfold point
    fun_prop
  have hc : DifferentiableAt ℝ (fun t : ℝ => row (point t 2)) 0 :=
    DifferentiableAt.comp (f := fun t : ℝ => point t 2) (g := row) 0
      (by simpa only [trial] using h) hline
  have ha := hc.sub_const (1 : ℝ)
  apply not_differentiableAt_abs_zero
  convert ha using 1
  ext t
  simp [row, point]
  ring

private lemma mem_domain (p : P) : p ∈ domain ↔
    -2 ≤ p.1 0 ∧ p.1 0 ≤ 2 ∧ 0 ≤ p.2 0 ∧ p.2 0 ≤ 2 := by
  simp [domain, point, Set.mem_Icc, Prod.le_def, Pi.le_def, Fin.forall_fin_one]
  tauto

private lemma original_zero : point 0 0 ∈ model.feasibleOn domain := by
  rw [source_feasible_iff]
  refine ⟨(mem_domain _).mpr (by norm_num [point]), ?_, ?_, ?_⟩
  · intro j; norm_num [model, row, point]
  · intro j; exact Fin.elim0 j
  · refine ⟨fun _ => 0, ?_, ?_⟩
    · intro i; norm_num [model]
    · funext i; norm_num [point]

private lemma original_one : point 0 1 ∈ model.feasibleOn domain := by
  rw [source_feasible_iff]
  refine ⟨(mem_domain _).mpr (by norm_num [point]), ?_, ?_, ?_⟩
  · intro j; norm_num [model, row, point]
  · intro j; exact Fin.elim0 j
  · refine ⟨fun _ => 1, ?_, ?_⟩
    · intro i; norm_num [model]
    · funext i; norm_num [point]

private lemma exact_cut (p : P) :
    p ∈ cuts.cutRegion (maximumRowModel model) ↔ p.2 0 ≤ 1 := by
  simp [cuts, maximumNormalFamily, TangentFamily.cutRegion, origins, normals,
    maximumRowModel, singleton_max, trial, point, row, coordY,
    ContinuousLinearMap.comp_apply, Fin.forall_fin_one]

private lemma objective_value (p : P) : model.objective p = -p.2 0 := by
  simp [ModelData.objective, LinearForm, model, Fin.sum_univ_succ]

private lemma objective_unchanged : (maximumRowModel model).objective = model.objective := rfl

/-- One linked control: a genuine nonsmooth mixed model, constructed ambient
normal, literal static source bridge, complete cut and actual optimization. -/
theorem kink_model_control :
    eshMaximum pieces = row ∧ eshMaximum model.g = row ∧
    (∑ j, weights j • pieceNormals j) = coordY ∧
    coordY ∈ ambientConvexSubdiff (eshMaximum pieces) trial ∧
    coordY ∈ ambientConvexSubdiff row trial ∧
    coordY ∈ ambientConvexSubdiff (eshMaximum model.g) trial ∧
    (∀ j, coordY ≠ pieceNormals j) ∧
    ¬ DifferentiableAt ℝ row trial ∧
    sourceMixedFeasible model mixedRow domain = model.feasibleOn domain ∧
    model.feasibleOn domain = (maximumRowModel model).feasibleOn domain ∧
    sourceMixedFeasible model mixedRow domain ⊆
      (maximumRowModel model).masterOn cuts domain ∧
    (∃ M : ℝ, 0 ≤ M ∧ ∀ x ∈ domain,
      ∀ D ∈ ambientConvexSubdiff (eshMaximum model.g) x, ‖D‖ ≤ M) ∧
    (∀ p : P, p ∈ cuts.cutRegion (maximumRowModel model) ↔ p.2 0 ≤ 1) ∧
    eshMaximum model.g trial = 1 ∧
    trial ∉ cuts.cutRegion (maximumRowModel model) ∧
    point 0 0 ∈ sourceMixedFeasible model mixedRow domain ∧
    point 0 0 ∈ (maximumRowModel model).masterOn cuts domain ∧
    IsMinimizer ((maximumRowModel model).masterOn cuts domain)
      (maximumRowModel model).objective (point 0 1) ∧
    model.objective (point 0 1) = -1 ∧
    IsMinimizer (sourceMixedFeasible model mixedRow domain) model.objective (point 0 1) := by
  have hs := source_convex_maximum_cuts model mixedRow domain origins normals
    (by intro j x y; rfl) isCompact_Icc
    (by intro j; exact row_convex)
    (by intro i; apply (mem_domain _).mpr; norm_num [origins, trial, point])
    (by intro i; exact singleton_member)
  have hcontain : sourceMixedFeasible model mixedRow domain ⊆
      (maximumRowModel model).masterOn cuts domain := hs.2.2.1
  have hzero : point 0 0 ∈ sourceMixedFeasible model mixedRow domain := by
    rw [hs.1]; exact original_zero
  have hone : point 0 1 ∈ sourceMixedFeasible model mixedRow domain := by
    rw [hs.1]; exact original_one
  have hmaster : IsMinimizer ((maximumRowModel model).masterOn cuts domain)
      (maximumRowModel model).objective (point 0 1) := by
    refine ⟨hcontain hone, ?_⟩
    intro p hp
    have hy : p.2 0 ≤ 1 := (exact_cut p).mp hp.1.1.2
    rw [objective_unchanged, objective_value, objective_value]
    simp only [point]
    linarith
  have horiginal : IsMinimizer (sourceMixedFeasible model mixedRow domain)
      model.objective (point 0 1) := by
    apply minimizer_of_relaxation_feasible hcontain _ hone
    simpa only [objective_unchanged] using hmaster
  refine ⟨pieces_max_identity, singleton_max_identity, weighted_normal,
    actual_combination.2, row_member, singleton_member, not_piece,
    genuinely_nondifferentiable, hs.1, hs.2.1, hcontain, hs.2.2.2.2,
    exact_cut, ?_, ?_, hzero, hcontain hzero, hmaster, ?_, horiginal⟩
  · rw [singleton_max]; norm_num [row, trial, point]
  · exact hs.2.2.2.1 0 (by rw [singleton_max]; norm_num [origins, row, trial, point])
  · rw [objective_value]; norm_num [point]

/-- Accepted relative normal freedom does not give ambient zero support.
The contradiction uses the actual off-segment test point z+(0,a). -/
theorem relative_normal_not_ambient (a : ℝ) (ha : a ≠ 0)
    (z : Chapter02CPDomainExamples.Plane) (hz : z ∈ Chapter02CPDomainExamples.segment) :
    HasFDerivWithinAt (fun _ : Chapter02CPDomainExamples.Plane => (0 : ℝ))
      (Chapter02CPDomainExamples.normal a) Chapter02CPDomainExamples.segment z ∧
    Chapter02CPDomainExamples.normal a ∉
      ambientConvexSubdiff (fun _ : Chapter02CPDomainExamples.Plane => (0 : ℝ)) z := by
  refine ⟨Chapter02CPDomainExamples.segment_arbitrary_normal_derivative a z hz, ?_⟩
  intro h
  have htest := h (z + (0, a))
  change 0 + a * (z.2 + a - z.2) ≤ 0 at htest
  have hpos := sq_pos_of_ne_zero ha
  nlinarith

end Chapter02ConvexSubgradientExamples

#print axioms Chapter02ConvexSubgradientExamples.kink_model_control
#print axioms Chapter02ConvexSubgradientExamples.relative_normal_not_ambient
