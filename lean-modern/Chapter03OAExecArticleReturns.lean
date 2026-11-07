module

public import Chapter03OAExecInitialization
public import Chapter03OAExecArticleGAvailability
public import Chapter03OAExecArticleTTrace

@[expose] public section

noncomputable section
open Chapter02 Chapter02DICOPTExamples Chapter03.OAKKT
namespace Chapter03.OAExec.Article

theorem box_card_two (a b : ℝ) (g : P → ℝ) :
    (integerBox_finite (boxModel a b g).lo (boxModel a b g).hi).toFinset.card=2 := by
  have h : (integerBox_finite (boxModel a b g).lo (boxModel a b g).hi).toFinset=
      {fun _ : Fin 1 => (0:ℤ),fun _ : Fin 1 => (1:ℤ)} := by
    ext y
    rw [Set.Finite.mem_toFinset,binary_box]
    simp [funext_iff,Fin.forall_fin_one]
  rw [h]
  norm_num [funext_iff,Fin.forall_fin_one]

theorem G_box_card : Gdata.box.card=2 := box_card_two (-1) 1 _
theorem T_box_card : Tdata.box.card=2 := box_card_two 0 1 _
theorem A_box_card : Adata.box.card=2 := box_card_two (-1) 1 _

/-- Actual application of the main theorem, with every analytic, initial,
master-attainment and certificate-bearing fixed-solve hypothesis discharged. -/
theorem G_corrected_finite (epsilon : ℝ) (heps : 0 ≤ epsilon) :
    Nonempty (Selector Gdata (pt 0 (1/2)) epsilon) ∧
    ∀ choose : Selector Gdata (pt 0 (1/2)) epsilon, ∃ out,
      runFuel Gdata (pt 0 (1/2)) epsilon choose 3
        (initialState Gdata (pt 0 (1/2))) .initial=some out ∧
      ReturnCertificate Gdata epsilon out.result ∧
      out.masters≤3 ∧ out.fixed≤3 ∧ out.restorations≤2 := by
  simpa only [G_box_card,show 2+1=3 by rfl] using
    locally_available_finite_return G_analytic G_seed_valid heps (G_local_availability epsilon)

/-- Every admissible exact policy reaches the actual master's empty exit.
The initializer is genuinely nonempty and fractional, and every selected
integer fiber has its positive actual sum-slack restoration. -/
theorem A_all_selectors_infeasible (epsilon : ℝ) (heps : 0 ≤ epsilon) :
    Nonempty (Selector Adata (pt 0 (1/2)) epsilon) ∧
    ∀ choose : Selector Adata (pt 0 (1/2)) epsilon, ∃ out,
      runFuel Adata (pt 0 (1/2)) epsilon choose 3
        (initialState Adata (pt 0 (1/2))) .initial=some out ∧
      out.result=.infeasible ∧ out.masters≤3 ∧ out.fixed≤3 ∧ out.restorations≤2 := by
  have h := locally_available_finite_return A_analytic A_seed_valid heps
    (A_local_availability epsilon)
  refine ⟨h.1,?_⟩
  intro choose
  obtain ⟨out,hr,hcert,hm,hf,hs⟩ := h.2 choose
  have hi : out.result=.infeasible := by
    cases he : out.result with
    | infeasible => rfl
    | solution p =>
      rw [he] at hcert
      exact (A_original_empty ⟨p,hcert.1⟩).elim
  refine ⟨out,?_,hi,?_,?_,?_⟩
  · simpa only [A_box_card,show 2+1=3 by rfl] using hr
  · simpa only [A_box_card,show 2+1=3 by rfl] using hm
  · simpa only [A_box_card,show 2+1=3 by rfl] using hf
  · simpa only [A_box_card] using hs

theorem integral_zero : integral (pt 0 0) := by
  refine ⟨fun _ => 0,?_⟩
  ext i
  fin_cases i
  norm_num [pt,Chapter03.OAKKT.intCast,scalar]

theorem Integral_minimum_unique (p : P)
    (hp : IsMinimizer IntegralData.relaxation IntegralData.f p) : p=pt 0 0 := by
  have h := hp.2 (pt 0 0) integral_initializer_minimum.1
  change quadratic 0 p ≤ quadratic 0 (pt 0 0) at h
  norm_num [quadratic,pt,scalar] at h
  have hx : p.1 0=0 := by nlinarith [sq_nonneg (p.1 0),sq_nonneg (p.2 0)]
  have hy : p.2 0=0 := by nlinarith [sq_nonneg (p.1 0),sq_nonneg (p.2 0)]
  apply Prod.ext <;> ext i <;> fin_cases i
  · exact hx
  · exact hy

def EmptyInitialSelectors (epsilon : ℝ) : InitializedSelectors EmptyData epsilon :=
  fun seed hs => (empty_initializer_relaxation ⟨seed,hs.1.1⟩).elim

def IntegralInitialSelectors (epsilon : ℝ) : InitializedSelectors IntegralData epsilon :=
  fun seed hs => (hs.2.2 (by rw [Integral_minimum_unique seed hs.1]; exact integral_zero)).elim

def EmptyInitialization : Initialization EmptyData :=
  .empty (Set.not_nonempty_iff_eq_empty.mp empty_initializer_relaxation)

def IntegralInitialization : Initialization IntegralData :=
  .minimum (pt 0 0) integral_initializer_minimum (Set.mem_univ _)

theorem actual_empty_initializer (epsilon : ℝ) :
    execute EmptyData epsilon (EmptyInitialSelectors epsilon) EmptyInitialization=
      some ⟨.infeasible,0,0,0⟩ ∧ ¬ EmptyData.original.Nonempty := by
  refine ⟨rfl,?_⟩
  rintro ⟨p,hp⟩
  exact empty_initializer_relaxation ⟨p,original_subset_relaxation EmptyData hp⟩

theorem actual_integral_initializer (epsilon : ℝ) :
    execute IntegralData epsilon (IntegralInitialSelectors epsilon) IntegralInitialization=
      some ⟨.solution (pt 0 0),0,0,0⟩ ∧
    IsMinimizer IntegralData.original IntegralData.f (pt 0 0) := by
  refine ⟨?_,Chapter03.OAExec.integral_initializer_minimum integral_initializer_minimum integral_zero⟩
  simp only [execute,IntegralInitialization,dif_pos integral_zero]

end Chapter03.OAExec.Article

#print axioms Chapter03.OAExec.Article.G_corrected_finite
#print axioms Chapter03.OAExec.Article.A_all_selectors_infeasible
#print axioms Chapter03.OAExec.Article.actual_empty_initializer
#print axioms Chapter03.OAExec.Article.actual_integral_initializer
