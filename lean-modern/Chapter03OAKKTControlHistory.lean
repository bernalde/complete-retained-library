module

public import Chapter03OAKKTControlCertificates

@[expose] public section

noncomputable section
open Chapter02 Chapter02DICOPTExamples
open scoped BigOperators
namespace Chapter03.OAKKT.Controls

def pairFamily {l r : ℕ} (d : ModelData 1 1 l r)
    (Dg : P → Fin l → P →L[ℝ] ℝ) (N : Set (Fin l)) (seed a : P) :
    TangentFamily 1 1 l 2 where
  origin := ![seed,a]
  selected := ![Set.univ,{j | j∈N ∧ 0≤d.g j a}]
  derivative i j := Dg (![seed,a] i) j

def pairDf (Df : P → P →L[ℝ] ℝ) (seed a : P) : Fin 2 → P →L[ℝ] ℝ :=
  fun i => Df (![seed,a] i)

def pairHistory {l r : ℕ} (d : ModelData 1 1 l r) (f : P → ℝ)
    (Df : P → P →L[ℝ] ℝ) (Dg : P → Fin l → P →L[ℝ] ℝ)
    (N : Set (Fin l)) (seed : P) (x y : V)
    (ha : ∀j,j∉N → AffineRow (d.g j))
    (hg : ∀p j,HasFDerivAt (d.g j) (Dg p j) p)
    (hf : ∀p,HasFDerivAt f (Df p) p) :
    History d f N (pairFamily d Dg N seed (x,y)) (pairDf Df seed (x,y)) x y where
  seed := 0
  current := 1
  distinct := by decide
  initial_all := rfl
  current_origin := rfl
  current_selected := rfl
  affine := ha
  g_derivative i j := hg _ j
  f_derivative i := hf _

theorem final_affine (j : Fin 1) (hj : j∉({0}:Set (Fin 1))) :
    AffineRow (finalModel.g j) := by
  fin_cases j
  exact (hj (by simp)).elim

theorem thesis_affine (j : Fin 5) (hj : j∉({0}:Set (Fin 5))) :
    AffineRow (thesisModel.g j) := by
  fin_cases j
  · exact (hj (by simp)).elim
  · refine ⟨scalar (-1),scalar 0,-(1/2),?_⟩
    intro p
    simp [thesisModel,LinearForm,scalar,Fin.sum_univ_one]
    ring
  · refine ⟨scalar 1,scalar 0,1,?_⟩
    intro p
    simp [thesisModel,LinearForm,scalar,Fin.sum_univ_one]
  · refine ⟨scalar 0,scalar (-1),0,?_⟩
    intro p
    simp [thesisModel,LinearForm,scalar,Fin.sum_univ_one]
  · refine ⟨scalar 0,scalar 1,1,?_⟩
    intro p
    simp [thesisModel,LinearForm,scalar,Fin.sum_univ_one]

theorem active_affine (j : Fin 3) (hj : j∉({0}:Set (Fin 3))) :
    AffineRow (activeModel.g j) := by
  fin_cases j
  · exact (hj (by simp)).elim
  · refine ⟨scalar 0,scalar (-1),0,?_⟩
    intro p
    simp [activeModel,LinearForm,scalar,Fin.sum_univ_one]
  · refine ⟨scalar 0,scalar 1,1,?_⟩
    intro p
    simp [activeModel,LinearForm,scalar,Fin.sum_univ_one]

def seed : P := pt (1/2) (1/4)
def finalFamily (b : ℝ) := pairFamily finalModel finalDg {0} seed (pt (1/2) b)
def thesisFamily (b : ℝ) := pairFamily thesisModel thesisDg {0} seed (pt (1/2) b)
def positiveHistoryDf (b : ℝ) := pairDf positiveDf seed (pt (1/2) b)
def activeFamily := pairFamily activeModel activeDg {0} seed (pt 1 1)
def activeHistoryDf := pairDf (fun _ => activeDf) seed (pt 1 1)

def finalHistory (b : ℝ) : History finalModel positiveF {0}
    (finalFamily b) (positiveHistoryDf b) (scalar (1/2)) (scalar b) :=
  pairHistory finalModel positiveF positiveDf finalDg {0} seed _ _
    final_affine final_derivative positiveF_derivative

def thesisHistory (b : ℝ) : History thesisModel positiveF {0}
    (thesisFamily b) (positiveHistoryDf b) (scalar (1/2)) (scalar b) :=
  pairHistory thesisModel positiveF positiveDf thesisDg {0} seed _ _
    thesis_affine thesis_derivative positiveF_derivative

def activeHistory : History activeModel activeF {0}
    activeFamily activeHistoryDf (scalar 1) (scalar 1) :=
  pairHistory activeModel activeF (fun _ => activeDf) activeDg {0} seed _ _
    active_affine active_derivative activeF_derivative

theorem final_feasible_selection : (finalFamily 1).selected 1=∅ := by
  ext j
  fin_cases j
  norm_num [finalFamily,pairFamily,finalModel,positiveG,pt,scalar]

theorem thesis_feasible_selection : (thesisFamily 1).selected 1=∅ := by
  ext j
  fin_cases j <;>
    norm_num [thesisFamily,pairFamily,thesisModel,positiveG,pt,scalar]

theorem final_restoration_selection : (finalFamily 0).selected 1={0} := by
  ext j
  fin_cases j
  norm_num [finalFamily,pairFamily,finalModel,positiveG,pt,scalar]

theorem thesis_restoration_selection : (thesisFamily 0).selected 1={0} := by
  ext j
  fin_cases j <;>
    norm_num [thesisFamily,pairFamily,thesisModel,positiveG,pt,scalar]

theorem active_selection : activeFamily.selected 1={0} := by
  ext j
  fin_cases j <;>
    norm_num [activeFamily,pairFamily,activeModel,positiveG,pt,scalar]

/-- Any master retaining this genuine seed and the physical hard lower bound
already excludes y=0. This does not assert an OA visit to that fiber. -/
theorem final_seed_already_excludes (b : ℝ) :
    ¬∃z∈Chapter06.EpigraphMaster finalModel positiveF (finalFamily b)
      (positiveHistoryDf b) Set.univ,z.1.2=scalar 0 := by
  rintro ⟨z,hz,hy⟩
  have hl := ((final_hard _).mp hz.1.1.2).1
  have hg := hz.1.1.1.2 0 0 (by simp [finalFamily,pairFamily])
  change positiveG seed+positiveDg seed (z.1-seed)≤0 at hg
  rw [show seed=pt (1/2) (1/4) from rfl,positive_row_tangent] at hg
  norm_num [hy,scalar] at hg
  linarith

/-- In the thesis encoding the retained initial affine g row supplies the same
lower bound. All these rows are soft in restoration; the check is static. -/
theorem thesis_seed_already_excludes (b : ℝ) :
    ¬∃z∈Chapter06.EpigraphMaster thesisModel positiveF (thesisFamily b)
      (positiveHistoryDf b) Set.univ,z.1.2=scalar 0 := by
  rintro ⟨z,hz,hy⟩
  have hg := hz.1.1.1.2 0 0 (by simp [thesisFamily,pairFamily])
  have hl := hz.1.1.1.2 0 1 (by simp [thesisFamily,pairFamily])
  change positiveG seed+positiveDg seed (z.1-seed)≤0 at hg
  rw [show seed=pt (1/2) (1/4) from rfl,positive_row_tangent] at hg
  change (1/2-seed.1 0)+(-cx) (z.1-seed)≤0 at hl
  norm_num [seed,pt,scalar] at hl
  norm_num [hy,scalar] at hg
  linarith

end Chapter03.OAKKT.Controls
