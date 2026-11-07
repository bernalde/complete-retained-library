module

public import Chapter02WeightedRestoration
public import Chapter06

@[expose] public section

/-! Author boundary controls. All source objectives are supplied separately;
all ModelData c1/c2 fields are zero. No algorithm execution is asserted. -/
noncomputable section
open scoped BigOperators
open Chapter02
namespace Chapter03.OAKKTBoundary

def vec (x : ℝ) : RealVector 1 := fun _ => x

def xcoord {m : ℕ} : Point 1 m →L[ℝ] ℝ :=
  (ContinuousLinearMap.proj (0 : Fin 1)).comp
    (ContinuousLinearMap.fst ℝ (RealVector 1) (RealVector m))

def ycoord : Point 1 1 →L[ℝ] ℝ :=
  (ContinuousLinearMap.proj (0 : Fin 1)).comp
    (ContinuousLinearMap.snd ℝ (RealVector 1) (RealVector 1))

@[simp] theorem xcoord_apply {m : ℕ} (p : Point 1 m) : xcoord p = p.1 0 := rfl
@[simp] theorem ycoord_apply (p : Point 1 1) : ycoord p = p.2 0 := rfl

theorem square_derivative {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (L : E →L[ℝ] ℝ) (c : ℝ) (p : E) :
    HasFDerivAt (fun q => (L q-c)^2) ((2*(L p-c)) • L) p := by
  have h := ((L.hasFDerivAt (x := p)).sub_const c).fun_mul
    ((L.hasFDerivAt (x := p)).sub_const c)
  simpa only [pow_two] using h.congr_fderiv (show
    (L p-c) • L+(L p-c) • L=(2*(L p-c)) • L by
      apply ContinuousLinearMap.ext
      intro q
      simp
      ring)

theorem square_convex {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (L : E →L[ℝ] ℝ) (c : ℝ) :
    ConvexOn ℝ Set.univ (fun p => (L p-c)^2) := by
  refine ⟨convex_univ,?_⟩
  intro p hp q hq a b ha hb hab
  simp only [map_add,map_smul,smul_eq_mul]
  have h := mul_nonneg (mul_nonneg ha hb) (sq_nonneg (L p-L q))
  have he : b=1-a := by linarith
  subst b
  nlinarith

/-- The integer carrier is empty: the fixed fiber is the entire one-dimensional
continuous space. The later n=0 control separately tests an empty continuous carrier. -/
def zeroPoint (x : ℝ) : Point 1 0 := (vec x,0)

def zeroData : ModelData 1 0 2 0 where
  g := ![fun p => (p.1 0)^2, fun p => (p.1 0-1)^2-1/4]
  A := fun j => Fin.elim0 j
  B := fun j => Fin.elim0 j
  rhs := fun j => Fin.elim0 j
  c1 := 0
  c2 := 0
  lo := 0
  hi := 0

def zeroDerivative (p : Point 1 0) : Fin 2 → Point 1 0 →L[ℝ] ℝ :=
  ![(2*p.1 0) • xcoord,(2*(p.1 0-1)) • xcoord]

theorem zero_derivative (p : Point 1 0) (j : Fin 2) :
    HasFDerivAt (zeroData.g j) (zeroDerivative p j) p := by
  fin_cases j
  · simpa [zeroData,zeroDerivative] using square_derivative (xcoord (m:=0)) 0 p
  · simpa [zeroData,zeroDerivative] using
      (square_derivative (xcoord (m:=0)) 1 p).sub_const (1/4)

theorem zero_convex (j : Fin 2) : ConvexOn ℝ Set.univ (zeroData.g j) := by
  fin_cases j
  · simpa [zeroData] using square_convex (xcoord (m:=0)) 0
  · simpa [zeroData,sub_eq_add_neg] using
      ((square_convex (xcoord (m:=0)) 1).add_const (-(1/4))).congr
        (g := fun p : Point 1 0 => (xcoord p-1)^2 + (-(1/4))) (fun _ _ => rfl)

theorem zero_current_residuals :
    zeroData.g 0 (zeroPoint (1/2))=1/4 ∧
    zeroData.g 1 (zeroPoint (1/2))=0 := by
  norm_num [zeroData,zeroPoint,vec]

theorem zero_current_tangents (p : Point 1 0) :
    zeroData.g 0 (zeroPoint (1/2))+
      zeroDerivative (zeroPoint (1/2)) 0 (p-zeroPoint (1/2))=p.1 0-1/4 ∧
    zeroData.g 1 (zeroPoint (1/2))+
      zeroDerivative (zeroPoint (1/2)) 1 (p-zeroPoint (1/2))=1/2-p.1 0 := by
  norm_num [zeroData,zeroPoint,vec,zeroDerivative]
  ring

theorem zero_seed_tangents (p : Point 1 0) :
    zeroData.g 0 (zeroPoint 1)+
      zeroDerivative (zeroPoint 1) 0 (p-zeroPoint 1)=2*p.1 0-1 ∧
    zeroData.g 1 (zeroPoint 1)+
      zeroDerivative (zeroPoint 1) 1 (p-zeroPoint 1)=-(1/4) := by
  norm_num [zeroData,zeroPoint,vec,zeroDerivative]
  ring

/-- The seed is deliberately not an original feasible point. -/
theorem zero_seed_not_feasible : zeroPoint 1 ∉ zeroData.feasibleOn Set.univ := by
  intro h
  have h0 := ((source_feasible_iff zeroData Set.univ _).mp h).2.1 0
  norm_num [zeroData,zeroPoint,vec] at h0

def splitPoint (x y : ℝ) : Point 1 1 := (vec x,vec y)

def splitSoftData : ModelData 1 1 5 0 where
  g := ![fun p => (p.1 0-2)^2-p.2 0, fun p => -p.1 0,
    fun p => p.1 0-1, fun p => -p.2 0, fun p => p.2 0-1]
  A := fun j => Fin.elim0 j
  B := fun j => Fin.elim0 j
  rhs := fun j => Fin.elim0 j
  c1 := 0
  c2 := 0
  lo := 0
  hi := 1

/-- The physical bounds become genuine hard rows; the two integer-bound residuals
remain soft rows with individual slacks. -/
def splitHardData : ModelData 1 1 3 2 where
  g := ![fun p => (p.1 0-2)^2-p.2 0, fun p => -p.2 0, fun p => p.2 0-1]
  A := ![vec (-1),vec 1]
  B := 0
  rhs := ![0,1]
  c1 := 0
  c2 := 0
  lo := 0
  hi := 1

def splitSoftDerivative (p : Point 1 1) : Fin 5 → Point 1 1 →L[ℝ] ℝ :=
  ![(2*(p.1 0-2)) • xcoord-ycoord,-xcoord,xcoord,-ycoord,ycoord]

def splitHardDerivative (p : Point 1 1) : Fin 3 → Point 1 1 →L[ℝ] ℝ :=
  ![(2*(p.1 0-2)) • xcoord-ycoord,-ycoord,ycoord]

theorem split_soft_derivative (p : Point 1 1) (j : Fin 5) :
    HasFDerivAt (splitSoftData.g j) (splitSoftDerivative p j) p := by
  fin_cases j
  · exact (square_derivative (xcoord (m:=1)) 2 p).sub ycoord.hasFDerivAt
  · exact xcoord.hasFDerivAt.neg
  · exact xcoord.hasFDerivAt.sub_const 1
  · exact ycoord.hasFDerivAt.neg
  · exact ycoord.hasFDerivAt.sub_const 1

theorem split_hard_derivative (p : Point 1 1) (j : Fin 3) :
    HasFDerivAt (splitHardData.g j) (splitHardDerivative p j) p := by
  fin_cases j
  · exact (square_derivative (xcoord (m:=1)) 2 p).sub ycoord.hasFDerivAt
  · exact ycoord.hasFDerivAt.neg
  · exact ycoord.hasFDerivAt.sub_const 1

theorem split_soft_convex (j : Fin 5) : ConvexOn ℝ Set.univ (splitSoftData.g j) := by
  fin_cases j
  · exact (square_convex (xcoord (m:=1)) 2).sub
      (ycoord.toLinearMap.concaveOn convex_univ)
  · exact (-xcoord.toLinearMap).convexOn convex_univ
  · simpa [splitSoftData,sub_eq_add_neg] using
      (((xcoord (m:=1)).toLinearMap.convexOn convex_univ).add_const (-1)).congr
        (g := fun p : Point 1 1 => xcoord p + (-1)) (fun _ _ => rfl)
  · exact (-ycoord.toLinearMap).convexOn convex_univ
  · simpa [splitSoftData,sub_eq_add_neg] using
      ((ycoord.toLinearMap.convexOn convex_univ).add_const (-1)).congr
        (g := fun p : Point 1 1 => ycoord p + (-1)) (fun _ _ => rfl)

theorem split_hard_convex (j : Fin 3) : ConvexOn ℝ Set.univ (splitHardData.g j) := by
  fin_cases j
  · exact split_soft_convex 0
  · exact split_soft_convex 3
  · exact split_soft_convex 4

theorem split_hard_region (p : Point 1 1) :
    p ∈ splitHardData.linearRegion ↔ 0 ≤ p.1 0 ∧ p.1 0 ≤ 1 := by
  simp [ModelData.linearRegion,splitHardData,LinearForm,Fin.forall_fin_two,vec]

theorem split_original_same :
    splitSoftData.feasibleOn Set.univ = splitHardData.feasibleOn Set.univ := by
  ext p
  rw [source_feasible_iff,source_feasible_iff]
  simp [splitSoftData,splitHardData,LinearForm,vec,Fin.forall_fin_succ]
  tauto

theorem split_original_feasible : splitPoint 1 1 ∈ splitSoftData.feasibleOn Set.univ := by
  apply (source_feasible_iff _ _ _).mpr
  refine ⟨Set.mem_univ _,?_,fun j => Fin.elim0 j,(fun _ => (1 : ℤ)),?_,?_⟩
  · intro j; fin_cases j <;> norm_num [splitSoftData,splitPoint,vec]
  · intro j; norm_num [splitSoftData,vec]
  · ext i; simp [splitPoint,vec]

/-- Lower bound for every literal separate-slack feasible pair. -/
theorem zero_slack_lower_bound (x : RealVector 1) (s : RealVector 2)
    (hg : ∀ j, zeroData.g j (x,0) ≤ s j) :
    (1/4 : ℝ) ≤ ∑ j, s j := by
  have h0 := hg 0
  have h1 := hg 1
  simp only [zeroData,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.head_cons] at h0 h1
  rw [Fin.sum_univ_two]
  nlinarith [sq_nonneg (x 0-1/2)]

theorem split_soft_slack_lower_bound (x : RealVector 1) (s : RealVector 5)
    (hg : ∀ j, splitSoftData.g j (x,0) ≤ s j)
    (hs : ∀ j, 0 ≤ s j) : (3/4 : ℝ) ≤ ∑ j, s j := by
  have h0 := hg 0
  have h2 := hg 2
  norm_num [splitSoftData] at h0
  change x 0-1 ≤ s 2 at h2
  simp only [Fin.sum_univ_succ]
  change (3/4 : ℝ) ≤ s 0+(s 1+(s 2+(s 3+(s 4+0))))
  have h1 := hs 1
  have h3 := hs 3
  have h4 := hs 4
  norm_num at *
  nlinarith [sq_nonneg (x 0-3/2)]

theorem split_hard_slack_lower_bound (x : RealVector 1) (s : RealVector 3)
    (hx : (x,0) ∈ splitHardData.linearRegion)
    (hg : ∀ j, splitHardData.g j (x,0) ≤ s j)
    (hs : ∀ j, 0 ≤ s j) : (1 : ℝ) ≤ ∑ j, s j := by
  have hu := ((split_hard_region (x,0)).mp hx).2
  have h0 := hg 0
  norm_num [splitHardData] at h0
  simp only [Fin.sum_univ_succ]
  have h1 := hs 1
  have h2 := hs 2
  norm_num at *
  nlinarith [sq_nonneg (x 0-1)]

end Chapter03.OAKKTBoundary
