module

public import Chapter03OAKKTMaps
public import Chapter03OAKKTControlConvexity

@[expose] public section

/-! Standalone analytic data for source-complete OA execution controls.
No execution or acceptance claim is made by this data module. -/
noncomputable section
open Chapter02 Chapter02DICOPTExamples Chapter03.OAKKT
open Chapter03.OAKKT.Controls
open scoped BigOperators
namespace Chapter03.OAExec.Controls

theorem point_ext {p q : P} (hx : p.1 0=q.1 0) (hy : p.2 0=q.2 0) : p=q :=
  Prod.ext (scalar_ext hx) (scalar_ext hy)

theorem affine_square_derivative (L : P →L[ℝ] ℝ) (c : ℝ) (p : P) :
    HasFDerivAt (fun z => (L z+c)^2) ((2*(L p+c)) • L) p := by
  have hf : (fun z : P => (L z+c)^2)=(fun z : P => (L z+c)*(L z+c)) := by
    funext z; exact pow_two (L z+c)
  rw [hf,show (2*(L p+c)) • L=(L p+c) • L+(L p+c) • L by rw [two_mul,add_smul]]
  exact (L.hasFDerivAt.add_const c).mul (L.hasFDerivAt.add_const c)

theorem affine_square_convex (L : P →L[ℝ] ℝ) (c : ℝ) :
    ConvexOn ℝ Set.univ (fun z => (L z+c)^2) := by
  refine ⟨convex_univ,?_⟩
  intro p hp q hq a b ha hb hab
  have hid : L (a • p+b • q)+c=a*(L p+c)+b*(L q+c) := by
    simp only [map_add,map_smul,smul_eq_mul]
    linear_combination -c*hab
  change (L (a • p+b • q)+c)^2 ≤ a*(L p+c)^2+b*(L q+c)^2
  rw [hid]
  have h := mul_nonneg (mul_nonneg ha hb) (sq_nonneg ((L p+c)-(L q+c)))
  nlinarith [sq_nonneg (L p+c),sq_nonneg (L q+c)]

theorem affine_row_y (a b : ℝ) : AffineRow (fun p : P => a*p.2 0+b) := by
  refine ⟨scalar 0,scalar a,-b,?_⟩
  intro p
  simp [LinearForm,scalar,Fin.sum_univ_one]

theorem affine_second_difference {g : P → ℝ} (hg : AffineRow g) :
    g (pt (-1) 0)+g (pt 1 0)=2*g (pt 0 0) := by
  obtain ⟨ax,ay,b,he⟩ := hg
  simp only [he,LinearForm,pt,scalar,Fin.sum_univ_one]
  ring

namespace U

def objective (p : P) : ℝ := p.1 0+(p.2 0-1/2)^2
def Df (p : P) : P →L[ℝ] ℝ := cx+(2*(p.2 0-1/2)) • cy
def data : ModelData 1 1 5 0 where
  g := ![fun p => (p.1 0)^2,
    fun p => (p.1 0+p.2 0-1/2)^2-1/4,
    fun p => (p.1 0-p.2 0+1/2)^2-1/4,
    fun p => -p.2 0, fun p => p.2 0-1]
  A := Fin.elim0
  B := Fin.elim0
  rhs := Fin.elim0
  c1 := scalar 0
  c2 := scalar 0
  lo := scalar 0
  hi := scalar 1
def Dg (p : P) : Fin 5 → P →L[ℝ] ℝ :=
  ![(2*p.1 0) • cx,
    (2*(p.1 0+p.2 0-1/2)) • (cx+cy),
    (2*(p.1 0-p.2 0+1/2)) • (cx-cy),-cy,cy]

theorem objective_derivative (p : P) : HasFDerivAt objective (Df p) p := by
  change HasFDerivAt (fun z : P => z.1 0+(z.2 0-1/2)^2) (Df p) p
  simpa [Df,sub_eq_add_neg] using
    cx.hasFDerivAt.fun_add (affine_square_derivative cy (-(1/2)) p)

theorem row_derivative (p : P) (j : Fin 5) :
    HasFDerivAt (data.g j) (Dg p j) p := by
  fin_cases j
  · exact square_derivative p
  · simpa [data,Dg,sub_eq_add_neg] using
      (affine_square_derivative (cx+cy) (-(1/2)) p).sub_const (1/4)
  · simpa [data,Dg,sub_eq_add_neg] using
      (affine_square_derivative (cx-cy) (1/2) p).sub_const (1/4)
  · exact cy.hasFDerivAt.neg
  · exact cy.hasFDerivAt.sub_const 1

theorem objective_convex : ConvexOn ℝ Set.univ objective := by
  change ConvexOn ℝ Set.univ (fun z : P => z.1 0+(z.2 0-1/2)^2)
  simpa [Pi.add_def,sub_eq_add_neg] using
    (cx.toLinearMap.convexOn convex_univ).add (affine_square_convex cy (-(1/2)))

theorem row_convex (j : Fin 5) : ConvexOn ℝ Set.univ (data.g j) := by
  fin_cases j
  · exact square_convex
  · simpa [data,Pi.add_def,sub_eq_add_neg] using
      (affine_square_convex (cx+cy) (-(1/2))).add_const (-(1/4))
  · simpa [data,Pi.add_def,sub_eq_add_neg] using
      (affine_square_convex (cx-cy) (1/2)).add_const (-(1/4))
  · simpa [data,sub_eq_add_neg] using affine_convex 0 (-1) 0
  · simpa [data,sub_eq_add_neg] using affine_convex 0 1 (-1)

theorem row_classification (j : Fin 5) : ¬ AffineRow (data.g j) ↔ j.val<3 := by
  fin_cases j <;> norm_num
  · intro h; have hh := affine_second_difference h
    norm_num [data,pt,scalar] at hh
  · intro h; have hh := affine_second_difference h
    norm_num [data,pt,scalar] at hh
  · intro h; have hh := affine_second_difference h
    norm_num [data,pt,scalar] at hh
  · simpa [data,sub_eq_add_neg] using affine_row_y (-1) 0
  · simpa [data,sub_eq_add_neg] using affine_row_y 1 (-1)

def boundRows : IntegerBoundRows data where
  lower _ := 3
  upper _ := 4
  lower_eq := by intro i p; fin_cases i; simp [data,scalar]
  upper_eq := by intro i p; fin_cases i; rfl

@[simp] theorem hard (p : P) : p ∈ data.linearRegion := by intro i; exact Fin.elim0 i

end U

namespace I

def objective (p : P) : ℝ := -p.1 0+p.2 0
def Df : P →L[ℝ] ℝ := -cx+cy
def data : ModelData 1 1 3 0 where
  g := ![fun p => (p.1 0)^2+7/16-p.2 0,
    fun p => -p.2 0,fun p => p.2 0-1]
  A := Fin.elim0
  B := Fin.elim0
  rhs := Fin.elim0
  c1 := scalar 0
  c2 := scalar 0
  lo := scalar 0
  hi := scalar 1
def Dg (p : P) : Fin 3 → P →L[ℝ] ℝ :=
  ![(2*p.1 0) • cx-cy,-cy,cy]

theorem objective_derivative (p : P) : HasFDerivAt objective Df p :=
  cx.hasFDerivAt.neg.add cy.hasFDerivAt

theorem row_derivative (p : P) (j : Fin 3) :
    HasFDerivAt (data.g j) (Dg p j) p := by
  fin_cases j
  · exact ((square_derivative p).add_const (7/16)).sub cy.hasFDerivAt
  · exact cy.hasFDerivAt.neg
  · exact cy.hasFDerivAt.sub_const 1

theorem objective_convex : ConvexOn ℝ Set.univ objective := by
  change ConvexOn ℝ Set.univ (fun p : P => -p.1 0+p.2 0)
  simpa using affine_convex (-1) 1 0

theorem row_convex (j : Fin 3) : ConvexOn ℝ Set.univ (data.g j) := by
  fin_cases j
  · exact (square_convex.add_const (7/16)).sub (cy.toLinearMap.concaveOn convex_univ)
  · simpa [data,sub_eq_add_neg] using affine_convex 0 (-1) 0
  · simpa [data,sub_eq_add_neg] using affine_convex 0 1 (-1)

theorem row_classification (j : Fin 3) : ¬ AffineRow (data.g j) ↔ j=0 := by
  fin_cases j <;> norm_num
  · intro h; have hh := affine_second_difference h
    norm_num [data,pt,scalar] at hh
  · simpa [data,sub_eq_add_neg] using affine_row_y (-1) 0
  · simpa [data,sub_eq_add_neg] using affine_row_y 1 (-1)

def boundRows : IntegerBoundRows data where
  lower _ := 1
  upper _ := 2
  lower_eq := by intro i p; fin_cases i; simp [data,scalar]
  upper_eq := by intro i p; fin_cases i; rfl

@[simp] theorem hard (p : P) : p ∈ data.linearRegion := by intro i; exact Fin.elim0 i

end I
end Chapter03.OAExec.Controls
