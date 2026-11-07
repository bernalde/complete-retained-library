module

public import Chapter03OAKKTControlConvexity
public import Chapter03OAKKTControlCertificates

@[expose] public section

/-! Author controls for the article's external hard X and Y boxes. No accepted
claim is changed. The one source g row remains soft in restoration. -/
noncomputable section
open Chapter02 Chapter02DICOPTExamples Chapter03.OAKKT
open scoped BigOperators
namespace Chapter03.OAExec.Article

abbrev P := Point 1 1
abbrev V := RealVector 1
abbrev pt := Chapter03.OAKKT.Controls.pt
abbrev cx := Chapter03.OAKKT.Controls.cx
abbrev cy := Chapter03.OAKKT.Controls.cy

def quadratic (a : ℝ) (p : P) : ℝ := (p.1 0)^2 + (p.2 0-a)^2
def quadraticD (a : ℝ) (p : P) : P →L[ℝ] ℝ :=
  (2*p.1 0) • cx + (2*(p.2 0-a)) • cy
def linearQuadratic (a : ℝ) (p : P) : ℝ := p.1 0 + (p.2 0-a)^2
def linearQuadraticD (a : ℝ) (p : P) : P →L[ℝ] ℝ :=
  cx + (2*(p.2 0-a)) • cy
def xSquareRow (c : ℝ) (p : P) : ℝ := (p.1 0)^2-c
def xSquareD (p : P) : P →L[ℝ] ℝ := (2*p.1 0) • cx

theorem y_square_derivative (a : ℝ) (p : P) :
    HasFDerivAt (fun q : P => (q.2 0-a)^2) ((2*(p.2 0-a)) • cy) p := by
  have h : HasFDerivAt (fun q : P => cy q-a) cy p := cy.hasFDerivAt.sub_const a
  convert h.mul h using 1
  · ext q
    exact pow_two (q.2 0-a)
  · apply ContinuousLinearMap.ext
    intro v
    simp [two_mul,add_mul]

theorem quadratic_derivative (a : ℝ) (p : P) :
    HasFDerivAt (quadratic a) (quadraticD a p) p :=
  (Chapter03.OAKKT.Controls.square_derivative p).add (y_square_derivative a p)

theorem linearQuadratic_derivative (a : ℝ) (p : P) :
    HasFDerivAt (linearQuadratic a) (linearQuadraticD a p) p :=
  cx.hasFDerivAt.add (y_square_derivative a p)

theorem xSquareRow_derivative (c : ℝ) (p : P) :
    HasFDerivAt (xSquareRow c) (xSquareD p) p :=
  (Chapter03.OAKKT.Controls.square_derivative p).sub_const c

theorem y_square_convex (a : ℝ) :
    ConvexOn ℝ Set.univ (fun q : P => (q.2 0-a)^2) := by
  refine ⟨convex_univ,?_⟩
  intro p hp q hq s t hs ht hst
  change (s*p.2 0+t*q.2 0-a)^2 ≤ s*(p.2 0-a)^2+t*(q.2 0-a)^2
  have h := mul_nonneg (mul_nonneg hs ht) (sq_nonneg (p.2 0-q.2 0))
  have he : t=1-s := by linarith
  rw [he] at h ⊢
  nlinarith only [h]

theorem quadratic_convex (a : ℝ) : ConvexOn ℝ Set.univ (quadratic a) :=
  Chapter03.OAKKT.Controls.square_convex.add (y_square_convex a)

theorem linearQuadratic_convex (a : ℝ) : ConvexOn ℝ Set.univ (linearQuadratic a) :=
  cx.toLinearMap.convexOn convex_univ |>.add (y_square_convex a)

theorem xSquareRow_convex (c : ℝ) : ConvexOn ℝ Set.univ (xSquareRow c) :=
  by
    change ConvexOn ℝ Set.univ (fun p : P => (p.1 0)^2-c)
    simpa only [Pi.add_def,sub_eq_add_neg] using
      Chapter03.OAKKT.Controls.square_convex.add_const (-c)

def boxModel (lower upper : ℝ) (g : P → ℝ) : ModelData 1 1 1 2 where
  g _ := g
  A := ![scalar (-1),scalar 1]
  B _ := scalar 0
  rhs := ![-lower,upper]
  c1 := scalar 0
  c2 := scalar 0
  lo := scalar 0
  hi := scalar 1

theorem box_hard (a b : ℝ) (g : P → ℝ) (p : P) :
    p ∈ (boxModel a b g).linearRegion ↔ a ≤ p.1 0 ∧ p.1 0 ≤ b := by
  simp [ModelData.linearRegion,LinearForm,boxModel,Fin.forall_fin_two,
    Fin.sum_univ_one,scalar]

theorem binary_box (a b : ℝ) (g : P → ℝ) (y : IntVector 1) :
    y ∈ IntegerBox (boxModel a b g).lo (boxModel a b g).hi ↔ y 0=0 ∨ y 0=1 := by
  simp only [IntegerBox,Set.mem_setOf_eq,boxModel,scalar,Fin.forall_fin_one]
  norm_cast
  omega

theorem box_relaxation (a b : ℝ) (g : P → ℝ) (p : P) :
    p ∈ (boxModel a b g).relaxationOn Set.univ ↔
      a ≤ p.1 0 ∧ p.1 0 ≤ b ∧ 0 ≤ p.2 0 ∧ p.2 0 ≤ 1 ∧ g p ≤ 0 := by
  simp only [ModelData.relaxationOn,ContinuousRelaxation,Set.mem_setOf_eq,
    Set.mem_inter_iff,Set.mem_univ,true_and,ModelData.nonlinearRegion]
  change ((∀ j : Fin 1, g p ≤ 0) ∧ p ∈ (boxModel a b g).linearRegion ∧
    ∀ i : Fin 1, 0 ≤ p.2 i ∧ p.2 i ≤ 1) ↔ _
  rw [box_hard]
  simp only [Fin.forall_fin_one]
  tauto

theorem xSquareRow_nonaffine (c : ℝ) : ¬ AffineRow (xSquareRow c) := by
  rintro ⟨ax,ay,b,h⟩
  have h0 := h (pt 0 0)
  have h1 := h (pt 1 0)
  have hm := h (pt (-1) 0)
  norm_num [xSquareRow,LinearForm,pt,scalar,Fin.sum_univ_one] at h0 h1 hm
  linarith

theorem quadraticRow_nonaffine (a c : ℝ) :
    ¬ AffineRow (fun p => quadratic a p-c) := by
  rintro ⟨ax,ay,b,h⟩
  have h0 := h (pt 0 0)
  have h1 := h (pt 1 0)
  have hm := h (pt (-1) 0)
  norm_num [quadratic,LinearForm,pt,scalar,Fin.sum_univ_one] at h0 h1 hm
  linarith

theorem square_le_one {x : ℝ} (hl : -1 ≤ x) (hu : x ≤ 1) : x^2 ≤ 1 := by
  have h := mul_nonneg (show 0 ≤ x+1 by linarith) (show 0 ≤ 1-x by linarith)
  nlinarith

def G := boxModel (-1) 1 (xSquareRow 4)
def Gf := quadratic (1/2)
def Gdf := quadraticD (1/2)
def Gdg (p : P) (_ : Fin 1) := xSquareD p

theorem G_rows_exact : {j | ¬ AffineRow (G.g j)} = Set.univ := by
  ext j
  simp [G,boxModel,xSquareRow_nonaffine]

theorem G_relaxation (p : P) : p ∈ G.relaxationOn Set.univ ↔
    -1 ≤ p.1 0 ∧ p.1 0 ≤ 1 ∧ 0 ≤ p.2 0 ∧ p.2 0 ≤ 1 := by
  rw [G,box_relaxation]
  constructor
  · tauto
  · rintro ⟨hl,hu,hyl,hyu⟩
    refine ⟨hl,hu,hyl,hyu,?_⟩
    dsimp [xSquareRow]
    nlinarith [square_le_one hl hu]

theorem G_initial_minimum : IsMinimizer (G.relaxationOn Set.univ) Gf (pt 0 (1/2)) := by
  refine ⟨(G_relaxation _).mpr (by norm_num [pt,scalar]),?_⟩
  intro p hp
  norm_num [Gf,quadratic,pt,scalar]
  positivity

theorem G_fiber (y : V) (x : V) : x ∈ fiber G y ↔ -1 ≤ x 0 ∧ x 0 ≤ 1 := by
  constructor
  · intro h; exact (box_hard (-1) 1 _ _).mp h.1
  · rintro ⟨hl,hu⟩
    refine ⟨(box_hard (-1) 1 _ _).mpr ⟨hl,hu⟩,?_⟩
    intro j
    change (x 0)^2-4 ≤ 0
    nlinarith [square_le_one hl hu]

theorem G_fiber_minimum (y : V) :
    IsMinimizer (fiber G y) (fiberObjective Gf y) (scalar 0) := by
  refine ⟨(G_fiber _ _).mpr (by norm_num [scalar]),?_⟩
  intro x hx
  norm_num only [fiberObjective,Gf,quadratic,scalar,zero_pow,zero_add]
  nlinarith [sq_nonneg (x 0)]

theorem G_fiber_minimum_unique (y : V) (x : V)
    (h : IsMinimizer (fiber G y) (fiberObjective Gf y) x) : x=scalar 0 := by
  have hm := h.2 (scalar 0) (G_fiber_minimum y).1
  have he : x 0=0 := by
    norm_num [fiberObjective,Gf,quadratic,scalar] at hm
    nlinarith [sq_nonneg (x 0)]
  ext i
  fin_cases i
  exact he

def G_fixed (y : V) : FixedKKT G Gf (scalar 0) y where
  Df := Gdf (scalar 0,y)
  Dg := Gdg (scalar 0,y)
  lambda := scalar 0
  mu := ![0,0]
  primal := (G_fiber_minimum y).1
  derivative_f := quadratic_derivative _ _
  derivative_g _ := xSquareRow_derivative _ _
  lambda_nonneg := by simp [scalar]
  mu_nonneg := by intro i; fin_cases i <;> norm_num
  soft_compl := by simp [scalar]
  hard_compl := by intro i; fin_cases i <;> simp
  stationarity := by
    ext v
    simp [Gdf,quadraticD,restrict_apply,scalar,Fin.sum_univ_two,Fin.sum_univ_one]

/-- Exactly the fixed-x source family: g and the two X rows. No fixed-y or
Y-domain equality is inserted in this LICQ assertion. -/
def G_active (y : V) : Set (Fin 1 ⊕ Fin 2) :=
  {i | Sum.elim (fun j => soft G y j (scalar 0))
      (fun k => hard G y k (scalar 0)) i=0}

theorem G_active_empty (y : V) : G_active y=∅ := by
  ext i
  cases i with
  | inl j => simp [G_active,soft,G,boxModel,xSquareRow,scalar]
  | inr k => fin_cases k <;>
      norm_num [G_active,hard,linearResidual,G,boxModel,LinearForm,scalar,Fin.sum_univ_one]

theorem G_fixed_LICQ (y : V) : LinearIndependent ℝ
    (fun i : G_active y => Sum.elim (fun j => restrict (Gdg (scalar 0,y) j))
      (fun k => fiberLinearRow G k) i.1) := by
  have : IsEmpty (G_active y) := by
    rw [G_active_empty]
    infer_instance
  exact linearIndependent_empty_type

end Chapter03.OAExec.Article
