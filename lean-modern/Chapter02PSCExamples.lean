module

public import Chapter02PSCOrder
public import Mathlib.Analysis.Calculus.Deriv.Pow
public import Mathlib.Tactic.FinCases

@[expose] public section

/-! Full-model PSC controls, conditional on the S018 source clearance.
Every result concerns the QG-(5)/Grossmann-PL separable subclass and matched
feasible-anchor data. The source-facing qualification adds fiber Slater and
explicit domain normals. No source theorem or solver protocol is certified by
this candidate module; final frozen independent review remains required. -/
noncomputable section
open scoped BigOperators
open Chapter02
namespace Chapter02PSCExamples

def scalar (x : ℝ) : RealVector 1 := fun _ => x

def scalarCoord : RealVector 1 →L[ℝ] ℝ := ContinuousLinearMap.proj 0

@[simp] theorem scalarCoord_apply (x : RealVector 1) : scalarCoord x = x 0 := rfl

def quadratic (A B C : ℝ) (x : RealVector 1) : ℝ := A*(x 0)^2+B*x 0+C

theorem quadratic_derivative (A B C : ℝ) (x : RealVector 1) :
    HasFDerivAt (quadratic A B C) ((2*A*x 0+B) • scalarCoord) x := by
  have h := ((((hasDerivAt_pow 2 (x 0)).comp_hasFDerivAt x
    scalarCoord.hasFDerivAt).const_mul A).add
    (scalarCoord.hasFDerivAt.const_mul B)).add_const C
  convert h using 1 <;> ext z <;>
    simp [quadratic, scalarCoord, Function.comp_def, smul_eq_mul] <;> ring

theorem quadratic_convex (A B C : ℝ) (hA : 0 ≤ A) :
    ConvexOn ℝ Set.univ (quadratic A B C) := by
  refine ⟨convex_univ, ?_⟩
  intro x _ z _ s t hs ht hst
  have hn := mul_nonneg (mul_nonneg (mul_nonneg hA hs) ht) (sq_nonneg (x 0-z 0))
  have ht' : t = 1-s := by linarith
  simp only [quadratic, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  rw [ht'] at hn ⊢
  nlinarith

theorem quadratic_support_identity (A B C : ℝ) (x z : RealVector 1) :
    quadratic A B C z - (quadratic A B C x +
      ((2*A*x 0+B) • scalarCoord) (z-x)) = A*(z 0-x 0)^2 := by
  simp [quadratic, scalarCoord, smul_eq_mul]
  ring

def lin (a : ℝ) : RealVector 1 →L[ℝ] ℝ := a • scalarCoord

@[simp] theorem lin_apply (a : ℝ) (x : RealVector 1) : lin a x = a*x 0 := by
  simp [lin, smul_eq_mul]

def intervalRow (i : Fin 2) : RealVector 1 →L[ℝ] ℝ :=
  if i = 0 then lin (-1) else lin 1

def intervalBound (lo hi : ℝ) (i : Fin 2) : ℝ := if i = 0 then -lo else hi

def singleY (relaxed : Bool) : Set (RealVector 1) :=
  if relaxed then {y | 0 ≤ y 0 ∧ y 0 ≤ 1} else {y | y 0 = 0 ∨ y 0 = 1}

theorem singleY_bounds {relaxed : Bool} {y : RealVector 1} (hy : y ∈ singleY relaxed) :
    0 ≤ y 0 ∧ y 0 ≤ 1 := by
  cases relaxed
  · rcases hy with h | h <;> simp [h]
  · exact hy

@[simp] theorem singleY_zero (relaxed : Bool) : scalar 0 ∈ singleY relaxed := by
  cases relaxed <;> norm_num [singleY, scalar]

@[simp] theorem singleY_one (relaxed : Bool) : scalar 1 ∈ singleY relaxed := by
  cases relaxed <;> norm_num [singleY, scalar]

def doubleY (relaxed : Bool) : Set (RealVector 2) :=
  {y | ∀ i, if relaxed then 0 ≤ y i ∧ y i ≤ 1 else y i = 0 ∨ y i = 1}

def signedY : RealVector 2 →L[ℝ] ℝ :=
  (ContinuousLinearMap.proj (0 : Fin 2) : RealVector 2 →L[ℝ] ℝ) -
    (ContinuousLinearMap.proj (1 : Fin 2) : RealVector 2 →L[ℝ] ℝ)

@[simp] theorem signedY_apply (y : RealVector 2) : signedY y = y 0-y 1 := rfl

theorem doubleY_bounds {relaxed : Bool} {y : RealVector 2} (hy : y ∈ doubleY relaxed) :
    -1 ≤ signedY y ∧ signedY y ≤ 1 := by
  have h0 := hy 0
  have h1 := hy 1
  cases relaxed
  · simp only [Bool.false_eq_true, ↓reduceIte] at h0 h1
    rcases h0 with h0 | h0 <;> rcases h1 with h1 | h1 <;> simp [h0,h1]
  · simp only [↓reduceIte] at h0 h1
    simp only [signedY_apply]
    constructor <;> linarith [h0.1,h0.2,h1.1,h1.2]

def skeleton {p m l s nw : ℕ} (lo hi : ℝ) (Y : Set (RealVector m)) :
    PSCData p 1 m l s nw 2 where
  a := 0
  c := 0
  r := quadratic 0 0 0
  C := fun _ => 0
  D := fun _ => 0
  t := fun _ => quadratic 0 0 0
  E := fun _ => 0
  F := fun _ => 0
  G := fun _ => 0
  b := fun _ => 0
  Wrow := fun _ => 0
  Wbound := fun _ => 0
  Vrow := intervalRow
  Vbound := intervalBound lo hi
  Y := Y

def eModel (relaxed : Bool) : PSCData 0 1 1 1 0 0 2 :=
  { skeleton (-1/4) 1 (singleY relaxed) with
    r := quadratic 1 (-2) 1
    C := fun _ => lin (-1)
    t := fun _ => quadratic 1 1 0 }

def s1Model (relaxed : Bool) : PSCData 1 1 1 1 2 2 2 :=
  { skeleton (p:=1) (m:=1) (l:=1) (s:=2) (nw:=2) (-1) 1 (singleY relaxed) with
    a := lin 1
    c := lin (-1/2)
    r := quadratic 1 0 0
    t := fun _ => quadratic 1 0 (-1/4)
    E := fun i => if i = 0 then 0 else lin 1
    F := fun _ => lin (-1)
    Wrow := intervalRow
    Wbound := intervalBound (-1) 1 }

def s2Model (relaxed : Bool) : PSCData 0 1 1 2 0 0 2 :=
  { skeleton (-1) 1 (singleY relaxed) with
    c := lin (-2)
    r := quadratic 0 1 0
    C := fun i => if i = 0 then 0 else lin 1
    t := fun i => if i = 0 then quadratic 0 (-1) 0 else quadratic 1 1 (-1/2) }

def s2cModel (relaxed : Bool) : PSCData 0 1 1 1 1 0 2 :=
  { skeleton (-1) 1 (singleY relaxed) with
    c := lin (-2)
    r := quadratic 0 1 0
    C := fun _ => lin 1
    t := fun _ => quadratic 1 1 (-1/2)
    G := fun _ => lin (-1) }

def nModel : PSCData 1 1 0 0 0 2 2 :=
  { skeleton (p:=1) (m:=0) (l:=0) (s:=0) (nw:=2) (-1) 1 Set.univ with
    a := lin 1
    r := quadratic 1 0 0
    Wrow := intervalRow
    Wbound := intervalBound 0 1 }

def vModel : PSCData 1 1 0 1 0 2 2 :=
  { skeleton (p:=1) (m:=0) (l:=1) (s:=0) (nw:=2) 0 1 Set.univ with
    a := lin 1
    r := quadratic 1 2 1
    D := fun _ => lin (-1)
    t := fun _ => quadratic 1 0 0
    Wrow := intervalRow
    Wbound := intervalBound (-1) 1 }

def vpModel : PSCData 1 1 0 1 1 2 2 :=
  { skeleton (p:=1) (m:=0) (l:=1) (s:=1) (nw:=2) (-1) 1 Set.univ with
    a := lin 1
    r := quadratic 1 2 1
    D := fun _ => lin (-1)
    t := fun _ => quadratic 1 0 0
    G := fun _ => lin (-1)
    Wrow := intervalRow
    Wbound := intervalBound (-1) 1 }

def hModel (relaxed : Bool) : PSCData 0 1 2 1 2 0 2 :=
  { skeleton (-2) 2 (doubleY relaxed) with
    r := quadratic 1 0 0
    t := fun _ => quadratic 1 0 (-9)
    E := fun i => if i = 0 then (2:ℝ) • signedY else (-2:ℝ) • signedY
    G := fun i => if i = 0 then lin (-1) else lin 1
    b := fun _ => 1 }

def rModel (relaxed : Bool) : PSCData 1 1 1 1 0 2 2 :=
  { skeleton (p:=1) (m:=1) (l:=1) (s:=0) (nw:=2) (-1) 1 (singleY relaxed) with
    a := lin 1
    C := fun _ => lin (-1)
    D := fun _ => lin (-1)
    t := fun _ => quadratic 1 0 0
    Wrow := intervalRow
    Wbound := intervalBound 0 1 }

def anchor0 {p q m l s nw nv : ℕ} (d : PSCData p q m l s nw nv)
    (w : RealVector p) (v : RealVector q) (y : RealVector m)
    (Dr : RealVector q →L[ℝ] ℝ) (Dt : Fin l → RealVector q →L[ℝ] ℝ) : PSCAnchor d where
  w := w
  v := v
  y := y
  Dr := Dr
  Dt := Dt
  lambda := fun _ => 0
  mu := fun _ => 0
  nuW := fun _ => 0
  nuV := fun _ => 0

def eAnchor (relaxed : Bool) : PSCAnchor (eModel relaxed) :=
  { anchor0 (eModel relaxed) 0 (scalar 0) (scalar 0) (lin (-2)) (fun _ => lin 1) with
    lambda := fun _ => 2 }

def s1Anchor (relaxed : Bool) : PSCAnchor (s1Model relaxed) :=
  { anchor0 (s1Model relaxed) (scalar 0) (scalar 0) (scalar 0) (lin 0) (fun _ => lin 0) with
    mu := fun i => if i = 0 then 1 else 0 }

def s2Anchor (relaxed : Bool) : PSCAnchor (s2Model relaxed) :=
  { anchor0 (s2Model relaxed) 0 (scalar 0) (scalar 0) (lin 1)
      (fun i => if i = 0 then lin (-1) else lin 1) with
    lambda := fun i => if i = 0 then 1 else 0 }

def s2cAnchor (relaxed : Bool) : PSCAnchor (s2cModel relaxed) :=
  { anchor0 (s2cModel relaxed) 0 (scalar 0) (scalar 0) (lin 1) (fun _ => lin 1) with
    mu := fun _ => 1 }

def nAnchor : PSCAnchor nModel :=
  { anchor0 nModel (scalar 0) (scalar 0) 0 (lin 0) (fun _ => 0) with
    nuW := fun i => if i = 0 then 1 else 0 }

def vAnchor : PSCAnchor vModel :=
  { anchor0 vModel (scalar 0) (scalar 0) 0 (lin 2) (fun _ => lin 0) with
    lambda := fun _ => 1
    nuV := fun i => if i = 0 then 2 else 0 }

def vpAnchor : PSCAnchor vpModel :=
  { anchor0 vpModel (scalar 0) (scalar 0) 0 (lin 2) (fun _ => lin 0) with
    lambda := fun _ => 1
    mu := fun _ => 2 }

def hAnchor (relaxed positive : Bool) : PSCAnchor (hModel relaxed) :=
  { anchor0 (hModel relaxed) 0 (scalar (if positive then 1 else -1))
      (fun i => if positive then (if i = 0 then 1 else 0) else (if i = 0 then 0 else 1))
      (lin (if positive then 2 else -2)) (fun _ => lin (if positive then 2 else -2)) with
    mu := fun i => if positive then (if i = 0 then 2 else 0) else (if i = 0 then 0 else 2) }

def rAnchor (relaxed : Bool) : PSCAnchor (rModel relaxed) :=
  { anchor0 (rModel relaxed) (scalar 0) (scalar 0) (scalar 0) (lin 0) (fun _ => lin 0) with
    lambda := fun _ => 1 }

macro "psc_numeric" : tactic => `(tactic|
  norm_num [eModel, s1Model, s2Model, s2cModel, nModel, vModel, vpModel, hModel, rModel,
    eAnchor, s1Anchor, s2Anchor, s2cAnchor, nAnchor, vAnchor, vpAnchor, hAnchor, rAnchor,
    skeleton, anchor0, PSCData.W, PSCData.V, affinePolyhedron, PSCData.nonlinear,
    PSCData.coupling, PSCData.objective, PSCAnchor.normalW, PSCAnchor.normalV,
    intervalRow, intervalBound, lin, scalarCoord, scalar, quadratic, doubleY,
    signedY, Fin.forall_fin_succ, Fin.sum_univ_two, Fin.sum_univ_one, smul_eq_mul])

private theorem e_derivatives (relaxed : Bool) :
    HasFDerivAt (eModel relaxed).r (eAnchor relaxed).Dr (eAnchor relaxed).v ∧
    ∀ j, HasFDerivAt ((eModel relaxed).t j) ((eAnchor relaxed).Dt j) (eAnchor relaxed).v := by
  constructor
  ·
    simpa [eModel,eAnchor,anchor0,scalar,lin] using quadratic_derivative 1 (-2) 1 (scalar 0)
  ·
    intro j
    simpa [eModel,eAnchor,anchor0,scalar,lin] using quadratic_derivative 1 1 0 (scalar 0)

theorem e_kkt (relaxed : Bool) : PSCKKT (eModel relaxed) (eAnchor relaxed) := by
  constructor
  case derivative_r => exact (e_derivatives relaxed).1
  case derivative_t => exact (e_derivatives relaxed).2
  all_goals psc_numeric

private theorem s1_derivatives (relaxed : Bool) :
    HasFDerivAt (s1Model relaxed).r (s1Anchor relaxed).Dr (s1Anchor relaxed).v ∧
    ∀ j, HasFDerivAt ((s1Model relaxed).t j) ((s1Anchor relaxed).Dt j) (s1Anchor relaxed).v := by
  constructor
  ·
    simpa [s1Model,s1Anchor,anchor0,scalar,lin] using quadratic_derivative 1 0 0 (scalar 0)
  ·
    intro j
    simpa [s1Model,s1Anchor,anchor0,scalar,lin] using quadratic_derivative 1 0 (-1/4) (scalar 0)

theorem s1_kkt (relaxed : Bool) : PSCKKT (s1Model relaxed) (s1Anchor relaxed) := by
  constructor
  case derivative_r => exact (s1_derivatives relaxed).1
  case derivative_t => exact (s1_derivatives relaxed).2
  all_goals psc_numeric

theorem s2_kkt (relaxed : Bool) : PSCKKT (s2Model relaxed) (s2Anchor relaxed) := by
  constructor
  case derivative_r =>
    simpa [s2Model,s2Anchor,anchor0,scalar,lin] using quadratic_derivative 0 1 0 (scalar 0)
  case derivative_t =>
    intro j
    fin_cases j
    · simpa [s2Model,s2Anchor,anchor0,scalar,lin] using quadratic_derivative 0 (-1) 0 (scalar 0)
    · simpa [s2Model,s2Anchor,anchor0,scalar,lin] using quadratic_derivative 1 1 (-1/2) (scalar 0)
  all_goals psc_numeric

theorem s2c_kkt (relaxed : Bool) : PSCKKT (s2cModel relaxed) (s2cAnchor relaxed) := by
  constructor
  case derivative_r =>
    simpa [s2cModel,s2cAnchor,anchor0,scalar,lin] using quadratic_derivative 0 1 0 (scalar 0)
  case derivative_t =>
    intro j
    simpa [s2cModel,s2cAnchor,anchor0,scalar,lin] using quadratic_derivative 1 1 (-1/2) (scalar 0)
  all_goals psc_numeric

theorem n_kkt : PSCKKT nModel nAnchor := by
  constructor
  case derivative_r =>
    simpa [nModel,nAnchor,anchor0,scalar,lin] using quadratic_derivative 1 0 0 (scalar 0)
  case derivative_t => intro j; exact Fin.elim0 j
  all_goals psc_numeric

theorem v_kkt : PSCKKT vModel vAnchor := by
  constructor
  case derivative_r =>
    simpa [vModel,vAnchor,anchor0,scalar,lin] using quadratic_derivative 1 2 1 (scalar 0)
  case derivative_t =>
    intro j
    simpa [vModel,vAnchor,anchor0,scalar,lin] using quadratic_derivative 1 0 0 (scalar 0)
  all_goals psc_numeric

theorem vp_kkt : PSCKKT vpModel vpAnchor := by
  constructor
  case derivative_r =>
    simpa [vpModel,vpAnchor,anchor0,scalar,lin] using quadratic_derivative 1 2 1 (scalar 0)
  case derivative_t =>
    intro j
    simpa [vpModel,vpAnchor,anchor0,scalar,lin] using quadratic_derivative 1 0 0 (scalar 0)
  all_goals psc_numeric

private theorem h_derivatives (relaxed positive : Bool) :
    HasFDerivAt (hModel relaxed).r (hAnchor relaxed positive).Dr (hAnchor relaxed positive).v ∧
    ∀ j, HasFDerivAt ((hModel relaxed).t j) ((hAnchor relaxed positive).Dt j)
      (hAnchor relaxed positive).v := by
  constructor
  ·
    have h := quadratic_derivative 1 0 0 (scalar (if positive then 1 else -1))
    cases positive <;> simpa [hModel,hAnchor,anchor0,scalar,lin] using h
  ·
    intro j
    have h := quadratic_derivative 1 0 (-9) (scalar (if positive then 1 else -1))
    cases positive <;> simpa [hModel,hAnchor,anchor0,scalar,lin] using h

private theorem h_anchor_y_mem (b positive : Bool) :
    (hAnchor b positive).y ∈ (hModel b).Y := by
  cases positive <;> psc_numeric

private theorem h_stationarity_v (b positive : Bool) (dv : RealVector 1) :
    (hAnchor b positive).Dr dv +
      (∑ j, (hAnchor b positive).lambda j * (hAnchor b positive).Dt j dv) +
      (∑ i, (hAnchor b positive).mu i * (hModel b).G i dv) +
      (hAnchor b positive).normalV dv = 0 := by
  cases positive <;> psc_numeric

private theorem h_kkt_positive (relaxed : Bool) :
    PSCKKT (hModel relaxed) (hAnchor relaxed true) := by
  constructor
  case derivative_r => exact (h_derivatives relaxed true).1
  case derivative_t => exact (h_derivatives relaxed true).2
  case y_mem => exact h_anchor_y_mem relaxed true
  case stationarity_v => exact h_stationarity_v relaxed true
  all_goals psc_numeric

private theorem h_kkt_negative (relaxed : Bool) :
    PSCKKT (hModel relaxed) (hAnchor relaxed false) := by
  constructor
  case derivative_r => exact (h_derivatives relaxed false).1
  case derivative_t => exact (h_derivatives relaxed false).2
  case y_mem => exact h_anchor_y_mem relaxed false
  case stationarity_v => exact h_stationarity_v relaxed false
  case w_mem => intro i; exact Fin.elim0 i
  case lambda_nonneg => intro i; exact le_rfl
  case mu_nonneg => intro i; fin_cases i <;> norm_num [hAnchor]
  case nuW_nonneg => intro i; exact Fin.elim0 i
  case nuV_nonneg => intro i; exact le_rfl
  case nonlinear_complementarity => intro i; exact zero_mul _
  case w_complementarity => intro i; exact Fin.elim0 i
  case v_complementarity => intro i; exact zero_mul _
  all_goals psc_numeric

theorem h_kkt (relaxed positive : Bool) :
    PSCKKT (hModel relaxed) (hAnchor relaxed positive) := by
  cases positive
  · exact h_kkt_negative relaxed
  · exact h_kkt_positive relaxed

theorem r_kkt (relaxed : Bool) : PSCKKT (rModel relaxed) (rAnchor relaxed) := by
  constructor
  case derivative_r =>
    simpa [rModel,rAnchor,anchor0,skeleton,scalar,lin] using quadratic_derivative 0 0 0 (scalar 0)
  case derivative_t =>
    intro j
    simpa [rModel,rAnchor,anchor0,scalar,lin] using quadratic_derivative 1 0 0 (scalar 0)
  all_goals psc_numeric

theorem domainV_convex {p q m l s nw nv : ℕ} (d : PSCData p q m l s nw nv) :
    Convex ℝ d.V := by
  intro x hx z hz a b ha hb hab i
  change d.Vrow i (a • x + b • z) ≤ d.Vbound i
  simp only [map_add, map_smul, smul_eq_mul]
  calc
    a*d.Vrow i x+b*d.Vrow i z ≤ a*d.Vbound i+b*d.Vbound i :=
      add_le_add (mul_le_mul_of_nonneg_left (hx i) ha) (mul_le_mul_of_nonneg_left (hz i) hb)
    _ = d.Vbound i := by rw [← add_mul, hab, one_mul]

theorem quadratic_on_domain {p m l s nw nv : ℕ} (d : PSCData p 1 m l s nw nv)
    (A B C : ℝ) (hA : 0 ≤ A) : ConvexOn ℝ d.V (quadratic A B C) :=
  (quadratic_convex A B C hA).subset (Set.subset_univ _) (domainV_convex d)

def ControlConvex {p q m l s nw nv : ℕ} (d : PSCData p q m l s nw nv) : Prop :=
  ConvexOn ℝ d.V d.r ∧ ∀ j, ConvexOn ℝ d.V (d.t j)

theorem e_convex (relaxed : Bool) : ControlConvex (eModel relaxed) :=
  ⟨quadratic_on_domain _ 1 (-2) 1 (by norm_num),
    fun _ => quadratic_on_domain _ 1 1 0 (by norm_num)⟩

theorem s1_convex (relaxed : Bool) : ControlConvex (s1Model relaxed) :=
  ⟨quadratic_on_domain _ 1 0 0 (by norm_num),
    fun _ => quadratic_on_domain _ 1 0 (-1/4) (by norm_num)⟩

theorem s2_convex (relaxed : Bool) : ControlConvex (s2Model relaxed) := by
  refine ⟨quadratic_on_domain _ 0 1 0 (by norm_num), ?_⟩
  intro j
  fin_cases j
  · exact quadratic_on_domain _ 0 (-1) 0 (by norm_num)
  · exact quadratic_on_domain _ 1 1 (-1/2) (by norm_num)

theorem s2c_convex (relaxed : Bool) : ControlConvex (s2cModel relaxed) :=
  ⟨quadratic_on_domain _ 0 1 0 (by norm_num),
    fun _ => quadratic_on_domain _ 1 1 (-1/2) (by norm_num)⟩

theorem n_convex : ControlConvex nModel :=
  ⟨quadratic_on_domain _ 1 0 0 (by norm_num), fun j => Fin.elim0 j⟩

theorem v_convex : ControlConvex vModel :=
  ⟨quadratic_on_domain _ 1 2 1 (by norm_num),
    fun _ => quadratic_on_domain _ 1 0 0 (by norm_num)⟩

theorem vp_convex : ControlConvex vpModel :=
  ⟨quadratic_on_domain _ 1 2 1 (by norm_num),
    fun _ => quadratic_on_domain _ 1 0 0 (by norm_num)⟩

theorem h_convex (relaxed : Bool) : ControlConvex (hModel relaxed) :=
  ⟨quadratic_on_domain _ 1 0 0 (by norm_num),
    fun _ => quadratic_on_domain _ 1 0 (-9) (by norm_num)⟩

theorem r_convex (relaxed : Bool) : ControlConvex (rModel relaxed) :=
  ⟨quadratic_on_domain _ 0 0 0 (by norm_num),
    fun _ => quadratic_on_domain _ 1 0 0 (by norm_num)⟩

def ControlSlater {p q m l s nw nv : ℕ} (d : PSCData p q m l s nw nv)
    (e : PSCAnchor d) : Prop :=
  ∃ z ∈ d.affineFiber e.y, ∀ j, d.fiberNonlinear e.y j z < 0

theorem e_slater (relaxed : Bool) : ControlSlater (eModel relaxed) (eAnchor relaxed) := by
  refine ⟨weightedInsert 0 (scalar (-1/8)), ?_, ?_⟩
  · rw [PSCData.affineFiber_insert_iff]; psc_numeric
  · intro j; rw [PSCData.fiberNonlinear_insert]; psc_numeric

theorem s1_slater (relaxed : Bool) : ControlSlater (s1Model relaxed) (s1Anchor relaxed) := by
  refine ⟨weightedInsert (scalar (1/2)) (scalar 0), ?_, ?_⟩
  · rw [PSCData.affineFiber_insert_iff]; psc_numeric
  · intro j; rw [PSCData.fiberNonlinear_insert]; psc_numeric

theorem s2_slater (relaxed : Bool) : ControlSlater (s2Model relaxed) (s2Anchor relaxed) := by
  refine ⟨weightedInsert 0 (scalar (1/8)), ?_, ?_⟩
  · rw [PSCData.affineFiber_insert_iff]; psc_numeric
  · intro j; rw [PSCData.fiberNonlinear_insert]; fin_cases j <;> psc_numeric

theorem s2c_slater (relaxed : Bool) : ControlSlater (s2cModel relaxed) (s2cAnchor relaxed) := by
  refine ⟨weightedInsert 0 (scalar (1/8)), ?_, ?_⟩
  · rw [PSCData.affineFiber_insert_iff]; psc_numeric
  · intro j; rw [PSCData.fiberNonlinear_insert]; psc_numeric

theorem n_slater : ControlSlater nModel nAnchor := by
  refine ⟨weightedInsert (scalar (1/2)) (scalar 0), ?_, ?_⟩
  · rw [PSCData.affineFiber_insert_iff]; psc_numeric
  · intro j; exact Fin.elim0 j

theorem v_slater : ControlSlater vModel vAnchor := by
  refine ⟨weightedInsert (scalar (1/2)) (scalar (1/4)), ?_, ?_⟩
  · rw [PSCData.affineFiber_insert_iff]; psc_numeric
  · intro j; rw [PSCData.fiberNonlinear_insert]; psc_numeric

theorem vp_slater : ControlSlater vpModel vpAnchor := by
  refine ⟨weightedInsert (scalar (1/2)) (scalar (1/4)), ?_, ?_⟩
  · rw [PSCData.affineFiber_insert_iff]; psc_numeric
  · intro j; rw [PSCData.fiberNonlinear_insert]; psc_numeric

theorem h_slater (relaxed positive : Bool) :
    ControlSlater (hModel relaxed) (hAnchor relaxed positive) := by
  refine ⟨weightedInsert 0 (scalar (if positive then 3/2 else -3/2)), ?_, ?_⟩
  · rw [PSCData.affineFiber_insert_iff]; cases positive <;> psc_numeric
  · intro j; rw [PSCData.fiberNonlinear_insert]; cases positive <;> psc_numeric

theorem r_slater (relaxed : Bool) : ControlSlater (rModel relaxed) (rAnchor relaxed) := by
  refine ⟨weightedInsert (scalar (1/2)) (scalar 0), ?_, ?_⟩
  · rw [PSCData.affineFiber_insert_iff]; psc_numeric
  · intro j; rw [PSCData.fiberNonlinear_insert]; psc_numeric

def eEntry (b : Bool) : PSCEntry (eModel b) := ⟨eAnchor b,e_kkt b⟩
def s1Entry (b : Bool) : PSCEntry (s1Model b) := ⟨s1Anchor b,s1_kkt b⟩
def s2Entry (b : Bool) : PSCEntry (s2Model b) := ⟨s2Anchor b,s2_kkt b⟩
def s2cEntry (b : Bool) : PSCEntry (s2cModel b) := ⟨s2cAnchor b,s2c_kkt b⟩
def nEntry : PSCEntry nModel := ⟨nAnchor,n_kkt⟩
def vEntry : PSCEntry vModel := ⟨vAnchor,v_kkt⟩
def vpEntry : PSCEntry vpModel := ⟨vpAnchor,vp_kkt⟩
def hEntry (b positive : Bool) : PSCEntry (hModel b) := ⟨hAnchor b positive,h_kkt b positive⟩
def rEntry (b : Bool) : PSCEntry (rModel b) := ⟨rAnchor b,r_kkt b⟩

def ControlReady {p q m l s nw nv : ℕ} (d : PSCData p q m l s nw nv)
    (e : PSCEntry d) : Prop :=
  ControlConvex d ∧ ControlSlater d e.data ∧
    IsMinimizer (d.fiberFeasible e.data.y) (d.fiberObjective e.data.y)
      (weightedInsert e.data.w e.data.v)

theorem e_full_model (b : Bool) : ControlReady (eModel b) (eEntry b) :=
  ⟨e_convex b,e_slater b,psc_kkt_sufficient_fixed_minimum _ _ (e_convex b).1 (e_convex b).2⟩
theorem s1_full_model (b : Bool) : ControlReady (s1Model b) (s1Entry b) :=
  ⟨s1_convex b,s1_slater b,psc_kkt_sufficient_fixed_minimum _ _ (s1_convex b).1 (s1_convex b).2⟩
theorem s2_full_model (b : Bool) : ControlReady (s2Model b) (s2Entry b) :=
  ⟨s2_convex b,s2_slater b,psc_kkt_sufficient_fixed_minimum _ _ (s2_convex b).1 (s2_convex b).2⟩
theorem s2c_full_model (b : Bool) : ControlReady (s2cModel b) (s2cEntry b) :=
  ⟨s2c_convex b,s2c_slater b,psc_kkt_sufficient_fixed_minimum _ _ (s2c_convex b).1 (s2c_convex b).2⟩
theorem n_full_model : ControlReady nModel nEntry :=
  ⟨n_convex,n_slater,psc_kkt_sufficient_fixed_minimum _ _ n_convex.1 n_convex.2⟩
theorem v_full_model : ControlReady vModel vEntry :=
  ⟨v_convex,v_slater,psc_kkt_sufficient_fixed_minimum _ _ v_convex.1 v_convex.2⟩
theorem vp_full_model : ControlReady vpModel vpEntry :=
  ⟨vp_convex,vp_slater,psc_kkt_sufficient_fixed_minimum _ _ vp_convex.1 vp_convex.2⟩
theorem h_full_model (b positive : Bool) : ControlReady (hModel b) (hEntry b positive) :=
  ⟨h_convex b,h_slater b positive,psc_kkt_sufficient_fixed_minimum _ _ (h_convex b).1 (h_convex b).2⟩
theorem r_full_model (b : Bool) : ControlReady (rModel b) (rEntry b) :=
  ⟨r_convex b,r_slater b,psc_kkt_sufficient_fixed_minimum _ _ (r_convex b).1 (r_convex b).2⟩

def pt0 (v y beta alpha : ℝ) : PSCPoint 0 1 1 := ⟨0,scalar v,scalar y,beta,alpha⟩
def pt1 (w v y beta alpha : ℝ) : PSCPoint 1 1 1 := ⟨scalar w,scalar v,scalar y,beta,alpha⟩
def ptN (w v beta alpha : ℝ) : PSCPoint 1 1 0 := ⟨scalar w,scalar v,0,beta,alpha⟩
def ptH (v y1 y2 beta : ℝ) : PSCPoint 0 1 2 :=
  ⟨0,scalar v,(fun i => if i = 0 then y1 else y2),beta,beta⟩

macro "master_numeric" : tactic => `(tactic|
  (simp only [pscMaster, pscOAMaster, pscGBDMaster, pscPointBase, PSCData.base,
    pscRow, pscGBDRow, pscOARows, pscObjectiveTangent, pscConstraintTangent,
    eEntry,s1Entry,s2Entry,s2cEntry,nEntry,vEntry,vpEntry,hEntry,rEntry,
    pt0,pt1,ptN,ptH,Set.mem_setOf_eq,List.mem_singleton,List.mem_cons,List.not_mem_nil,
    or_false,forall_eq,forall_eq_or_imp]
   psc_numeric))

theorem e_psc_row (b : Bool) (w : RealVector 0) (v y : RealVector 1) :
    pscRow (eModel b) (eAnchor b) w v y = 1-2*y 0 := by
  unfold pscRow; psc_numeric; ring
theorem e_gbd_row (b : Bool) (y : RealVector 1) :
    pscGBDRow (eModel b) (eAnchor b) y = 1-2*y 0 := by
  unfold pscGBDRow; psc_numeric; ring
theorem s1_psc_row (b : Bool) (w v y : RealVector 1) :
    pscRow (s1Model b) (s1Anchor b) w v y = 0 := by unfold pscRow; psc_numeric
theorem s1_gbd_row (b : Bool) (y : RealVector 1) :
    pscGBDRow (s1Model b) (s1Anchor b) y = -(y 0)/2 := by
  unfold pscGBDRow; psc_numeric; ring
theorem s2_psc_row (b : Bool) (w : RealVector 0) (v y : RealVector 1) :
    pscRow (s2Model b) (s2Anchor b) w v y = 0 := by unfold pscRow; psc_numeric
theorem s2c_psc_row (b : Bool) (w : RealVector 0) (v y : RealVector 1) :
    pscRow (s2cModel b) (s2cAnchor b) w v y = v 0 := by unfold pscRow; psc_numeric
theorem s2_gbd_row (b : Bool) (y : RealVector 1) :
    pscGBDRow (s2Model b) (s2Anchor b) y = -2*y 0 := by unfold pscGBDRow; psc_numeric
theorem s2c_gbd_row (b : Bool) (y : RealVector 1) :
    pscGBDRow (s2cModel b) (s2cAnchor b) y = -2*y 0 := by unfold pscGBDRow; psc_numeric
theorem n_psc_row (w v : RealVector 1) (y : RealVector 0) :
    pscRow nModel nAnchor w v y = 0 := by unfold pscRow; psc_numeric
theorem n_gbd_row (y : RealVector 0) : pscGBDRow nModel nAnchor y = 0 := by
  unfold pscGBDRow; psc_numeric
theorem v_psc_row (w v : RealVector 1) (y : RealVector 0) :
    pscRow vModel vAnchor w v y = 1-w 0 := by unfold pscRow; psc_numeric; ring
theorem vp_psc_row (w v : RealVector 1) (y : RealVector 0) :
    pscRow vpModel vpAnchor w v y = 1-w 0+2*v 0 := by unfold pscRow; psc_numeric; ring
theorem v_gbd_row (y : RealVector 0) : pscGBDRow vModel vAnchor y = 1 := by
  unfold pscGBDRow; psc_numeric
theorem vp_gbd_row (y : RealVector 0) : pscGBDRow vpModel vpAnchor y = 1 := by
  unfold pscGBDRow; psc_numeric
theorem h_psc_row (b positive : Bool) (w : RealVector 0) (v : RealVector 1) (y : RealVector 2) :
    pscRow (hModel b) (hAnchor b positive) w v y = (if positive then 2*v 0-1 else -2*v 0-1) := by
  unfold pscRow; cases positive <;> psc_numeric <;> ring
theorem h_gbd_row (b positive : Bool) (y : RealVector 2) :
    pscGBDRow (hModel b) (hAnchor b positive) y =
      (if positive then 4*signedY y-3 else -4*signedY y-3) := by
  unfold pscGBDRow; cases positive <;> psc_numeric <;> ring
theorem r_psc_row (b : Bool) (w v y : RealVector 1) :
    pscRow (rModel b) (rAnchor b) w v y = -w 0-y 0 := by
  unfold pscRow; psc_numeric; ring
theorem r_gbd_row (b : Bool) (y : RealVector 1) :
    pscGBDRow (rModel b) (rAnchor b) y = -y 0 := by unfold pscGBDRow; psc_numeric

private theorem psc_minimum_from_gbd {p q m l s nw nv : ℕ}
    (d : PSCData p q m l s nw nv) (H : List (PSCEntry d))
    {g : RealVector m × ℝ} {z : PSCPoint p q m}
    (hg : IsMinimizer (pscGBDMaster d H) Prod.snd g)
    (hz : z ∈ pscMaster d H) (hvalue : z.alpha = g.2) :
    IsMinimizer (pscMaster d H) PSCPoint.alpha z := by
  refine ⟨hz,?_⟩
  intro x hx
  rw [hvalue]
  exact hg.2 (x.y,x.alpha) (psc_projected_subset_gbd d H ⟨x,hx,rfl,rfl⟩)

private theorem oa_minimum_from_psc {p q m l s nw nv : ℕ}
    (d : PSCData p q m l s nw nv) (H : List (PSCEntry d))
    {z : PSCPoint p q m} (hz : IsMinimizer (pscMaster d H) PSCPoint.alpha z)
    (ho : z ∈ pscOAMaster d H) :
    IsMinimizer (pscOAMaster d H) PSCPoint.alpha z :=
  ⟨ho,fun x hx => hz.2 x (psc_oa_subset d H hx)⟩

theorem e_gbd_minimum (b : Bool) :
    IsMinimizer (pscGBDMaster (eModel b) [eEntry b]) Prod.snd (scalar 1,-1) := by
  refine ⟨?_,?_⟩
  · master_numeric
  · intro x hx
    have hb := hx.2 (eEntry b) (by simp)
    rw [show (eEntry b).data=eAnchor b from rfl, e_gbd_row] at hb
    have hy := singleY_bounds hx.1
    change -1 ≤ x.2
    linarith [hy.2]

theorem e_master_minima (b : Bool) :
    IsMinimizer (pscMaster (eModel b) [eEntry b]) PSCPoint.alpha (pt0 1 1 (-1) (-1)) ∧
    IsMinimizer (pscOAMaster (eModel b) [eEntry b]) PSCPoint.alpha (pt0 1 1 (-1) (-1)) := by
  have ho : pt0 1 1 (-1) (-1) ∈ pscOAMaster (eModel b) [eEntry b] := by master_numeric
  have hp := psc_minimum_from_gbd (eModel b) [eEntry b] (e_gbd_minimum b)
    (psc_oa_subset _ _ ho) rfl
  exact ⟨hp,oa_minimum_from_psc _ _ hp ho⟩

theorem s1_gbd_minimum (b : Bool) :
    IsMinimizer (pscGBDMaster (s1Model b) [s1Entry b]) Prod.snd (scalar 1,-1/2) := by
  refine ⟨?_,?_⟩
  · master_numeric
  · intro x hx
    have hb := hx.2 (s1Entry b) (by simp)
    rw [show (s1Entry b).data=s1Anchor b from rfl, s1_gbd_row] at hb
    have hy := singleY_bounds hx.1
    change -1/2 ≤ x.2
    linarith [hy.2]

theorem s1_psc_lower (b : Bool) (x : PSCPoint 1 1 1)
    (hx : x ∈ pscMaster (s1Model b) [s1Entry b]) : 0 ≤ x.alpha := by
  have hb := hx.2 (s1Entry b) (by simp)
  rw [show (s1Entry b).data=s1Anchor b from rfl,s1_psc_row] at hb
  have hy := singleY_bounds hx.1.1.2.2.1
  have hl := hx.1.1.2.2.2 (1 : Fin 2)
  have he := hx.1.2
  norm_num [s1Model,skeleton,PSCData.coupling] at hl he
  linarith [hy.1]

theorem s1_master_minima (b : Bool) :
    IsMinimizer (pscMaster (s1Model b) [s1Entry b]) PSCPoint.alpha (pt1 0 0 0 0 0) ∧
    IsMinimizer (pscOAMaster (s1Model b) [s1Entry b]) PSCPoint.alpha (pt1 0 0 0 0 0) := by
  have ho : pt1 0 0 0 0 0 ∈ pscOAMaster (s1Model b) [s1Entry b] := by master_numeric
  have hp : IsMinimizer (pscMaster (s1Model b) [s1Entry b]) PSCPoint.alpha (pt1 0 0 0 0 0) :=
    ⟨psc_oa_subset _ _ ho,fun x hx => s1_psc_lower b x hx⟩
  exact ⟨hp,oa_minimum_from_psc _ _ hp ho⟩

theorem s2_gbd_minimum (b : Bool) :
    IsMinimizer (pscGBDMaster (s2Model b) [s2Entry b]) Prod.snd (scalar 1,-2) := by
  refine ⟨?_,?_⟩
  · master_numeric
  · intro x hx
    have hb := hx.2 (s2Entry b) (by simp)
    rw [show (s2Entry b).data=s2Anchor b from rfl, s2_gbd_row] at hb
    have hy := singleY_bounds hx.1
    change -2 ≤ x.2
    linarith [hy.2]

theorem s2c_gbd_minimum (b : Bool) :
    IsMinimizer (pscGBDMaster (s2cModel b) [s2cEntry b]) Prod.snd (scalar 1,-2) := by
  refine ⟨?_,?_⟩
  · master_numeric
  · intro x hx
    have hb := hx.2 (s2cEntry b) (by simp)
    rw [show (s2cEntry b).data=s2cAnchor b from rfl, s2c_gbd_row] at hb
    have hy := singleY_bounds hx.1
    change -2 ≤ x.2
    linarith [hy.2]

theorem s2_psc_minimum (b : Bool) :
    IsMinimizer (pscMaster (s2Model b) [s2Entry b]) PSCPoint.alpha (pt0 0 1 0 (-2)) := by
  apply psc_minimum_from_gbd _ _ (s2_gbd_minimum b) ?_ rfl
  master_numeric

theorem s2c_psc_minimum (b : Bool) :
    IsMinimizer (pscMaster (s2cModel b) [s2cEntry b]) PSCPoint.alpha (pt0 0 1 0 (-2)) := by
  apply psc_minimum_from_gbd _ _ (s2c_gbd_minimum b) ?_ rfl
  master_numeric

theorem s2_oa_bounds (b : Bool) (x : PSCPoint 0 1 1)
    (hx : x ∈ pscOAMaster (s2Model b) [s2Entry b]) :
    0 ≤ x.v 0 ∧ x.v 0+x.y 0 ≤ 1/2 ∧ x.v 0 ≤ x.beta ∧
      x.alpha = -2*x.y 0+x.beta := by
  have h := hx.2 (s2Entry b) (by simp)
  have h0 := h.2 (0 : Fin 2)
  have h1 := h.2 (1 : Fin 2)
  have ho := h.1
  have he := hx.1.2
  norm_num [pscOARows,pscObjectiveTangent,pscConstraintTangent,s2Entry,s2Anchor,anchor0,
    s2Model,skeleton,PSCData.nonlinear,quadratic,scalar] at h0 h1 ho he
  exact ⟨by linarith,by linarith,ho,by linarith⟩

theorem s2c_oa_bounds (b : Bool) (x : PSCPoint 0 1 1)
    (hx : x ∈ pscOAMaster (s2cModel b) [s2cEntry b]) :
    0 ≤ x.v 0 ∧ x.v 0+x.y 0 ≤ 1/2 ∧ x.v 0 ≤ x.beta ∧
      x.alpha = -2*x.y 0+x.beta := by
  have h := hx.2 (s2cEntry b) (by simp)
  have h0 := hx.1.1.2.2.2 (0 : Fin 1)
  have h1 := h.2 (0 : Fin 1)
  have ho := h.1
  have he := hx.1.2
  norm_num [pscOARows,pscObjectiveTangent,pscConstraintTangent,s2cEntry,s2cAnchor,anchor0,
    s2cModel,skeleton,PSCData.nonlinear,PSCData.coupling,quadratic,scalar] at h0 h1 ho he
  exact ⟨by linarith,by linarith,ho,by linarith⟩

theorem s2_binary_oa_minimum :
    IsMinimizer (pscOAMaster (s2Model false) [s2Entry false]) PSCPoint.alpha (pt0 0 0 0 0) := by
  refine ⟨by master_numeric,?_⟩
  intro x hx
  have h := s2_oa_bounds false x hx
  have hy : x.y 0=0 ∨ x.y 0=1 := hx.1.1.2.2.1
  change 0 ≤ x.alpha
  rcases hy with hy | hy <;> linarith [h.1,h.2.1,h.2.2.1,h.2.2.2]

theorem s2c_binary_oa_minimum :
    IsMinimizer (pscOAMaster (s2cModel false) [s2cEntry false]) PSCPoint.alpha (pt0 0 0 0 0) := by
  refine ⟨by master_numeric,?_⟩
  intro x hx
  have h := s2c_oa_bounds false x hx
  have hy : x.y 0=0 ∨ x.y 0=1 := hx.1.1.2.2.1
  change 0 ≤ x.alpha
  rcases hy with hy | hy <;> linarith [h.1,h.2.1,h.2.2.1,h.2.2.2]

theorem s2_continuous_oa_minimum :
    IsMinimizer (pscOAMaster (s2Model true) [s2Entry true]) PSCPoint.alpha (pt0 0 (1/2) 0 (-1)) := by
  refine ⟨?_,?_⟩
  · master_numeric; norm_num [singleY,scalar]
  · intro x hx
    have h := s2_oa_bounds true x hx
    change -1 ≤ x.alpha
    linarith [h.1,h.2.1,h.2.2.1,h.2.2.2]

theorem s2c_continuous_oa_minimum :
    IsMinimizer (pscOAMaster (s2cModel true) [s2cEntry true]) PSCPoint.alpha (pt0 0 (1/2) 0 (-1)) := by
  refine ⟨?_,?_⟩
  · master_numeric; norm_num [singleY,scalar]
  · intro x hx
    have h := s2c_oa_bounds true x hx
    change -1 ≤ x.alpha
    linarith [h.1,h.2.1,h.2.2.1,h.2.2.2]

theorem n_gbd_minimum :
    IsMinimizer (pscGBDMaster nModel [nEntry]) Prod.snd (0,0) := by
  refine ⟨by master_numeric,?_⟩
  intro x hx
  have hb := hx.2 nEntry (by simp)
  change pscGBDRow nModel nAnchor x.1 ≤ x.2 at hb
  simpa only [n_gbd_row] using hb

theorem n_master_minima :
    IsMinimizer (pscMaster nModel [nEntry]) PSCPoint.alpha (ptN 0 0 0 0) ∧
    IsMinimizer (pscOAMaster nModel [nEntry]) PSCPoint.alpha (ptN 0 0 0 0) := by
  have ho : ptN 0 0 0 0 ∈ pscOAMaster nModel [nEntry] := by master_numeric
  have hp := psc_minimum_from_gbd nModel [nEntry] n_gbd_minimum (psc_oa_subset _ _ ho) rfl
  exact ⟨hp,oa_minimum_from_psc _ _ hp ho⟩

theorem v_gbd_minimum :
    IsMinimizer (pscGBDMaster vModel [vEntry]) Prod.snd (0,1) := by
  refine ⟨by master_numeric,?_⟩
  intro x hx
  have hb := hx.2 vEntry (by simp)
  change pscGBDRow vModel vAnchor x.1 ≤ x.2 at hb
  simpa only [v_gbd_row] using hb

theorem v_master_minima :
    IsMinimizer (pscMaster vModel [vEntry]) PSCPoint.alpha (ptN 0 0 1 1) ∧
    IsMinimizer (pscOAMaster vModel [vEntry]) PSCPoint.alpha (ptN 0 0 1 1) := by
  have ho : ptN 0 0 1 1 ∈ pscOAMaster vModel [vEntry] := by master_numeric
  have hp := psc_minimum_from_gbd vModel [vEntry] v_gbd_minimum (psc_oa_subset _ _ ho) rfl
  exact ⟨hp,oa_minimum_from_psc _ _ hp ho⟩

theorem vp_gbd_minimum :
    IsMinimizer (pscGBDMaster vpModel [vpEntry]) Prod.snd (0,1) := by
  refine ⟨by master_numeric,?_⟩
  intro x hx
  have hb := hx.2 vpEntry (by simp)
  change pscGBDRow vpModel vpAnchor x.1 ≤ x.2 at hb
  simpa only [vp_gbd_row] using hb

theorem vp_master_minima :
    IsMinimizer (pscMaster vpModel [vpEntry]) PSCPoint.alpha (ptN 0 0 1 1) ∧
    IsMinimizer (pscOAMaster vpModel [vpEntry]) PSCPoint.alpha (ptN 0 0 1 1) := by
  have ho : ptN 0 0 1 1 ∈ pscOAMaster vpModel [vpEntry] := by master_numeric
  have hp := psc_minimum_from_gbd vpModel [vpEntry] vp_gbd_minimum (psc_oa_subset _ _ ho) rfl
  exact ⟨hp,oa_minimum_from_psc _ _ hp ho⟩

theorem h_gbd_minimum (b : Bool) :
    IsMinimizer (pscGBDMaster (hModel b) [hEntry b true,hEntry b false]) Prod.snd (0,-3) := by
  refine ⟨by master_numeric,?_⟩
  intro x hx
  have hp := hx.2 (hEntry b true) (by simp)
  have hn := hx.2 (hEntry b false) (by simp)
  change pscGBDRow (hModel b) (hAnchor b true) x.1 ≤ x.2 at hp
  change pscGBDRow (hModel b) (hAnchor b false) x.1 ≤ x.2 at hn
  rw [h_gbd_row] at hp hn
  simp only [Bool.false_eq_true, ↓reduceIte] at hp hn
  change -3 ≤ x.2
  linarith

theorem h_psc_lower (b : Bool) (x : PSCPoint 0 1 2)
    (hx : x ∈ pscMaster (hModel b) [hEntry b true,hEntry b false]) : -1 ≤ x.alpha := by
  have hp := hx.2 (hEntry b true) (by simp)
  have hn := hx.2 (hEntry b false) (by simp)
  change pscRow (hModel b) (hAnchor b true) x.w x.v x.y ≤ x.beta at hp
  change pscRow (hModel b) (hAnchor b false) x.w x.v x.y ≤ x.beta at hn
  rw [h_psc_row] at hp hn
  simp only [Bool.false_eq_true, ↓reduceIte] at hp hn
  have he := hx.1.2
  norm_num [hModel,skeleton] at he
  linarith

theorem h_master_minima (b : Bool) :
    IsMinimizer (pscMaster (hModel b) [hEntry b true,hEntry b false]) PSCPoint.alpha (ptH 0 0 0 (-1)) ∧
    IsMinimizer (pscOAMaster (hModel b) [hEntry b true,hEntry b false]) PSCPoint.alpha (ptH 0 0 0 (-1)) := by
  have ho : ptH 0 0 0 (-1) ∈ pscOAMaster (hModel b) [hEntry b true,hEntry b false] := by master_numeric
  have hp : IsMinimizer (pscMaster (hModel b) [hEntry b true,hEntry b false])
      PSCPoint.alpha (ptH 0 0 0 (-1)) :=
    ⟨psc_oa_subset _ _ ho,fun x hx => h_psc_lower b x hx⟩
  exact ⟨hp,oa_minimum_from_psc _ _ hp ho⟩

theorem r_gbd_minimum (b : Bool) :
    IsMinimizer (pscGBDMaster (rModel b) [rEntry b]) Prod.snd (scalar 1,-1) := by
  refine ⟨by master_numeric,?_⟩
  intro x hx
  have hb := hx.2 (rEntry b) (by simp)
  change pscGBDRow (rModel b) (rAnchor b) x.1 ≤ x.2 at hb
  rw [r_gbd_row] at hb
  have hy := singleY_bounds hx.1
  change -1 ≤ x.2
  linarith [hy.2]

theorem r_psc_minimum (b : Bool) :
    IsMinimizer (pscMaster (rModel b) [rEntry b]) PSCPoint.alpha (pt1 0 0 1 (-1) (-1)) := by
  apply psc_minimum_from_gbd _ _ (r_gbd_minimum b) ?_ rfl
  master_numeric

theorem r_oa_minimum (b : Bool) :
    IsMinimizer (pscOAMaster (rModel b) [rEntry b]) PSCPoint.alpha (pt1 0 0 0 0 0) := by
  refine ⟨by master_numeric,?_⟩
  intro x hx
  have hw := hx.1.1.1 (0 : Fin 2)
  have he := hx.1.2
  have hb := (hx.2 (rEntry b) (by simp)).1
  norm_num [rModel,rAnchor,rEntry,anchor0,skeleton,intervalRow,intervalBound,
    pscObjectiveTangent,quadratic,scalar] at hw he hb
  change 0 ≤ x.alpha
  linarith

theorem r_beta_zero_minimum (b : Bool) :
    IsMinimizer (pscBetaZeroMaster (rModel b) [rEntry b]) PSCPoint.alpha (pt1 0 0 0 0 0) := by
  refine ⟨?_,?_⟩
  · constructor
    · master_numeric
    · rfl
  · intro x hx
    have hw := hx.1.1.1.1 (0 : Fin 2)
    have he := hx.1.1.2
    have hb := hx.2
    norm_num [rModel,skeleton,intervalRow,intervalBound] at hw he
    change 0 ≤ x.alpha
    linarith

theorem e_projected_equality (b : Bool) :
    pscProject (pscMaster (eModel b) [eEntry b]) = pscGBDMaster (eModel b) [eEntry b] := by
  apply Set.Subset.antisymm (psc_projected_subset_gbd _ _)
  intro ya h
  have hc := h.2 (eEntry b) (by simp)
  change pscGBDRow (eModel b) (eAnchor b) ya.1 ≤ ya.2 at hc
  rw [e_gbd_row] at hc
  let z : PSCPoint 0 1 1 := ⟨0,scalar 0,ya.1,ya.2,ya.2⟩
  refine ⟨z,?_,rfl,rfl⟩
  constructor
  · constructor
    · refine ⟨?_,?_,h.1,?_⟩
      · intro i; exact Fin.elim0 i
      · change scalar 0 ∈ (eModel b).V; psc_numeric
      · intro i; exact Fin.elim0 i
    · change ya.2 = (0:ℝ)+0+ya.2
      ring
  · intro e he
    have he' : e=eEntry b := by simpa using he
    subst e
    change pscRow (eModel b) (eAnchor b) 0 (scalar 0) ya.1 ≤ ya.2
    simpa only [e_psc_row] using hc

theorem e_projected_oa_equality (b : Bool) :
    pscProject (pscOAMaster (eModel b) [eEntry b]) = pscGBDMaster (eModel b) [eEntry b] := by
  apply Set.Subset.antisymm
    ((psc_projected_oa_subset (eModel b) [eEntry b]).trans (psc_projected_subset_gbd _ _))
  intro ya h
  have hc := h.2 (eEntry b) (by simp)
  change pscGBDRow (eModel b) (eAnchor b) ya.1 ≤ ya.2 at hc
  rw [e_gbd_row] at hc
  have hy := singleY_bounds h.1
  let z : PSCPoint 0 1 1 := ⟨0,ya.1,ya.1,ya.2,ya.2⟩
  refine ⟨z,?_,rfl,rfl⟩
  constructor
  · constructor
    · refine ⟨?_,?_,h.1,?_⟩
      · intro i; exact Fin.elim0 i
      · change ya.1 ∈ (eModel b).V
        psc_numeric
        exact ⟨by linarith [hy.1],hy.2⟩
      · intro i; exact Fin.elim0 i
    · change ya.2 = (0:ℝ)+0+ya.2
      ring
  · intro e he
    have he' : e=eEntry b := by simpa using he
    subst e
    change pscOARows (eModel b) (eAnchor b) 0 ya.1 ya.1 ya.2
    simp only [pscOARows,pscObjectiveTangent,pscConstraintTangent]
    psc_numeric
    linarith

theorem e_relaxation_optimum_not_original (b : Bool) :
    ¬ (eModel b).feasible 0 (scalar 1) (scalar 1) := by
  intro h
  have hh := h.2 (0 : Fin 1)
  norm_num [eModel,PSCData.nonlinear,skeleton,quadratic,scalar] at hh

theorem s1_strict_projected_gap (b : Bool) :
    (scalar 1,-1/2) ∈ pscGBDMaster (s1Model b) [s1Entry b] ∧
    (scalar 1,-1/2) ∉ pscProject (pscMaster (s1Model b) [s1Entry b]) := by
  refine ⟨(s1_gbd_minimum b).1,?_⟩
  rintro ⟨z,hz,_,ha⟩
  have hl := s1_psc_lower b z hz
  simp only [Prod.snd] at ha
  linarith

theorem s2_strict_projected_gap (b : Bool) :
    (scalar 1,-2) ∈ pscProject (pscMaster (s2Model b) [s2Entry b]) ∧
    (scalar 1,-2) ∉ pscProject (pscOAMaster (s2Model b) [s2Entry b]) := by
  refine ⟨⟨pt0 0 1 0 (-2),(s2_psc_minimum b).1,rfl,rfl⟩,?_⟩
  rintro ⟨z,hz,hy,_⟩
  have hh := s2_oa_bounds b z hz
  have hy0 : z.y 0=1 := congrFun hy 0
  linarith [hh.1,hh.2.1]

theorem s2c_strict_projected_gap (b : Bool) :
    (scalar 1,-2) ∈ pscProject (pscMaster (s2cModel b) [s2cEntry b]) ∧
    (scalar 1,-2) ∉ pscProject (pscOAMaster (s2cModel b) [s2cEntry b]) := by
  refine ⟨⟨pt0 0 1 0 (-2),(s2c_psc_minimum b).1,rfl,rfl⟩,?_⟩
  rintro ⟨z,hz,hy,_⟩
  have hh := s2c_oa_bounds b z hz
  have hy0 : z.y 0=1 := congrFun hy 0
  linarith [hh.1,hh.2.1]

theorem s2_encoding_same_original_feasible (b : Bool) (w : RealVector 0) (v y : RealVector 1) :
    (s2Model b).feasible w v y ↔ (s2cModel b).feasible w v y := by
  simp only [PSCData.feasible,PSCData.base]
  psc_numeric
  tauto

theorem s2_encoding_same_original_objective (b : Bool) (w : RealVector 0) (v y : RealVector 1) :
    (s2Model b).objective w v y = (s2cModel b).objective w v y := rfl

theorem s2_encoding_strict_retained_witness (b : Bool) :
    pt0 (1/2) 1 0 (-2) ∈ pscMaster (s2Model b) [s2Entry b] ∧
    pt0 (1/2) 1 0 (-2) ∉ pscMaster (s2cModel b) [s2cEntry b] := by
  constructor
  · master_numeric
  · intro h
    have hh := h.2 (s2cEntry b) (by simp)
    change pscRow (s2cModel b) (s2cAnchor b) 0 (scalar (1/2)) (scalar 1) ≤ 0 at hh
    rw [s2c_psc_row] at hh
    norm_num [scalar] at hh

theorem n_nonzero_domain_normal : nAnchor.normalW (scalar 1) = -1 := by psc_numeric

theorem n_domain_deletion_witness :
    (scalar (-1) : RealVector 1) ∉ nModel.W ∧
    pscRow nModel nAnchor (scalar (-1)) (scalar 0) 0 ≤ 0 ∧
    (-1:ℝ) = nModel.a (scalar (-1))+nModel.c 0+0 ∧
    (0,-1) ∉ pscGBDMaster nModel [nEntry] := by
  constructor
  · psc_numeric
  refine ⟨?_,?_,?_⟩
  · rw [n_psc_row]
  · norm_num [nModel,skeleton,scalar]
  · intro h
    have hh := (n_gbd_minimum).2 (0,-1) h
    norm_num at hh

theorem v_nonzero_domain_normal : vAnchor.normalV (scalar 1) = -2 := by psc_numeric

theorem v_strict_retained_gap :
    ptN 0 (1/2) 1 1 ∈ pscMaster vModel [vEntry] ∧
    ptN 0 (1/2) 1 1 ∉ pscOAMaster vModel [vEntry] := by
  constructor
  · master_numeric
  · intro h
    have hh := (h.2 vEntry (by simp)).1
    norm_num [pscObjectiveTangent,vEntry,vAnchor,vModel,anchor0,ptN,scalar,quadratic] at hh

theorem v_domain_deletion_witness :
    scalar (-1/2) ∉ vModel.V ∧
    pscOARows vModel vAnchor (scalar 0) (scalar (-1/2)) 0 0 ∧
    ¬ pscRow vModel vAnchor (scalar 0) (scalar (-1/2)) 0 ≤ 0 := by
  constructor
  · psc_numeric
  constructor
  · simp only [pscOARows,pscObjectiveTangent,pscConstraintTangent]; psc_numeric
  · rw [v_psc_row]; norm_num [scalar]

theorem vp_encoding_changes_row (w v : RealVector 1) (y : RealVector 0) :
    pscRow vpModel vpAnchor w v y = pscRow vModel vAnchor w v y + 2*v 0 := by
  rw [vp_psc_row,v_psc_row]

theorem vp_encoding_strict_witness :
    ptN 0 (1/2) 1 1 ∈ pscMaster vModel [vEntry] ∧
    ptN 0 (1/2) 1 1 ∉ pscMaster vpModel [vpEntry] := by
  refine ⟨v_strict_retained_gap.1,?_⟩
  intro h
  have hh := h.2 vpEntry (by simp)
  change pscRow vpModel vpAnchor (scalar 0) (scalar (1/2)) 0 ≤ 1 at hh
  rw [vp_psc_row] at hh
  norm_num [scalar] at hh

theorem vp_same_original_feasible (w v : RealVector 1) (y : RealVector 0) :
    vModel.feasible w v y ↔ vpModel.feasible w v y := by
  simp only [PSCData.feasible,PSCData.base]
  psc_numeric
  intro _ _ _
  constructor
  · rintro ⟨hv0,hv1⟩
    exact ⟨⟨by linarith,hv1⟩,hv0⟩
  · rintro ⟨⟨_,hv1⟩,hv0⟩
    exact ⟨hv0,hv1⟩

theorem vp_same_original_objective (w v : RealVector 1) (y : RealVector 0) :
    vpModel.objective w v y = vModel.objective w v y := rfl

def hRowwise (b : Bool) : Set (RealVector 2 × ℝ) :=
  {ya | ∀ e ∈ [hEntry b true,hEntry b false], ∃ z : PSCPoint 0 1 2,
    pscPointBase (hModel b) z ∧ z.y=ya.1 ∧ z.alpha=ya.2 ∧
      pscRow (hModel b) e.data z.w z.v z.y ≤ z.beta}

theorem h_rowwise_witness (b : Bool) : (0,-3) ∈ hRowwise b := by
  intro e he
  simp only [List.mem_cons,List.not_mem_nil,or_false] at he
  rcases he with he | he
  · subst e
    refine ⟨ptH (-1) 0 0 (-3),?_⟩
    master_numeric
    rfl
  · subst e
    refine ⟨ptH 1 0 0 (-3),?_⟩
    master_numeric
    rfl

theorem h_rowwise_subset_gbd (b : Bool) :
    hRowwise b ⊆ pscGBDMaster (hModel b) [hEntry b true,hEntry b false] := by
  intro ya h
  obtain ⟨z,hz,hy,_,_⟩ := h (hEntry b true) (by simp)
  refine ⟨hy ▸ hz.1.2.2.1,?_⟩
  intro e he
  obtain ⟨x,hx,hxy,hxa,hr⟩ := h e he
  have hb := psc_row_implies_gbd (hModel b) e.data e.kkt x hx hr
  simpa only [hxy,hxa] using hb

theorem h_rowwise_minimum (b : Bool) : IsMinimizer (hRowwise b) Prod.snd (0,-3) :=
  ⟨h_rowwise_witness b,fun ya hya => (h_gbd_minimum b).2 ya (h_rowwise_subset_gbd b hya)⟩

theorem h_shared_witness_strict_gap (b : Bool) :
    (0,-3) ∈ hRowwise b ∧
    (0,-3) ∉ pscProject (pscMaster (hModel b) [hEntry b true,hEntry b false]) := by
  refine ⟨h_rowwise_witness b,?_⟩
  rintro ⟨z,hz,_,ha⟩
  have hl := h_psc_lower b z hz
  simp only [Prod.snd] at ha
  linarith

theorem h_original_attained_zero (b : Bool) :
    (hModel b).feasible 0 (scalar 0) 0 ∧
    (hModel b).objective 0 (scalar 0) 0 = 0 ∧
    ∀ w v y, (hModel b).feasible w v y → 0 ≤ (hModel b).objective w v y := by
  refine ⟨?_,?_,?_⟩
  · simp only [PSCData.feasible,PSCData.base]; psc_numeric
  · psc_numeric
  · intro w v y _
    simpa [hModel,skeleton,PSCData.objective,quadratic] using sq_nonneg (v 0)

theorem r_rebuilt_variant_differs (b : Bool) :
    pt1 0 0 1 (-1) (-1) ∈ pscMaster (rModel b) [rEntry b] ∧
    pt1 0 0 1 (-1) (-1) ∉ pscBetaZeroMaster (rModel b) [rEntry b] := by
  refine ⟨(r_psc_minimum b).1,?_⟩
  intro h
  have hh := h.2
  norm_num [pt1] at hh

theorem r_rebuilt_projection_not_upward_closed (b : Bool) :
    (scalar 0,0) ∈ pscProject (pscBetaZeroMaster (rModel b) [rEntry b]) ∧
    (scalar 0,2) ∉ pscProject (pscBetaZeroMaster (rModel b) [rEntry b]) := by
  refine ⟨⟨pt1 0 0 0 0 0,(r_beta_zero_minimum b).1,rfl,rfl⟩,?_⟩
  rintro ⟨z,hz,_,ha⟩
  have hw := hz.1.1.1.1 (1 : Fin 2)
  have he := hz.1.1.2
  have hb := hz.2
  norm_num [rModel,skeleton,intervalRow,intervalBound] at hw he
  simp only [Prod.snd] at ha
  linarith

theorem v_projected_oa_equality :
    pscProject (pscOAMaster vModel [vEntry]) = pscGBDMaster vModel [vEntry] := by
  apply Set.Subset.antisymm
    ((psc_projected_oa_subset vModel [vEntry]).trans (psc_projected_subset_gbd vModel [vEntry]))
  intro ya h
  have hh := h.2 vEntry (by simp)
  change pscGBDRow vModel vAnchor ya.1 ≤ ya.2 at hh
  rw [v_gbd_row] at hh
  refine ⟨⟨scalar 0,scalar 0,ya.1,ya.2,ya.2⟩,?_,rfl,rfl⟩
  master_numeric
  exact hh

theorem v_projected_psc_equality :
    pscProject (pscMaster vModel [vEntry]) = pscGBDMaster vModel [vEntry] := by
  apply Set.Subset.antisymm (psc_projected_subset_gbd _ _)
  intro ya h
  exact psc_projected_oa_subset _ _ (v_projected_oa_equality.symm ▸ h)

end Chapter02PSCExamples

#print axioms Chapter02PSCExamples.scalarCoord_apply
#print axioms Chapter02PSCExamples.quadratic_derivative
#print axioms Chapter02PSCExamples.quadratic_convex
#print axioms Chapter02PSCExamples.quadratic_support_identity
#print axioms Chapter02PSCExamples.lin_apply
#print axioms Chapter02PSCExamples.singleY_bounds
#print axioms Chapter02PSCExamples.singleY_zero
#print axioms Chapter02PSCExamples.singleY_one
#print axioms Chapter02PSCExamples.signedY_apply
#print axioms Chapter02PSCExamples.doubleY_bounds
#print axioms Chapter02PSCExamples.e_kkt
#print axioms Chapter02PSCExamples.s1_kkt
#print axioms Chapter02PSCExamples.s2_kkt
#print axioms Chapter02PSCExamples.s2c_kkt
#print axioms Chapter02PSCExamples.n_kkt
#print axioms Chapter02PSCExamples.v_kkt
#print axioms Chapter02PSCExamples.vp_kkt
#print axioms Chapter02PSCExamples.h_kkt
#print axioms Chapter02PSCExamples.r_kkt
#print axioms Chapter02PSCExamples.domainV_convex
#print axioms Chapter02PSCExamples.quadratic_on_domain
#print axioms Chapter02PSCExamples.e_convex
#print axioms Chapter02PSCExamples.s1_convex
#print axioms Chapter02PSCExamples.s2_convex
#print axioms Chapter02PSCExamples.s2c_convex
#print axioms Chapter02PSCExamples.n_convex
#print axioms Chapter02PSCExamples.v_convex
#print axioms Chapter02PSCExamples.vp_convex
#print axioms Chapter02PSCExamples.h_convex
#print axioms Chapter02PSCExamples.r_convex
#print axioms Chapter02PSCExamples.e_slater
#print axioms Chapter02PSCExamples.s1_slater
#print axioms Chapter02PSCExamples.s2_slater
#print axioms Chapter02PSCExamples.s2c_slater
#print axioms Chapter02PSCExamples.n_slater
#print axioms Chapter02PSCExamples.v_slater
#print axioms Chapter02PSCExamples.vp_slater
#print axioms Chapter02PSCExamples.h_slater
#print axioms Chapter02PSCExamples.r_slater
#print axioms Chapter02PSCExamples.e_full_model
#print axioms Chapter02PSCExamples.s1_full_model
#print axioms Chapter02PSCExamples.s2_full_model
#print axioms Chapter02PSCExamples.s2c_full_model
#print axioms Chapter02PSCExamples.n_full_model
#print axioms Chapter02PSCExamples.v_full_model
#print axioms Chapter02PSCExamples.vp_full_model
#print axioms Chapter02PSCExamples.h_full_model
#print axioms Chapter02PSCExamples.r_full_model
#print axioms Chapter02PSCExamples.e_psc_row
#print axioms Chapter02PSCExamples.e_gbd_row
#print axioms Chapter02PSCExamples.s1_psc_row
#print axioms Chapter02PSCExamples.s1_gbd_row
#print axioms Chapter02PSCExamples.s2_psc_row
#print axioms Chapter02PSCExamples.s2c_psc_row
#print axioms Chapter02PSCExamples.s2_gbd_row
#print axioms Chapter02PSCExamples.s2c_gbd_row
#print axioms Chapter02PSCExamples.n_psc_row
#print axioms Chapter02PSCExamples.n_gbd_row
#print axioms Chapter02PSCExamples.v_psc_row
#print axioms Chapter02PSCExamples.vp_psc_row
#print axioms Chapter02PSCExamples.v_gbd_row
#print axioms Chapter02PSCExamples.vp_gbd_row
#print axioms Chapter02PSCExamples.h_psc_row
#print axioms Chapter02PSCExamples.h_gbd_row
#print axioms Chapter02PSCExamples.r_psc_row
#print axioms Chapter02PSCExamples.r_gbd_row
#print axioms Chapter02PSCExamples.e_gbd_minimum
#print axioms Chapter02PSCExamples.e_master_minima
#print axioms Chapter02PSCExamples.s1_gbd_minimum
#print axioms Chapter02PSCExamples.s1_psc_lower
#print axioms Chapter02PSCExamples.s1_master_minima
#print axioms Chapter02PSCExamples.s2_gbd_minimum
#print axioms Chapter02PSCExamples.s2c_gbd_minimum
#print axioms Chapter02PSCExamples.s2_psc_minimum
#print axioms Chapter02PSCExamples.s2c_psc_minimum
#print axioms Chapter02PSCExamples.s2_oa_bounds
#print axioms Chapter02PSCExamples.s2c_oa_bounds
#print axioms Chapter02PSCExamples.s2_binary_oa_minimum
#print axioms Chapter02PSCExamples.s2c_binary_oa_minimum
#print axioms Chapter02PSCExamples.s2_continuous_oa_minimum
#print axioms Chapter02PSCExamples.s2c_continuous_oa_minimum
#print axioms Chapter02PSCExamples.n_gbd_minimum
#print axioms Chapter02PSCExamples.n_master_minima
#print axioms Chapter02PSCExamples.v_gbd_minimum
#print axioms Chapter02PSCExamples.v_master_minima
#print axioms Chapter02PSCExamples.vp_gbd_minimum
#print axioms Chapter02PSCExamples.vp_master_minima
#print axioms Chapter02PSCExamples.h_gbd_minimum
#print axioms Chapter02PSCExamples.h_psc_lower
#print axioms Chapter02PSCExamples.h_master_minima
#print axioms Chapter02PSCExamples.r_gbd_minimum
#print axioms Chapter02PSCExamples.r_psc_minimum
#print axioms Chapter02PSCExamples.r_oa_minimum
#print axioms Chapter02PSCExamples.r_beta_zero_minimum
#print axioms Chapter02PSCExamples.e_projected_equality
#print axioms Chapter02PSCExamples.e_projected_oa_equality
#print axioms Chapter02PSCExamples.e_relaxation_optimum_not_original
#print axioms Chapter02PSCExamples.s1_strict_projected_gap
#print axioms Chapter02PSCExamples.s2_strict_projected_gap
#print axioms Chapter02PSCExamples.s2c_strict_projected_gap
#print axioms Chapter02PSCExamples.s2_encoding_same_original_feasible
#print axioms Chapter02PSCExamples.s2_encoding_same_original_objective
#print axioms Chapter02PSCExamples.s2_encoding_strict_retained_witness
#print axioms Chapter02PSCExamples.n_nonzero_domain_normal
#print axioms Chapter02PSCExamples.n_domain_deletion_witness
#print axioms Chapter02PSCExamples.v_nonzero_domain_normal
#print axioms Chapter02PSCExamples.v_strict_retained_gap
#print axioms Chapter02PSCExamples.v_domain_deletion_witness
#print axioms Chapter02PSCExamples.vp_encoding_changes_row
#print axioms Chapter02PSCExamples.vp_encoding_strict_witness
#print axioms Chapter02PSCExamples.vp_same_original_feasible
#print axioms Chapter02PSCExamples.vp_same_original_objective
#print axioms Chapter02PSCExamples.h_rowwise_witness
#print axioms Chapter02PSCExamples.h_rowwise_subset_gbd
#print axioms Chapter02PSCExamples.h_rowwise_minimum
#print axioms Chapter02PSCExamples.h_shared_witness_strict_gap
#print axioms Chapter02PSCExamples.h_original_attained_zero
#print axioms Chapter02PSCExamples.r_rebuilt_variant_differs
#print axioms Chapter02PSCExamples.r_rebuilt_projection_not_upward_closed
#print axioms Chapter02PSCExamples.v_projected_oa_equality
#print axioms Chapter02PSCExamples.v_projected_psc_equality
