module

public import Chapter02DICOPTModel
public import Mathlib.Tactic.Positivity

@[expose] public section

noncomputable section
open scoped BigOperators
namespace Chapter02.DICOPT
variable {n m e l r : ℕ} {d : Data n m e l r}
variable {x0 : RealVector n} {y0 : RealVector m}

@[simp] theorem dot_sub {a x y : RealVector n} : dot a (x-y) = dot a x - dot a y := by
  simp [dot, mul_sub, Finset.sum_sub_distrib]

@[simp] theorem dot_zero (a : RealVector n) : dot a 0 = 0 := by simp [dot]

@[simp] theorem FixedKKT.sigma_eq_one (k : FixedKKT d x0 y0) : k.sigma = 1 := by
  linarith [k.alphaStationarity]

@[simp] theorem FixedKKT.alpha_eq (k : FixedKKT d x0 y0) : k.alpha = d.f x0 := by
  have h := k.alphaComp
  rw [k.sigma_eq_one, one_mul] at h
  linarith

@[simp] theorem abs_mul_signReal (a : ℝ) : |a| * signReal a = a := by
  exact abs_mul_sign a

@[simp] theorem signReal_zero : signReal 0 = 0 := by simp [signReal]

def boxTerm (k : FixedKKT d x0 y0) (x : RealVector n) : ℝ :=
  ∑ i, (k.xLower i * (d.xL i-x i) + k.xUpper i * (x i-d.xU i))

def yBoxTerm (k : JointKKT d x0 y0) (y : RealVector m) : ℝ :=
  ∑ i, (k.yLower i * (0-y i) + k.yUpper i * (y i-1))

theorem FixedKKT.eq_expansion (k : FixedKKT d x0 y0) (x : RealVector n)
    (y : RealVector m) (i : Fin e) :
    |k.lambda i| * eqTangent d k.jet k.lambda i x y =
      k.lambda i * k.jet.Dh i (x-x0) + k.lambda i * dot (d.A i) (y-y0) := by
  have hf := k.feasible.2.1 i
  dsimp [Data.eqRow] at hf
  simp only [eqTangent, ← mul_assoc, abs_mul_signReal, dot_sub]
  have hh : d.h i x0 = -dot (d.A i) y0 := by linarith
  rw [hh]
  ring

theorem FixedKKT.ineq_expansion (k : FixedKKT d x0 y0) (x : RealVector n)
    (y : RealVector m) (i : Fin l) :
    k.mu i * ineqTangent d k.jet i x y =
      k.mu i * k.jet.Dg i (x-x0) + k.mu i * dot (d.B i) (y-y0) := by
  have hf := k.ineqComp i
  dsimp [Data.ineqRow] at hf
  simp only [ineqTangent, dot_sub]
  nlinarith

theorem FixedKKT.affine_expansion (k : FixedKKT d x0 y0) (x : RealVector n)
    (y : RealVector m) (i : Fin r) :
    k.nu i * d.affineRow i x y =
      k.nu i * dot (d.D i) (x-x0) + k.nu i * dot (d.C i) (y-y0) := by
  have hf := k.affineComp i
  dsimp [Data.affineRow] at hf ⊢
  simp only [dot_sub]
  nlinarith

theorem FixedKKT.box_expansion (k : FixedKKT d x0 y0) (x : RealVector n) :
    boxTerm k x = ∑ i, (k.xUpper i-k.xLower i) * (x-x0) i := by
  apply Finset.sum_congr rfl
  intro i _
  have hl := k.lowerComp i
  have hu := k.upperComp i
  simp only [Pi.sub_apply]
  nlinarith

theorem FixedKKT.affine_balance (k : FixedKKT d x0 y0) (x : RealVector n)
    (y : RealVector m) :
    objTangent d k.jet x - d.f x0 +
      (∑ i, |k.lambda i| * eqTangent d k.jet k.lambda i x y) +
      (∑ i, k.mu i * ineqTangent d k.jet i x y) +
      (∑ i, k.nu i * d.affineRow i x y) + boxTerm k x =
      (∑ i, k.lambda i * dot (d.A i) (y-y0)) +
      (∑ i, k.mu i * dot (d.B i) (y-y0)) +
      (∑ i, k.nu i * dot (d.C i) (y-y0)) := by
  simp_rw [k.eq_expansion, k.ineq_expansion, k.affine_expansion, Finset.sum_add_distrib]
  rw [k.box_expansion]
  have hs := k.stationarity (x-x0)
  rw [k.sigma_eq_one, one_mul] at hs
  simp only [Pi.sub_apply] at hs
  dsimp [objTangent]
  linarith

theorem FixedKKT.fixed_balance (k : FixedKKT d x0 y0) (x : RealVector n) :
    objTangent d k.jet x - d.f x0 +
      (∑ i, |k.lambda i| * eqTangent d k.jet k.lambda i x y0) +
      (∑ i, k.mu i * ineqTangent d k.jet i x y0) +
      (∑ i, k.nu i * d.affineRow i x y0) + boxTerm k x = 0 := by
  simpa using k.affine_balance x y0

theorem FixedKKT.box_nonpos (k : FixedKKT d x0 y0) {x : RealVector n}
    (hx : x ∈ d.xBox) : boxTerm k x ≤ 0 := by
  apply Finset.sum_nonpos
  intro i _
  exact add_nonpos
    (mul_nonpos_of_nonneg_of_nonpos (k.lowerNonneg i) (sub_nonpos.mpr (hx.1 i)))
    (mul_nonpos_of_nonneg_of_nonpos (k.upperNonneg i) (sub_nonpos.mpr (hx.2 i)))

theorem FixedKKT.affine_nonpos (k : FixedKKT d x0 y0) {x : RealVector n}
    {y : RealVector m} (hx : d.Hard x y) :
    (∑ i, k.nu i * d.affineRow i x y) ≤ 0 :=
  Finset.sum_nonpos fun i _ => mul_nonpos_of_nonneg_of_nonpos (k.nuNonneg i) (hx.2 i)

theorem JointKKT.y_balance (k : JointKKT d x0 y0) (y : RealVector m) :
    dot d.c (y-y0) + (∑ i, k.lambda i * dot (d.A i) (y-y0)) +
      (∑ i, k.mu i * dot (d.B i) (y-y0)) +
      (∑ i, k.nu i * dot (d.C i) (y-y0)) + yBoxTerm k y = 0 := by
  have hb : yBoxTerm k y = ∑ i, (k.yUpper i-k.yLower i)*(y-y0) i := by
    apply Finset.sum_congr rfl
    intro i _
    have hl := k.yLowerComp i
    have hu := k.yUpperComp i
    simp only [Pi.sub_apply]
    nlinarith
  rw [hb]
  exact k.yStationarity (y-y0)

theorem JointKKT.y_nonpos (k : JointKKT d x0 y0) {y : RealVector m}
    (hy : y ∈ d.yBox) : yBoxTerm k y ≤ 0 := by
  apply Finset.sum_nonpos
  intro i _
  exact add_nonpos
    (mul_nonpos_of_nonneg_of_nonpos (k.yLowerNonneg i) (sub_nonpos.mpr (hy.1 i)))
    (mul_nonpos_of_nonneg_of_nonpos (k.yUpperNonneg i) (sub_nonpos.mpr (hy.2 i)))

theorem source_tangents (k : FixedKKT d x0 y0) (hc : SignedConvex d k)
    {x : RealVector n} {y : RealVector m} (hx : d.Feasible x y) :
    objTangent d k.jet x ≤ d.f x ∧
    (∀ i, eqTangent d k.jet k.lambda i x y ≤ 0) ∧
    (∀ i, ineqTangent d k.jet i x y ≤ 0) := by
  refine ⟨tangent_underestimator_on hc.objective k.feasible.1.1 hx.1.1 k.jet.fderiv, ?_, ?_⟩
  · intro i
    have ht := tangent_underestimator_on (hc.equalities i) k.feasible.1.1 hx.1.1
      ((k.jet.hderiv i).const_mul (signReal (k.lambda i)))
    have he := hx.2.1 i
    simp only [ContinuousLinearMap.smul_apply, smul_eq_mul] at ht
    dsimp [Data.eqRow] at he
    have hz : signReal (k.lambda i) * (dot (d.A i) y + d.h i x) = 0 := by rw [he]; ring
    dsimp [eqTangent]
    nlinarith [hz]
  · intro i
    have ht := tangent_underestimator_on (hc.inequalities i) k.feasible.1.1 hx.1.1
      (k.jet.gderiv i)
    have hi := hx.2.2 i
    dsimp [Data.ineqRow] at hi
    dsimp [ineqTangent]
    linarith

theorem FixedKKT.global_min (k : FixedKKT d x0 y0) (hc : SignedConvex d k) :
    IsMinimizer (d.fiber y0) (fun x => d.objective x y0) x0 := by
  refine ⟨k.feasible, ?_⟩
  intro x hx
  obtain ⟨hf, he, hg⟩ := source_tangents k hc hx
  have he' : (∑ i, |k.lambda i| * eqTangent d k.jet k.lambda i x y0) ≤ 0 :=
    Finset.sum_nonpos fun i _ => mul_nonpos_of_nonneg_of_nonpos (abs_nonneg _) (he i)
  have hg' : (∑ i, k.mu i * ineqTangent d k.jet i x y0) ≤ 0 :=
    Finset.sum_nonpos fun i _ => mul_nonpos_of_nonneg_of_nonpos (k.muNonneg i) (hg i)
  have ha := k.affine_nonpos hx.1
  have hb := k.box_nonpos hx.1.1
  have hbal := k.fixed_balance x
  dsimp [Data.objective]
  linarith

theorem JointKKT.global_min (k : JointKKT d x0 y0) (hc : SignedConvex d k.toFixedKKT) :
    IsMinimizer d.relaxed (fun z => d.objective z.1 z.2) (x0,y0) := by
  refine ⟨⟨k.feasible, k.yFeasible⟩, ?_⟩
  rintro ⟨x,y⟩ ⟨hx,hy⟩
  obtain ⟨hf, he, hg⟩ := source_tangents k.toFixedKKT hc hx
  have he' : (∑ i, |k.lambda i| * eqTangent d k.jet k.lambda i x y) ≤ 0 :=
    Finset.sum_nonpos fun i _ => mul_nonpos_of_nonneg_of_nonpos (abs_nonneg _) (he i)
  have hg' : (∑ i, k.mu i * ineqTangent d k.jet i x y) ≤ 0 :=
    Finset.sum_nonpos fun i _ => mul_nonpos_of_nonneg_of_nonpos (k.muNonneg i) (hg i)
  have ha := k.toFixedKKT.affine_nonpos hx.1
  have hb := k.toFixedKKT.box_nonpos hx.1.1
  have hyb := k.y_nonpos hy
  have hbal := k.toFixedKKT.affine_balance x y
  have hybal := k.y_balance y
  rw [dot_sub] at hybal
  dsimp [Data.objective]
  linarith

/-- Literal fixed-real-parameter signed tangent LP, with unrestricted alpha. -/
def hardFeasible (k : FixedKKT d x0 y0) : Set (RealVector n × ℝ) := {z |
  d.Hard z.1 y0 ∧ objTangent d k.jet z.1 ≤ z.2 ∧
  (∀ i, eqTangent d k.jet k.lambda i z.1 y0 ≤ 0) ∧
  ∀ i, ineqTangent d k.jet i z.1 y0 ≤ 0}

def hardObjective (_k : FixedKKT d x0 y0) (z : RealVector n × ℝ) : ℝ :=
  dot d.c y0 + z.2

/-- Multipliers and full x/alpha stationarity shared by both literal affine programs. -/
structure TangentDual (k : FixedKKT d x0 y0) where
  sigma : ℝ
  eta : RealVector e
  mu : RealVector l
  nu : RealVector r
  lower : RealVector n
  upper : RealVector n
  sigmaNonneg : 0 ≤ sigma
  etaNonneg : ∀ i, 0 ≤ eta i
  muNonneg : ∀ i, 0 ≤ mu i
  nuNonneg : ∀ i, 0 ≤ nu i
  lowerNonneg : ∀ i, 0 ≤ lower i
  upperNonneg : ∀ i, 0 ≤ upper i
  alphaStationarity : 1-sigma=0
  xStationarity : ∀ v : RealVector n,
    sigma*k.jet.Df v + (∑ i, eta i * (signReal (k.lambda i)*k.jet.Dh i v)) +
      (∑ i, mu i*k.jet.Dg i v) + (∑ i, nu i*dot (d.D i) v) +
      (∑ i, (upper i-lower i)*v i) = 0

structure HardKKT (k : FixedKKT d x0 y0) (z : RealVector n × ℝ) extends TangentDual k where
  primal : z ∈ hardFeasible k
  objComp : sigma*(objTangent d k.jet z.1-z.2)=0
  eqComp : ∀ i, eta i*eqTangent d k.jet k.lambda i z.1 y0=0
  ineqComp : ∀ i, mu i*ineqTangent d k.jet i z.1 y0=0
  affineComp : ∀ i, nu i*d.affineRow i z.1 y0=0
  lowerComp : ∀ i, lower i*(d.xL i-z.1 i)=0
  upperComp : ∀ i, upper i*(z.1 i-d.xU i)=0

structure SlicePoint (n e l : ℕ) where
  x : RealVector n
  alpha : ℝ
  s : ℝ
  p : RealVector e
  q : RealVector l

def apFeasible (k : FixedKKT d x0 y0) : Set (SlicePoint n e l) := {z |
  d.Hard z.x y0 ∧ 0 ≤ z.s ∧ (∀ i, 0 ≤ z.p i) ∧ (∀ i, 0 ≤ z.q i) ∧
  objTangent d k.jet z.x-z.alpha ≤ z.s ∧
  (∀ i, eqTangent d k.jet k.lambda i z.x y0 ≤ z.p i) ∧
  ∀ i, ineqTangent d k.jet i z.x y0 ≤ z.q i}

def apObjective (k : FixedKKT d x0 y0) (w : Weights k) (z : SlicePoint n e l) : ℝ :=
  dot d.c y0+z.alpha+w.obj*z.s+(∑ i,w.eq i*z.p i)+(∑ i,w.ineq i*z.q i)

def apAnchor (k : FixedKKT d x0 y0) : SlicePoint n e l := ⟨x0,k.alpha,0,0,0⟩

structure APKKT (k : FixedKKT d x0 y0) (w : Weights k) (z : SlicePoint n e l)
    extends TangentDual k where
  primal : z ∈ apFeasible k
  sLower : ℝ
  pLower : RealVector e
  qLower : RealVector l
  sLowerNonneg : 0 ≤ sLower
  pLowerNonneg : ∀ i, 0 ≤ pLower i
  qLowerNonneg : ∀ i, 0 ≤ qLower i
  objComp : sigma*(objTangent d k.jet z.x-z.alpha-z.s)=0
  eqComp : ∀ i, eta i*(eqTangent d k.jet k.lambda i z.x y0-z.p i)=0
  ineqComp : ∀ i, mu i*(ineqTangent d k.jet i z.x y0-z.q i)=0
  affineComp : ∀ i, nu i*d.affineRow i z.x y0=0
  lowerComp : ∀ i, lower i*(d.xL i-z.x i)=0
  upperComp : ∀ i, upper i*(z.x i-d.xU i)=0
  sComp : sLower*(-z.s)=0
  pComp : ∀ i, pLower i*(-z.p i)=0
  qComp : ∀ i, qLower i*(-z.q i)=0
  sStationarity : w.obj-sigma-sLower=0
  pStationarity : ∀ i, w.eq i-eta i-pLower i=0
  qStationarity : ∀ i, w.ineq i-mu i-qLower i=0

def sourceDual (k : FixedKKT d x0 y0) : TangentDual k where
  sigma := k.sigma
  eta := fun i => |k.lambda i|
  mu := k.mu
  nu := k.nu
  lower := k.xLower
  upper := k.xUpper
  sigmaNonneg := k.sigmaNonneg
  etaNonneg := fun i => abs_nonneg _
  muNonneg := k.muNonneg
  nuNonneg := k.nuNonneg
  lowerNonneg := k.lowerNonneg
  upperNonneg := k.upperNonneg
  alphaStationarity := k.alphaStationarity
  xStationarity := by
    intro v
    simpa only [← mul_assoc, abs_mul_signReal] using k.stationarity v

theorem hard_anchor_feasible (k : FixedKKT d x0 y0) : (x0,k.alpha) ∈ hardFeasible k := by
  refine ⟨k.feasible.1, ?_, ?_, ?_⟩
  · simp [objTangent]
  · intro i
    have he := k.feasible.2.1 i
    simpa [eqTangent, Data.eqRow, he] using (show signReal (k.lambda i)*d.eqRow i x0 y0 ≤ 0 by rw [he]; simp)
  · intro i
    simpa [ineqTangent,Data.ineqRow] using k.feasible.2.2 i

def sourceHardKKT (k : FixedKKT d x0 y0) : HardKKT k (x0,k.alpha) where
  toTangentDual := sourceDual k
  primal := hard_anchor_feasible k
  objComp := by simp [sourceDual,objTangent]
  eqComp := by
    intro i
    change |k.lambda i| * eqTangent d k.jet k.lambda i x0 y0 = 0
    rw [k.eq_expansion]
    simp
  ineqComp := by intro i; simpa [sourceDual,ineqTangent,Data.ineqRow] using k.ineqComp i
  affineComp := k.affineComp
  lowerComp := k.lowerComp
  upperComp := k.upperComp

theorem hard_anchor_min (k : FixedKKT d x0 y0) :
    IsMinimizer (hardFeasible k) (hardObjective k) (x0,k.alpha) := by
  refine ⟨hard_anchor_feasible k, ?_⟩
  rintro ⟨x,a⟩ ⟨hx,hobj,he,hg⟩
  have he' : (∑ i,|k.lambda i| *eqTangent d k.jet k.lambda i x y0) ≤ 0 :=
    Finset.sum_nonpos fun i _ => mul_nonpos_of_nonneg_of_nonpos (abs_nonneg _) (he i)
  have hg' : (∑ i,k.mu i*ineqTangent d k.jet i x y0) ≤ 0 :=
    Finset.sum_nonpos fun i _ => mul_nonpos_of_nonneg_of_nonpos (k.muNonneg i) (hg i)
  have ha := k.affine_nonpos hx
  have hb := k.box_nonpos hx.1
  have hbal := k.fixed_balance x
  simp only [hardObjective,k.alpha_eq]
  linarith

/-- VG1990 Prop1, plus derived fixed-slice global affine optimality; NO convexity assumption. -/
theorem source_signed_hard_transfer (k : FixedKKT d x0 y0) :
    Nonempty (HardKKT k (x0,k.alpha)) ∧
    IsMinimizer (hardFeasible k) (hardObjective k) (x0,k.alpha) :=
  ⟨⟨sourceHardKKT k⟩,hard_anchor_min k⟩

theorem ap_anchor_feasible (k : FixedKKT d x0 y0) : apAnchor k ∈ apFeasible k := by
  obtain ⟨hh,hf,he,hg⟩ := hard_anchor_feasible k
  exact ⟨hh,le_rfl,fun _ => le_rfl,fun _ => le_rfl,sub_nonpos.mpr hf,he,hg⟩

def sourceAPKKT (k : FixedKKT d x0 y0) (w : Weights k) : APKKT k w (apAnchor k) where
  toTangentDual := sourceDual k
  primal := ap_anchor_feasible k
  sLower := w.obj-k.sigma
  pLower := fun i => w.eq i-|k.lambda i|
  qLower := fun i => w.ineq i-k.mu i
  sLowerNonneg := by have h := w.obj_gt; have h' := le_abs_self k.sigma; linarith
  pLowerNonneg := fun i => sub_nonneg.mpr (w.eq_gt i).le
  qLowerNonneg := by intro i; have h := w.ineq_gt i; have h' := le_abs_self (k.mu i); linarith
  objComp := by simp [sourceDual,apAnchor,objTangent]
  eqComp := by
    intro i
    change |k.lambda i| * (eqTangent d k.jet k.lambda i x0 y0 - 0) = 0
    rw [sub_zero, k.eq_expansion]
    simp
  ineqComp := by intro i; simpa [apAnchor, sourceDual, sourceHardKKT] using (sourceHardKKT k).ineqComp i
  affineComp := k.affineComp
  lowerComp := k.lowerComp
  upperComp := k.upperComp
  sComp := by simp [apAnchor]
  pComp := by intro i; simp [apAnchor]
  qComp := by intro i; simp [apAnchor]
  sStationarity := by simp [sourceDual]
  pStationarity := by intro i; simp [sourceDual]
  qStationarity := by intro i; simp [sourceDual]

def slackGap (k : FixedKKT d x0 y0) (w : Weights k) (z : SlicePoint n e l) : ℝ :=
  (w.obj-1)*z.s+(∑ i,(w.eq i-|k.lambda i|)*z.p i)+(∑ i,(w.ineq i-k.mu i)*z.q i)

theorem ap_gap (k : FixedKKT d x0 y0) (w : Weights k) {z : SlicePoint n e l}
    (hz : z ∈ apFeasible k) :
    slackGap k w z ≤ apObjective k w z-apObjective k w (apAnchor k) := by
  obtain ⟨hh,hs,hp,hq,hf,he,hg⟩ := hz
  have he' : (∑ i,|k.lambda i| *eqTangent d k.jet k.lambda i z.x y0) ≤
      ∑ i,|k.lambda i| *z.p i :=
    Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_left (he i) (abs_nonneg _)
  have hg' : (∑ i,k.mu i*ineqTangent d k.jet i z.x y0) ≤ ∑ i,k.mu i*z.q i :=
    Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_left (hg i) (k.muNonneg i)
  have ha := k.affine_nonpos hh
  have hb := k.box_nonpos hh.1
  have hbal := k.fixed_balance z.x
  simp only [slackGap,apObjective,apAnchor,k.alpha_eq,Pi.zero_apply,mul_zero,
    Finset.sum_const_zero,add_zero,sub_mul,Finset.sum_sub_distrib,one_mul]
  linarith

theorem slackGap_nonneg (k : FixedKKT d x0 y0) (w : Weights k) {z : SlicePoint n e l}
    (hz : z ∈ apFeasible k) : 0 ≤ slackGap k w z := by
  have ho : 1 < w.obj := by simpa using w.obj_gt
  exact add_nonneg (add_nonneg (mul_nonneg (sub_nonneg.mpr ho.le) hz.2.1)
    (Finset.sum_nonneg fun i _ => mul_nonneg (sub_nonneg.mpr (w.eq_gt i).le) (hz.2.2.1 i)))
    (Finset.sum_nonneg fun i _ => mul_nonneg (sub_nonneg.mpr
      ((le_abs_self (k.mu i)).trans (w.ineq_gt i).le)) (hz.2.2.2.1 i))

theorem ap_anchor_min (k : FixedKKT d x0 y0) (w : Weights k) :
    IsMinimizer (apFeasible k) (apObjective k w) (apAnchor k) := by
  refine ⟨ap_anchor_feasible k, ?_⟩
  intro z hz
  have h := ap_gap k w hz
  have h0 := slackGap_nonneg k w hz
  linarith

theorem ap_min_slacks_zero (k : FixedKKT d x0 y0) (w : Weights k)
    {z : SlicePoint n e l} (hz : IsMinimizer (apFeasible k) (apObjective k w) z) :
    z.s=0 ∧ (∀ i,z.p i=0) ∧ ∀ i,z.q i=0 := by
  have hgap := ap_gap k w hz.1
  have hmin := hz.2 (apAnchor k) (ap_anchor_feasible k)
  have hs := hz.1.2.1
  have hp := hz.1.2.2.1
  have hq := hz.1.2.2.2.1
  have ho : 1 < w.obj := by simpa using w.obj_gt
  have hep : ∀ i,0 ≤ (w.eq i-|k.lambda i|)*z.p i :=
    fun i => mul_nonneg (sub_nonneg.mpr (w.eq_gt i).le) (hp i)
  have hgq : ∀ i,0 ≤ (w.ineq i-k.mu i)*z.q i := fun i =>
    mul_nonneg (sub_nonneg.mpr ((le_abs_self _).trans (w.ineq_gt i).le)) (hq i)
  have hp0 := Finset.sum_nonneg (s := Finset.univ) (fun i _ => hep i)
  have hq0 := Finset.sum_nonneg (s := Finset.univ) (fun i _ => hgq i)
  have hs0 : 0 ≤ (w.obj-1)*z.s := mul_nonneg (sub_nonneg.mpr ho.le) hs
  change (w.obj-1)*z.s+(∑ i,(w.eq i-|k.lambda i|)*z.p i)+
    (∑ i,(w.ineq i-k.mu i)*z.q i) ≤ _ at hgap
  refine ⟨?_,?_,?_⟩
  · nlinarith
  · intro i
    have hi := Finset.single_le_sum (fun j (_ : j ∈ Finset.univ) => hep j) (Finset.mem_univ i)
    have hw := w.eq_gt i
    nlinarith [hp i]
  · intro i
    have hi := Finset.single_le_sum (fun j (_ : j ∈ Finset.univ) => hgq j) (Finset.mem_univ i)
    have hw := (le_abs_self (k.mu i)).trans_lt (w.ineq_gt i)
    nlinarith [hq i]

/-- VG1990 Prop2 and derived gap/all-minimizer fixed-slice strengthening. -/
theorem source_separate_slack_transfer (k : FixedKKT d x0 y0) (w : Weights k) :
    Nonempty (APKKT k w (apAnchor k)) ∧
    IsMinimizer (apFeasible k) (apObjective k w) (apAnchor k) ∧
    (∀ z ∈ apFeasible k, slackGap k w z ≤ apObjective k w z-apObjective k w (apAnchor k)) ∧
    (∀ z, IsMinimizer (apFeasible k) (apObjective k w) z →
      z.s=0 ∧ (∀ i,z.p i=0) ∧ ∀ i,z.q i=0) :=
  ⟨⟨sourceAPKKT k w⟩,ap_anchor_min k w,fun _ hz => ap_gap k w hz,
    fun _ hz => ap_min_slacks_zero k w hz⟩

end Chapter02.DICOPT
#print axioms Chapter02.DICOPT.source_signed_hard_transfer
#print axioms Chapter02.DICOPT.source_separate_slack_transfer
