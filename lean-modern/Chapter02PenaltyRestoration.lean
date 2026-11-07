module

public import Chapter02WeightedRestoration
public import Chapter02Restoration

@[expose] public section

/-! Objective-plus-nonnegative-slack restoration. This is distinct from both
signed free-slack and weighted positive-part restoration. All penalty bounds
are quantified and all minimizers are actual optimization minima. -/
noncomputable section
open scoped BigOperators
open Set
namespace Chapter02

def penaltyViolation {E : Type*} {l : ℕ} (g : Fin l → E → ℝ) (x : E) : ℝ :=
  eshMaximum (Fin.cases (fun _ => 0) g) x

theorem penaltyViolation_le_iff {E : Type*} {l : ℕ} (g : Fin l → E → ℝ)
    (x : E) (u : ℝ) : penaltyViolation g x ≤ u ↔ 0 ≤ u ∧ ∀ j, g j x ≤ u := by
  rw [penaltyViolation,eshMaximum_le_iff]
  constructor
  · intro h; exact ⟨h 0,fun j => h j.succ⟩
  · rintro ⟨h0,hg⟩ i
    exact Fin.cases h0 hg i

theorem penaltyViolation_nonneg {E : Type*} {l : ℕ} (g : Fin l → E → ℝ) (x : E) :
    0 ≤ penaltyViolation g x := (penaltyViolation_le_iff g x _).mp le_rfl |>.1

theorem penaltyViolation_row_le {E : Type*} {l : ℕ} (g : Fin l → E → ℝ) (x : E)
    (j : Fin l) : g j x ≤ penaltyViolation g x :=
  (penaltyViolation_le_iff g x _).mp le_rfl |>.2 j

theorem penaltyViolation_eq_zero_iff {E : Type*} {l : ℕ} (g : Fin l → E → ℝ) (x : E) :
    penaltyViolation g x = 0 ↔ ∀ j, g j x ≤ 0 := by
  constructor
  · intro hz j; simpa only [hz] using penaltyViolation_row_le g x j
  · intro hg
    exact le_antisymm ((penaltyViolation_le_iff g x 0).mpr ⟨le_rfl,hg⟩)
      (penaltyViolation_nonneg g x)

theorem penaltyViolation_continuous {E : Type*} [TopologicalSpace E] {l : ℕ}
    (g : Fin l → E → ℝ) (hg : ∀ j, Continuous (g j)) : Continuous (penaltyViolation g) := by
  apply eshMaximum_continuous
  intro i
  exact Fin.cases continuous_const hg i

def penaltyObjective {E : Type*} {l : ℕ} (f : E → ℝ) (g : Fin l → E → ℝ)
    (M : ℝ) (x : E) : ℝ := f x + M * penaltyViolation g x

def penaltyPairs {E : Type*} {l : ℕ} (C : Set E) (g : Fin l → E → ℝ) : Set (E × ℝ) :=
  {q | q.1 ∈ C ∧ 0 ≤ q.2 ∧ ∀ j, g j q.1 ≤ q.2}

theorem penalty_pairs_minimizer_iff {E : Type*} {l : ℕ} (C : Set E)
    (f : E → ℝ) (g : Fin l → E → ℝ) {M : ℝ} (hM : 0 < M) (q : E × ℝ) :
    IsMinimizer (penaltyPairs C g) (fun z => f z.1 + M*z.2) q ↔
    IsMinimizer C (penaltyObjective f g M) q.1 ∧ q.2 = penaltyViolation g q.1 := by
  constructor
  · intro hp
    have hle := (penaltyViolation_le_iff g q.1 q.2).mpr ⟨hp.1.2.1,hp.1.2.2⟩
    have hc := hp.2 (q.1,penaltyViolation g q.1)
      ⟨hp.1.1,penaltyViolation_nonneg g q.1,penaltyViolation_row_le g q.1⟩
    have ht : q.2 = penaltyViolation g q.1 := by dsimp at hc; nlinarith
    refine ⟨⟨hp.1.1,?_⟩,ht⟩
    intro x hx
    have hh := hp.2 (x,penaltyViolation g x)
      ⟨hx,penaltyViolation_nonneg g x,penaltyViolation_row_le g x⟩
    simpa only [penaltyObjective,ht] using hh
  · rintro ⟨hp,ht⟩
    refine ⟨⟨hp.1,?_,?_⟩,?_⟩
    · rw [ht]; exact penaltyViolation_nonneg g q.1
    · rw [ht]; exact penaltyViolation_row_le g q.1
    · intro z hz
      have ha := hp.2 z.1 hz.1
      have hb := (penaltyViolation_le_iff g z.1 z.2).mpr ⟨hz.2.1,hz.2.2⟩
      dsimp [penaltyObjective] at ha
      change f q.1 + M*q.2 ≤ f z.1+M*z.2
      rw [ht]
      nlinarith

theorem penalty_minimum_exists {E : Type*} [TopologicalSpace E] {l : ℕ}
    (C : Set E) (f : E → ℝ) (g : Fin l → E → ℝ) (M : ℝ)
    (hC : IsCompact C) (hne : C.Nonempty) (hf : ContinuousOn f C)
    (hg : ∀ j, Continuous (g j)) : ∃ p, IsMinimizer C (penaltyObjective f g M) p :=
  compact_feasible_attainment hC hne
    (hf.add (continuousOn_const.mul (penaltyViolation_continuous g hg).continuousOn))

theorem penalty_pairs_minimum_exists {E : Type*} [TopologicalSpace E] {l : ℕ}
    (C : Set E) (f : E → ℝ) (g : Fin l → E → ℝ) {M : ℝ} (hM : 0 < M)
    (hC : IsCompact C) (hne : C.Nonempty) (hf : ContinuousOn f C)
    (hg : ∀ j, Continuous (g j)) :
    ∃ q, IsMinimizer (penaltyPairs C g) (fun z => f z.1+M*z.2) q := by
  obtain ⟨p,hp⟩ := penalty_minimum_exists C f g M hC hne hf hg
  exact ⟨(p,penaltyViolation g p),(penalty_pairs_minimizer_iff C f g hM _).mpr ⟨hp,rfl⟩⟩

/-- An algebraic bridge used only after support has been derived from an actual
convex constrained minimum. It is not a restoration-reply exclusion field. -/
theorem penalty_exact_of_support {E : Type*} {l : ℕ} (C : Set E)
    (f : E → ℝ) (g : Fin l → E → ℝ) (lambda : Fin l → ℝ)
    {pstar p : E} {M : ℝ} (hl : ∀ j, 0 ≤ lambda j)
    (hstar : pstar ∈ C ∧ ∀ j, g j pstar ≤ 0)
    (hsupport : ∀ x ∈ C, f pstar ≤ f x + ∑ j, lambda j*g j x)
    (hM : (∑ j,lambda j) < M)
    (hp : IsMinimizer C (penaltyObjective f g M) p) :
    penaltyViolation g p = 0 ∧ IsMinimizer {x ∈ C | ∀ j, g j x ≤ 0} f p := by
  have hsum : (∑ j, lambda j*g j p) ≤ (∑ j,lambda j)*penaltyViolation g p := by
    rw [Finset.sum_mul]
    exact Finset.sum_le_sum fun j _ => mul_le_mul_of_nonneg_left
      (penaltyViolation_row_le g p j) (hl j)
  have hzstar := (penaltyViolation_eq_zero_iff g pstar).mpr hstar.2
  have hm := hp.2 pstar hstar.1
  dsimp [penaltyObjective] at hm
  rw [hzstar,mul_zero,add_zero] at hm
  have hs := hsupport p hp.1
  have hn := penaltyViolation_nonneg g p
  have hz : penaltyViolation g p=0 := by nlinarith
  refine ⟨hz,⟨⟨hp.1,(penaltyViolation_eq_zero_iff g p).mp hz⟩,?_⟩⟩
  intro q hq
  have hh := hp.2 q hq.1
  dsimp [penaltyObjective] at hh
  rw [hz,(penaltyViolation_eq_zero_iff g q).mpr hq.2] at hh
  simpa using hh

/-- Strict Slater and a domain-wide objective lower bound produce an explicit
sufficient threshold. Equality with the threshold is intentionally excluded. -/
theorem penalty_quantified_feasible_exactness {n l : ℕ} (C : Set (RealVector n))
    (f : RealVector n → ℝ) (g : Fin l → RealVector n → ℝ)
    {pstar p z : RealVector n} {M sigma L : ℝ}
    (hC : Convex ℝ C) (hf : ConvexOn ℝ C f) (hg : ∀ j, ConvexOn ℝ C (g j))
    (hstar : IsMinimizer {x ∈ C | ∀ j, g j x ≤ 0} f pstar)
    (hz : z ∈ C) (hsigma : 0 < sigma) (hstrict : ∀ j, g j z ≤ -sigma)
    (hL : ∀ x ∈ C, L ≤ f x) (hM : (f z-L)/sigma < M)
    (hp : IsMinimizer C (penaltyObjective f g M) p) :
    penaltyViolation g p = 0 ∧ IsMinimizer {x ∈ C | ∀ j, g j x ≤ 0} f p := by
  obtain ⟨lambda,hl,hcomp,hsup⟩ := convex_slater_partialLagrangian_minimum C f g pstar
    hC hf hg hstar ⟨z,hz,fun j => lt_of_le_of_lt (hstrict j) (by linarith)⟩
  have hsupport : ∀ x ∈ C, f pstar ≤ f x + ∑ j, lambda j*g j x := by
    intro x hx
    simpa only [hcomp,Finset.sum_const_zero,add_zero] using hsup.2 x hx
  have hs : (∑ j,lambda j*g j z) ≤ (∑ j,lambda j)*(-sigma) := by
    rw [Finset.sum_mul]
    exact Finset.sum_le_sum fun j _ => mul_le_mul_of_nonneg_left (hstrict j) (hl j)
  have hbound : (∑ j,lambda j) ≤ (f z-L)/sigma := by
    apply (le_div_iff₀ hsigma).mpr
    have := hsupport z hz
    have := hL pstar hstar.1.1
    nlinarith
  exact penalty_exact_of_support C f g lambda hl hstar.1 hsupport (hbound.trans_lt hM) hp


def penaltyHeight {n : ℕ} : RealVector (n+1) →L[ℝ] ℝ :=
  ContinuousLinearMap.proj ((0 : Fin 1).natAdd n)

@[simp] theorem penaltyHeight_insert {n : ℕ} (p : RealVector n) (v : RealVector 1) :
    penaltyHeight (weightedInsert p v) = v 0 := by simp [penaltyHeight,weightedInsert]

def penaltyLiftRows {n l : ℕ} (g : Fin l → RealVector n → ℝ) :
    Fin (l+1) → RealVector (n+1) → ℝ :=
  Fin.cases (fun q => -penaltyHeight q) (fun j q => g j (weightedX q)-penaltyHeight q)

def penaltyLiftRowD {n l : ℕ} (Dg : Fin l → RealVector n →L[ℝ] ℝ) :
    Fin (l+1) → RealVector (n+1) →L[ℝ] ℝ :=
  Fin.cases (-penaltyHeight) (fun j => (Dg j).comp weightedX-penaltyHeight)

def penaltyLiftF {n : ℕ} (f : RealVector n → ℝ) (M : ℝ) (q : RealVector (n+1)) : ℝ :=
  f (weightedX q)+M*penaltyHeight q

def penaltyLiftD {n : ℕ} (Df : RealVector n →L[ℝ] ℝ) (M : ℝ) :
    RealVector (n+1) →L[ℝ] ℝ := Df.comp weightedX+M • penaltyHeight

theorem penalty_lift_rows_iff {n l : ℕ} (g : Fin l → RealVector n → ℝ)
    (q : RealVector (n+1)) : (∀ i,penaltyLiftRows g i q≤0) ↔
      0≤penaltyHeight q ∧ ∀ j,g j (weightedX q)≤penaltyHeight q := by
  constructor
  · intro h
    exact ⟨neg_nonpos.mp (h 0),fun j => sub_nonpos.mp (h j.succ)⟩
  · rintro ⟨h0,hg⟩ i
    exact Fin.cases (neg_nonpos.mpr h0) (fun j => sub_nonpos.mpr (hg j)) i

theorem penalty_lift_actual_minimum {n l : ℕ} (C : Set (RealVector n))
    (f : RealVector n → ℝ) (g : Fin l → RealVector n → ℝ)
    {M : ℝ} (hM : 0 ≤ M) {p : RealVector n}
    (hp : IsMinimizer C (penaltyObjective f g M) p) :
    IsMinimizer {q ∈ weightedX ⁻¹' C | ∀ i,penaltyLiftRows g i q≤0}
      (penaltyLiftF f M) (weightedInsert p (fun _ => penaltyViolation g p)) := by
  refine ⟨⟨by simpa using hp.1,?_⟩,?_⟩
  · rw [penalty_lift_rows_iff]
    simpa only [weightedX_insert,penaltyHeight_insert] using
      And.intro (penaltyViolation_nonneg g p) (penaltyViolation_row_le g p)
  · intro q hq
    have hh := (penalty_lift_rows_iff g q).mp hq.2
    have hb := (penaltyViolation_le_iff g (weightedX q) (penaltyHeight q)).mpr hh
    have hm := hp.2 (weightedX q) hq.1
    dsimp [penaltyObjective] at hm
    simp only [penaltyLiftF,weightedX_insert,penaltyHeight_insert]
    exact hm.trans (add_le_add_right (mul_le_mul_of_nonneg_left hb hM) _)

theorem penalty_lift_slater {n l : ℕ} (C : Set (RealVector n))
    (g : Fin l → RealVector n → ℝ) (hne : C.Nonempty) :
    ∃ q ∈ weightedX ⁻¹' C, ∀ i,penaltyLiftRows g i q<0 := by
  obtain ⟨p,hp⟩ := hne
  refine ⟨weightedInsert p (fun _ => penaltyViolation g p+1),by simpa using hp,?_⟩
  intro i
  refine Fin.cases ?_ (fun j => ?_) i
  · simp only [penaltyLiftRows,Fin.cases_zero,penaltyHeight_insert]
    linarith [penaltyViolation_nonneg g p]
  · simp only [penaltyLiftRows,Fin.cases_succ,penaltyHeight_insert,weightedX_insert]
    linarith [penaltyViolation_row_le g p j]

theorem penalty_lift_rows_convex {n l : ℕ} (g : Fin l → RealVector n → ℝ)
    (hg : ∀ j,ConvexOn ℝ Set.univ (g j)) :
    ∀ i, ConvexOn ℝ Set.univ (penaltyLiftRows g i) := by
  intro i
  refine Fin.cases ?_ (fun j => ?_) i
  · exact (-penaltyHeight (n:=n)).toLinearMap.convexOn convex_univ
  · have hc : ConvexOn ℝ Set.univ (fun q : RealVector (n+1) => g j (weightedX q)) := by
      simpa only [Set.preimage_univ, Function.comp_def, ContinuousLinearMap.coe_coe] using (hg j).comp_linearMap weightedX.toLinearMap
    exact hc.sub (penaltyHeight.toLinearMap.concaveOn convex_univ)

theorem penalty_lift_rows_derivative {n l : ℕ} (g : Fin l → RealVector n → ℝ)
    (Dg : Fin l → RealVector n →L[ℝ] ℝ) {p : RealVector n}
    (hg : ∀ j,HasFDerivAt (g j) (Dg j) p) (u : ℝ) :
    ∀ i,HasFDerivAt (penaltyLiftRows g i) (penaltyLiftRowD Dg i)
      (weightedInsert p (fun _ => u)) := by
  intro i
  refine Fin.cases ?_ (fun j => ?_) i
  · exact penaltyHeight.hasFDerivAt.neg
  · exact ((show HasFDerivAt (g j) (Dg j) (weightedX (weightedInsert p (fun _ : Fin 1 => u)))
      by simpa using hg j).comp _ weightedX.hasFDerivAt).sub penaltyHeight.hasFDerivAt

def penaltyPartialD {n l : ℕ} (Df : RealVector n →L[ℝ] ℝ) (M : ℝ)
    (Dg : Fin l → RealVector n →L[ℝ] ℝ) (L : Fin (l+1) → ℝ) :
    RealVector (n+1) →L[ℝ] ℝ := penaltyLiftD Df M+∑ i,L i • penaltyLiftRowD Dg i

theorem penalty_partial_apply {n l : ℕ} (Df : RealVector n →L[ℝ] ℝ) (M : ℝ)
    (Dg : Fin l → RealVector n →L[ℝ] ℝ) (L : Fin (l+1) → ℝ)
    (q : RealVector (n+1)) : penaltyPartialD Df M Dg L q =
      Df (weightedX q)+M*penaltyHeight q-L 0*penaltyHeight q+
        ∑ j : Fin l,L j.succ*(Dg j (weightedX q)-penaltyHeight q) := by
  simp only [penaltyPartialD,penaltyLiftD,penaltyLiftRowD,ContinuousLinearMap.add_apply,
    ContinuousLinearMap.sum_apply,ContinuousLinearMap.smul_apply,smul_eq_mul,
    Fin.sum_univ_succ,Fin.cases_zero,Fin.cases_succ,ContinuousLinearMap.neg_apply,
    ContinuousLinearMap.comp_apply,ContinuousLinearMap.sub_apply]
  ring

structure PenaltyKKT {n l : ℕ} (C : Set (RealVector n))
    (g : Fin l → RealVector n → ℝ) (p : RealVector n) (u M : ℝ)
    (Df : RealVector n →L[ℝ] ℝ) (Dg : Fin l → RealVector n →L[ℝ] ℝ)
    (lambda : Fin l → ℝ) (nu : ℝ) (normal : RealVector n →L[ℝ] ℝ) : Prop where
  mem : p ∈ C
  slack_nonneg : 0 ≤ u
  rows : ∀ j,g j p ≤ u
  multiplier_nonneg : ∀ j,0 ≤ lambda j
  lower_multiplier_nonneg : 0 ≤ nu
  row_compl : ∀ j,lambda j*(g j p-u)=0
  lower_compl : nu*u=0
  balance : (∑ j,lambda j)+nu=M
  normal_le : ∀ q ∈ C, normal (q-p) ≤ 0
  stationarity : Df+(∑ j,lambda j • Dg j)+normal=0

/-- The scalar-slack lift has a strict point for every nonempty C, regardless
of original nonlinear feasibility. Its KKT certificate is derived, not assumed. -/
theorem penalty_actual_minimum_kkt {n l : ℕ} (C : Set (RealVector n))
    (f : RealVector n → ℝ) (g : Fin l → RealVector n → ℝ)
    {M : ℝ} (hM : 0≤M) (p : RealVector n)
    (Df : RealVector n →L[ℝ] ℝ) (Dg : Fin l → RealVector n →L[ℝ] ℝ)
    (hC : Convex ℝ C) (hf : ConvexOn ℝ Set.univ f)
    (hg : ∀ j,ConvexOn ℝ Set.univ (g j)) (hdf : HasFDerivAt f Df p)
    (hdg : ∀ j,HasFDerivAt (g j) (Dg j) p)
    (hp : IsMinimizer C (penaltyObjective f g M) p) :
    ∃ lambda nu normal, PenaltyKKT C g p (penaltyViolation g p) M Df Dg lambda nu normal := by
  let u := penaltyViolation g p
  let z := weightedInsert p (fun _ : Fin 1 => u)
  let P : Set (RealVector (n+1)) := weightedX ⁻¹' C
  have hP : Convex ℝ P := hC.linear_preimage weightedX.toLinearMap
  have hfc : ConvexOn ℝ Set.univ (fun q : RealVector (n+1) => f (weightedX q)) := by
    simpa only [Set.preimage_univ, Function.comp_def, ContinuousLinearMap.coe_coe] using hf.comp_linearMap weightedX.toLinearMap
  have hlc : ConvexOn ℝ Set.univ (penaltyLiftF f M) :=
    hfc.add ((M • penaltyHeight (n:=n)).toLinearMap.convexOn convex_univ)
  obtain ⟨L,hL,hcomp,hmin⟩ := convex_slater_partialLagrangian_minimum P (penaltyLiftF f M)
    (penaltyLiftRows g) z hP (hlc.subset (subset_univ _) hP)
    (fun j => (penalty_lift_rows_convex g hg j).subset (subset_univ _) hP)
    (penalty_lift_actual_minimum C f g hM hp) (penalty_lift_slater C g ⟨p,hp.1⟩)
  have hfd : HasFDerivAt (penaltyLiftF f M) (penaltyLiftD Df M) z :=
    ((show HasFDerivAt f Df (weightedX z) by simpa [z] using hdf).comp _
      weightedX.hasFDerivAt).add (penaltyHeight.hasFDerivAt.const_mul M)
  have hd : HasFDerivAt
      (fun q => penaltyLiftF f M q+∑ i,L i*penaltyLiftRows g i q)
      (penaltyPartialD Df M Dg L) z :=
    hfd.add (HasFDerivAt.fun_sum fun i _ =>
      ((penalty_lift_rows_derivative g Dg hdg u i).const_mul (L i)))
  have hdir : ∀ q : RealVector (n+1),weightedX q∈C → 0≤penaltyPartialD Df M Dg L (q-z) :=
    fun q hq => convex_minimum_derivative_nonneg hP hmin hd hq
  have hbalance : (∑ j : Fin l,L j.succ)+L 0=M := by
    have hplus := hdir (z+weightedInsert (0 : RealVector n) (fun _ : Fin 1 => 1))
      (by simpa [z] using hp.1)
    have hminus := hdir (z-weightedInsert (0 : RealVector n) (fun _ : Fin 1 => 1))
      (by simpa [z] using hp.1)
    simp only [add_sub_cancel_left,sub_sub_cancel_left,map_neg] at hplus hminus
    have he : penaltyPartialD Df M Dg L
        (weightedInsert (0 : RealVector n) (fun _ : Fin 1 => 1))=M-L 0-∑ j : Fin l,L j.succ := by
      rw [penalty_partial_apply]
      simp [sub_eq_add_neg]
    rw [he] at hplus hminus
    linarith
  let normal := -(Df+∑ j : Fin l,L j.succ • Dg j)
  refine ⟨fun j => L j.succ,L 0,normal,hp.1,penaltyViolation_nonneg g p,
    penaltyViolation_row_le g p,fun j => hL _,hL 0,?_,?_,hbalance,?_,?_⟩
  · intro j
    simpa only [z,u,penaltyLiftRows,Fin.cases_succ,weightedX_insert,penaltyHeight_insert]
      using hcomp j.succ
  · have hh := hcomp 0
    simpa only [z,u,penaltyLiftRows,Fin.cases_zero,penaltyHeight_insert,mul_neg,neg_eq_zero]
      using hh
  · intro q hq
    have hh := hdir (weightedInsert q (fun _ : Fin 1 => u)) (by simpa using hq)
    rw [penalty_partial_apply] at hh
    simp only [z,map_sub,weightedX_insert,penaltyHeight_insert,sub_self,mul_zero,
      add_zero,sub_zero,mul_sub,Finset.sum_sub_distrib] at hh
    simp only [normal,ContinuousLinearMap.neg_apply,ContinuousLinearMap.add_apply,
      ContinuousLinearMap.sum_apply,ContinuousLinearMap.smul_apply,smul_eq_mul,map_sub]
    linarith
  · dsimp [normal]; abel


theorem penalty_tangent_lower {n l : ℕ} {C : Set (RealVector n)}
    {g : Fin l → RealVector n → ℝ} {p : RealVector n} {u M : ℝ}
    {Df : RealVector n →L[ℝ] ℝ} {Dg : Fin l → RealVector n →L[ℝ] ℝ}
    {lambda : Fin l → ℝ} {nu : ℝ} {normal : RealVector n →L[ℝ] ℝ}
    (hk : PenaltyKKT C g p u M Df Dg lambda nu normal)
    {q : RealVector n} (hq : q∈C) :
    M*u-Df (q-p) ≤ ∑ j,lambda j*(g j p+Dg j (q-p)) := by
  have hconst : (∑ j,lambda j*g j p)=M*u := by
    have hr : ∀ j,lambda j*g j p=lambda j*u := by
      intro j; nlinarith [hk.row_compl j]
    simp only [hr,←Finset.sum_mul]
    rw [←hk.balance,add_mul,hk.lower_compl,add_zero]
  have he := congrArg (fun D : RealVector n →L[ℝ] ℝ => D (q-p)) hk.stationarity
  simp only [ContinuousLinearMap.add_apply,ContinuousLinearMap.sum_apply,
    ContinuousLinearMap.smul_apply,smul_eq_mul,ContinuousLinearMap.zero_apply] at he
  rw [show (∑ j,lambda j*(g j p+Dg j (q-p)))=
      (∑ j,lambda j*g j p)+(∑ j,lambda j*Dg j (q-p)) by
        simp only [mul_add,Finset.sum_add_distrib],hconst]
  linarith [hk.normal_le q hq]

theorem penalty_kkt_excludes_of_derivative_bound {n l : ℕ} {C : Set (RealVector n)}
    {g : Fin l → RealVector n → ℝ} {p : RealVector n} {u M : ℝ}
    {Df : RealVector n →L[ℝ] ℝ} {Dg : Fin l → RealVector n →L[ℝ] ℝ}
    {lambda : Fin l → ℝ} {nu : ℝ} {normal : RealVector n →L[ℝ] ℝ}
    (hk : PenaltyKKT C g p u M Df Dg lambda nu normal)
    (hbound : ∀ q ∈ C, Df (q-p)<M*u) :
    ¬ ∃ q ∈ C, ∀ j, g j p+Dg j (q-p)≤0 := by
  rintro ⟨q,hq,hcuts⟩
  have ht := penalty_tangent_lower hk hq
  have hs : (∑ j,lambda j*(g j p+Dg j (q-p)))≤0 :=
    Finset.sum_nonpos fun j _ => mul_nonpos_of_nonneg_of_nonpos (hk.multiplier_nonneg j) (hcuts j)
  linarith [hbound q hq]

/-- Quantified infeasible-fiber exclusion. rho is a proved positive uniform
violation margin, Delta a proved objective oscillation bound on the full domain.
The domain normal remains in the derivation; it is not set to zero. -/
theorem penalty_actual_minimum_excludes {n l : ℕ} (C : Set (RealVector n))
    (f : RealVector n → ℝ) (g : Fin l → RealVector n → ℝ)
    {M rho Delta : ℝ} (hM : 0≤M) (p : RealVector n)
    (Df : RealVector n →L[ℝ] ℝ) (Dg : Fin l → RealVector n →L[ℝ] ℝ)
    (hC : Convex ℝ C) (hf : ConvexOn ℝ Set.univ f)
    (hg : ∀ j,ConvexOn ℝ Set.univ (g j)) (hdf : HasFDerivAt f Df p)
    (hdg : ∀ j,HasFDerivAt (g j) (Dg j) p)
    (hp : IsMinimizer C (penaltyObjective f g M) p)
    (hrho : 0<rho) (hmargin : ∀ x ∈ C, rho≤penaltyViolation g x)
    (hosc : ∀ x ∈ C, ∀ y ∈ C, f x-f y≤Delta) (hlarge : Delta<M*rho) :
    ¬ ∃ q ∈ C, ∀ j, g j p+Dg j (q-p)≤0 := by
  obtain ⟨lambda,nu,normal,hk⟩ := penalty_actual_minimum_kkt C f g hM p Df Dg hC hf hg hdf hdg hp
  apply penalty_kkt_excludes_of_derivative_bound hk
  intro q hq
  have ht := tangent_underestimator hf hdf (b:=q)
  have ho := hosc q hq p hp.1
  have hu : 0 < penaltyViolation g p := hrho.trans_le (hmargin p hp.1)
  have hm := mul_le_mul_of_nonneg_left (hmargin p hp.1) hM
  linarith

/-- Positive uniform margins exist on compact nonempty infeasible domains.
This supplies an actual margin rather than a solver infeasibility flag. -/
theorem penalty_positive_margin_exists {E : Type*} [TopologicalSpace E] {l : ℕ}
    (C : Set E) (g : Fin l → E → ℝ) (hC : IsCompact C) (hne : C.Nonempty)
    (hg : ∀j,Continuous (g j)) (hempty : ¬∃x∈C,∀j,g j x≤0) :
    ∃rho,0<rho ∧ ∀ x ∈ C, rho≤penaltyViolation g x := by
  obtain ⟨p,hp⟩ := compact_feasible_attainment hC hne (penaltyViolation_continuous g hg).continuousOn
  refine ⟨penaltyViolation g p,?_,hp.2⟩
  have hn := penaltyViolation_nonneg g p
  refine lt_of_le_of_ne hn ?_
  intro he
  exact hempty ⟨p,hp.1,(penaltyViolation_eq_zero_iff g p).mp he.symm⟩

theorem penalty_zero_rows_value {E : Type*} (g : Fin 0 → E → ℝ) (x : E) :
    penaltyViolation g x=0 := (penaltyViolation_eq_zero_iff g x).mpr (fun j => Fin.elim0 j)

theorem penalty_zero_rows_positive_iff {E : Type*} (C : Set E) (f : E → ℝ)
    (g : Fin 0 → E → ℝ) {M : ℝ} (hM : 0<M) (q : E × ℝ) :
    IsMinimizer (penaltyPairs C g) (fun z => f z.1+M*z.2) q ↔
      IsMinimizer C f q.1 ∧ q.2=0 := by
  rw [penalty_pairs_minimizer_iff C f g hM]
  have he : penaltyObjective f g M=f := by
    funext x
    simp only [penaltyObjective,penalty_zero_rows_value,mul_zero,add_zero]
  rw [he,penalty_zero_rows_value]

theorem penalty_zero_coefficient_any_height {E : Type*} {l : ℕ} (C : Set E)
    (f : E → ℝ) (g : Fin l → E → ℝ) {p : E} (hp : IsMinimizer C f p)
    {u : ℝ} (hu : 0≤u) (hg : ∀j,g j p≤u) :
    IsMinimizer (penaltyPairs C g) (fun z => f z.1+0*z.2) (p,u) := by
  refine ⟨⟨hp.1,hu,hg⟩,?_⟩
  intro q hq
  simpa using hp.2 q.1 hq.1

/-- With a negative coefficient, increasing an admissible slack strictly
improves the objective. No minimum exists, even for nonempty compact C. -/
theorem penalty_negative_no_minimum {E : Type*} {l : ℕ} (C : Set E)
    (f : E → ℝ) (g : Fin l → E → ℝ) {M : ℝ} (hM : M<0) :
    ¬∃q,IsMinimizer (penaltyPairs C g) (fun z => f z.1+M*z.2) q := by
  rintro ⟨q,hq⟩
  have hm := hq.2 (q.1,q.2+1)
    ⟨hq.1.1,by dsimp; linarith [hq.1.2.1],fun j => (hq.1.2.2 j).trans (by dsimp; linarith)⟩
  dsimp at hm
  nlinarith

theorem penalty_empty_domain_no_minimum {E : Type*} {l : ℕ}
    (f : E → ℝ) (g : Fin l → E → ℝ) (M : ℝ) :
    ¬∃q,IsMinimizer (penaltyPairs ∅ g) (fun z => f z.1+M*z.2) q := by
  rintro ⟨q,hq⟩
  exact hq.1.1

end Chapter02

#print axioms Chapter02.penaltyViolation_le_iff
#print axioms Chapter02.penaltyViolation_nonneg
#print axioms Chapter02.penaltyViolation_row_le
#print axioms Chapter02.penaltyViolation_eq_zero_iff
#print axioms Chapter02.penaltyViolation_continuous
#print axioms Chapter02.penalty_pairs_minimizer_iff
#print axioms Chapter02.penalty_minimum_exists
#print axioms Chapter02.penalty_pairs_minimum_exists
#print axioms Chapter02.penalty_exact_of_support
#print axioms Chapter02.penalty_quantified_feasible_exactness
#print axioms Chapter02.penaltyHeight_insert
#print axioms Chapter02.penalty_lift_rows_iff
#print axioms Chapter02.penalty_lift_actual_minimum
#print axioms Chapter02.penalty_lift_slater
#print axioms Chapter02.penalty_lift_rows_convex
#print axioms Chapter02.penalty_lift_rows_derivative
#print axioms Chapter02.penalty_partial_apply
#print axioms Chapter02.penalty_actual_minimum_kkt
#print axioms Chapter02.penalty_tangent_lower
#print axioms Chapter02.penalty_kkt_excludes_of_derivative_bound
#print axioms Chapter02.penalty_actual_minimum_excludes
#print axioms Chapter02.penalty_positive_margin_exists
#print axioms Chapter02.penalty_zero_rows_value
#print axioms Chapter02.penalty_zero_rows_positive_iff
#print axioms Chapter02.penalty_zero_coefficient_any_height
#print axioms Chapter02.penalty_negative_no_minimum
#print axioms Chapter02.penalty_empty_domain_no_minimum
