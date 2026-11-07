module

public import Chapter03FPTraceCommon
public import Chapter03FPUnboundedModel
public import Chapter03FPUnboundedProcedureModel
public import Chapter03OAKKTSource
public import Mathlib.Tactic.FinCases
public import Mathlib.Tactic.Positivity

@[expose] public section

/-! Exact analytic helpers for the unrestricted, success-exclusion-disabled
pump controls. These contain no feasibility or progress oracle assumptions. -/
noncomputable section
open scoped BigOperators RealInnerProductSpace
open Chapter02 Chapter03.FP
namespace Chapter03.FPUnboundedControls

abbrev P := Point 0 1
abbrev Q := Point 1 1

def pt (y : ℝ) : P := (fun i => Fin.elim0 i, fun _ => y)
def xy (x y : ℝ) : Q := (fun _ => x, fun _ => y)
def iv (y : ℤ) : IntVector 1 := fun _ => y

def yc (n : ℕ) : Point n 1 →L[ℝ] ℝ :=
  (ContinuousLinearMap.proj 0).comp (ContinuousLinearMap.snd ℝ _ _)
def xc : Q →L[ℝ] ℝ :=
  (ContinuousLinearMap.proj 0).comp (ContinuousLinearMap.fst ℝ _ _)

@[simp] theorem yc_apply {n : ℕ} (p : Point n 1) : yc n p = p.2 0 := rfl
@[simp] theorem xc_apply (p : Q) : xc p = p.1 0 := rfl
@[simp] theorem pt_snd (y : ℝ) (j : Fin 1) : (pt y).2 j = y := rfl
@[simp] theorem xy_fst (x y : ℝ) (j : Fin 1) : (xy x y).1 j = x := rfl
@[simp] theorem xy_snd (x y : ℝ) (j : Fin 1) : (xy x y).2 j = y := rfl
@[simp] theorem iv_apply (y : ℤ) (j : Fin 1) : iv y j = y := rfl

theorem pt_eta (p : P) : pt (p.2 0) = p := by
  apply Prod.ext
  · exact Subsingleton.elim _ _
  · funext j; fin_cases j; rfl

theorem xy_eta (p : Q) : xy (p.1 0) (p.2 0) = p := by
  apply Prod.ext <;> funext j <;> fin_cases j <;> rfl

theorem scalar_integer {n : ℕ} (p : Point n 1) :
    (∃ y : IntVector 1, p.2 = intCast y) ↔ ∃ k : ℤ, p.2 0 = k := by
  constructor
  · rintro ⟨y, hy⟩; exact ⟨y 0, congrFun hy 0⟩
  · rintro ⟨k, hk⟩; refine ⟨iv k, ?_⟩
    funext j; fin_cases j; exact hk

theorem scalar_distance {n : ℕ} (y : IntVector 1) (p : Point n 1) :
    distance y p = ((y 0 : ℝ) - p.2 0)^2 := by
  simp [distance, intY, intCast, Chapter03.yMap, PiLp.norm_sq_eq_of_L2,
    Fin.sum_univ_one, Real.norm_eq_abs, sq_abs]

theorem scalar_l1 {n : ℕ} (p q : Point n 1) : l1 p q = |q.2 0-p.2 0| := by
  simp [l1, Fin.sum_univ_one]

theorem scalar_normal {n : ℕ} (e : Event n 1) (p : Point n 1) :
    e.normal p = (e.projection.2 0 - (e.target 0 : ℝ)) *
      (p.2 0 - e.projection.2 0) := by
  simp [Event.normal, Chapter03.yMap, intY, intCast, PiLp.inner_apply,
    Fin.sum_univ_one, real_inner_eq_re_inner]
  ring

theorem square_derivative {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (L : E →L[ℝ] ℝ) (c : ℝ) (p : E) :
    HasFDerivAt (fun q => (L q-c)^2) ((2*(L p-c)) • L) p :=
  FPTrace.square_derivative L c p

theorem square_convex {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {S : Set E} (hS : Convex ℝ S) (L : E →L[ℝ] ℝ) (c : ℝ) :
    ConvexOn ℝ S (fun p => (L p-c)^2) := FPTrace.square_convex hS L c

theorem scalar_square_not_affine (c r : ℝ) :
    ¬ OAKKT.AffineRow (fun p : P => (p.2 0-c)^2-r) := by
  intro h
  have hd : HasFDerivAt (fun p : P => (p.2 0-c)^2-r) (0 : P →L[ℝ] ℝ) (pt c) := by
    simpa using (square_derivative (yc 0) c (pt c)).sub_const r
  have ht := OAKKT.affine_tangent h hd (pt (c+1))
  norm_num at ht
  linarith

theorem binary_value {k : ℤ} (h0 : 0 ≤ (k:ℝ)) (h1 : (k:ℝ) ≤ 1) :
    k=0 ∨ k=1 := by
  have h0' : 0 ≤ k := by exact_mod_cast h0
  have h1' : k ≤ 1 := by exact_mod_cast h1
  omega

theorem master_rows {n m l : ℕ} (d : FPUnbounded.Data n m l) (s : State n m)
    (z : Point n m × ℝ) : z ∈ FPUnbounded.master d s ↔
    z.1 ∈ d.base ∧ (∃ y : IntVector m, z.1.2 = intCast y) ∧
    (∀ a ∈ FPUnbounded.anchors d s,
      d.f a.point + d.Df a.point (z.1-a.point) ≤ z.2 ∧
      ∀ j ∈ a.selected, d.g j a.point + d.Dg j a.point (z.1-a.point) ≤ 0) ∧
    retainedNormals s z.1 ∧ Allows (d.level s.incumbent) z.2 := by
  constructor
  · rintro ⟨⟨hb, hi, hg, hf⟩, hn, hc⟩
    refine ⟨hb, hi, ?_, hn, hc⟩
    intro a ha
    obtain ⟨i, rfl⟩ := List.mem_iff_get.mp ha
    exact ⟨hf i, hg i⟩
  · rintro ⟨hb, hi, hr, hn, hc⟩
    refine ⟨⟨hb, hi, ?_, ?_⟩, hn, hc⟩
    · intro i; exact (hr _ (List.get_mem _ _)).2
    · intro i; exact (hr _ (List.get_mem _ _)).1

def patch {n m l : ℕ} {d : FPUnbounded.Data n m l} {cap : Option ℕ}
    (atState : State n m) (dec : FPUnbounded.Decision d cap atState)
    (fallback : FPUnbounded.Selector d cap) : FPUnbounded.Selector d cap := by
  classical
  exact fun s => if h : s=atState then h.symm ▸ dec else fallback s

@[simp] theorem patch_same {n m l : ℕ} {d : FPUnbounded.Data n m l} {cap : Option ℕ}
    (s : State n m) (dec : FPUnbounded.Decision d cap s) (fallback : FPUnbounded.Selector d cap) :
    patch s dec fallback s = dec := by simp [patch]

theorem patch_other {n m l : ℕ} {d : FPUnbounded.Data n m l} {cap : Option ℕ}
    (s t : State n m) (dec : FPUnbounded.Decision d cap s) (fallback : FPUnbounded.Selector d cap)
    (h : t≠s) : patch s dec fallback t = fallback t := by simp [patch,h]

end Chapter03.FPUnboundedControls
