module

public import Chapter02DICOPTModel
public import Chapter02DICOPTControlGeometry
public import Mathlib.Analysis.Convex.Mul
public import Mathlib.Analysis.Convex.Quasiconvex
public import Mathlib.Analysis.Calculus.LocalExtr.Basic
public import Mathlib.Analysis.Calculus.MeanValue
public import Mathlib.Analysis.Calculus.Deriv.Pow

@[expose] public section

noncomputable section
open Set Filter
open scoped Topology

namespace Chapter02.DICOPTQuasiconvex

def f (x : ℝ) : ℝ := (3/10)*x^4 - (4/5)*x + 19/10
def h (x : ℝ) : ℝ := (x^3+x)/2
def objective (p : ℝ × ℝ) : ℝ := -p.2 + f p.1
def original : Set (ℝ × ℝ) :=
  {p | p.1 ∈ Icc (-1) 0 ∧ (p.2 = 0 ∨ p.2 = 1) ∧ p.2 + h p.1 = 0}
def relaxed : Set (ℝ × ℝ) :=
  {p | p.1 ∈ Icc (-1) 0 ∧ p.2 ∈ Icc 0 1 ∧ p.2 + h p.1 = 0}
def hardMaster : Set (ℝ × ℝ × ℝ) :=
  {p | p.1 ∈ Icc (-1) 0 ∧ (p.2.1 = 0 ∨ p.2.1 = 1) ∧
    1-2*p.1 ≤ p.2.2 ∧ p.2.1+2*p.1+1 ≤ 0}
def hardObjective (p : ℝ × ℝ × ℝ) : ℝ := -p.2.1+p.2.2

theorem f_deriv (x : ℝ) : HasDerivAt f ((6/5)*x^3-4/5) x := by
  convert ((((hasDerivAt_id x).pow 4).const_mul (3/10)).sub
    ((hasDerivAt_id x).const_mul (4/5))).add_const (19/10) using 1 <;>
    (try ext z) <;> norm_num [f, Function.comp_def] <;> ring

theorem h_deriv (x : ℝ) : HasDerivAt h ((3*x^2+1)/2) x := by
  convert (((hasDerivAt_id x).pow 3).add (hasDerivAt_id x)).div_const 2 using 1 <;>
    (try ext z) <;> norm_num [h, Function.comp_def] <;> ring

theorem h_deriv_positive (x : ℝ) : 0 < (3*x^2+1)/2 := by positivity

theorem h_strictMono : StrictMono h := by
  apply strictMono_of_deriv_pos
  intro x
  rw [(h_deriv x).deriv]
  exact h_deriv_positive x

theorem h_quasiconvex : QuasiconvexOn ℝ univ h :=
  h_strictMono.monotone.quasiconvexOn

theorem f_convex : ConvexOn ℝ univ f := by
  have hp : ConvexOn ℝ univ (fun x : ℝ => x^4) := (show Even (4 : ℕ) by decide).convexOn_pow
  have hi : ConvexOn ℝ univ (fun x : ℝ => -(4/5)*x) := by
    refine ⟨convex_univ, ?_⟩
    intro x hx y hy a b ha hb hab
    simp only [smul_eq_mul]
    ring_nf
    exact le_rfl
  apply (((hp.smul (by norm_num : (0 : ℝ) ≤ 3/10)).add hi).add_const (19/10)).congr
  intro x hx
  simp [f, Pi.add_apply, Pi.smul_apply]
  ring

theorem relaxed_gap (x : ℝ) : objective (x,-h x)-2 = (x+1)^2*(3*x^2-x-1)/10 := by
  dsimp [objective, f, h]
  ring

theorem local_gap_bound {x : ℝ} (hx : x ∈ Icc (-1) (-(3/4))) :
    (23/160)*(x+1)^2 ≤ objective (x,-h x)-2 := by
  rw [relaxed_gap]
  have hp : 0 ≤ (x+3/4)*(3*x-13/4) := mul_nonneg_of_nonpos_of_nonpos (by linarith [hx.2]) (by linarith [hx.2])
  nlinarith [sq_nonneg (x+1), mul_nonneg (sq_nonneg (x+1)) hp]

theorem original_points {p : ℝ × ℝ} : p ∈ original ↔ p = (-1,1) ∨ p = (0,0) := by
  constructor
  · rintro ⟨hx, hy, he⟩
    rcases hy with hy | hy
    · have hh : h p.1 = h 0 := by norm_num [h] at *; linarith
      have hh' := h_strictMono.injective hh
      right
      exact Prod.ext hh' hy
    · have hh : h p.1 = h (-1) := by norm_num [h] at *; linarith
      have hh' := h_strictMono.injective hh
      left
      exact Prod.ext hh' hy
  · rintro (rfl | rfl) <;> norm_num [original, h]

theorem original_minimum : IsMinimizer original objective (0,0) := by
  constructor
  · exact original_points.mpr (Or.inr rfl)
  · intro p hp
    rcases original_points.mp hp with rfl | rfl <;> norm_num [objective, f]

theorem hard_minimum : IsMinimizer hardMaster hardObjective (-1,1,3) := by
  constructor
  · norm_num [hardMaster]
  · rintro p ⟨hx, hy, ha, he⟩
    dsimp [hardObjective]
    linarith

theorem hard_minimum_gap : hardObjective (-1,1,3) - objective (0,0) = 1/10 := by
  norm_num [hardObjective, objective, f]

theorem local_strict_on_open_set :
    IsOpen {p : ℝ × ℝ | p.1 < -(3/4)} ∧
    ((-1,1) : ℝ × ℝ) ∈ {p | p.1 < -(3/4)} ∧
    ∀ p ∈ ({p : ℝ × ℝ | p.1 < -(3/4)} ∩ relaxed),
      p ≠ (-1,1) → objective (-1,1) < objective p := by
  refine ⟨isOpen_lt continuous_fst continuous_const, by norm_num, ?_⟩
  intro p hp hne
  have hx : p.1 ∈ Icc (-1) (-(3/4)) := ⟨hp.2.1.1, le_of_lt hp.1⟩
  have hy : p.2 = -h p.1 := by linarith [hp.2.2.2]
  have hxne : p.1 + 1 ≠ 0 := by
    intro hh
    have hpx : p.1 = -1 := by linarith
    apply hne
    apply Prod.ext hpx
    rw [hy, hpx]
    norm_num [h]
  have hg := local_gap_bound hx
  have he : (p.1, -h p.1) = p := Prod.ext rfl hy.symm
  rw [he] at hg
  have hpos : 0 < (23/160 : ℝ)*(p.1+1)^2 := mul_pos (by norm_num) (sq_pos_of_ne_zero hxne)
  have ha : objective (-1,1) = 2 := by norm_num [objective, f]
  rw [ha]
  linarith

theorem local_minimum : IsLocalMinOn objective relaxed (-1,1) := by
  change ∀ᶠ p in 𝓝[relaxed] (-1,1), objective (-1,1) ≤ objective p
  have hn : {p : ℝ × ℝ | p.1 < -(3/4)} ∈ 𝓝 (-1,1) :=
    local_strict_on_open_set.1.mem_nhds local_strict_on_open_set.2.1
  filter_upwards [mem_nhdsWithin_of_mem_nhds hn, self_mem_nhdsWithin] with p hp hpr
  by_cases he : p = (-1,1)
  · simp [he]
  · exact (local_strict_on_open_set.2.2 p ⟨hp,hpr⟩ he).le

theorem relaxed_anchor_feasible : ((-1,1) : ℝ × ℝ) ∈ relaxed := by
  norm_num [relaxed, h]

theorem relaxed_anchor_not_global : ¬ IsMinimizer relaxed objective (-1,1) := by
  intro hm
  have hp : ((0,0) : ℝ × ℝ) ∈ relaxed := by norm_num [relaxed, h]
  have hh := hm.2 (0,0) hp
  norm_num [objective, f] at hh

theorem joint_residual_not_quasiconvex :
    ¬ QuasiconvexOn ℝ (Icc (-1 : ℝ) 0 ×ˢ Icc (0 : ℝ) 1)
      (fun p : ℝ × ℝ => p.2+h p.1) := by
  intro hq
  have hx : ((-1,1) : ℝ × ℝ) ∈ {p ∈ Icc (-1 : ℝ) 0 ×ˢ Icc (0 : ℝ) 1 | p.2+h p.1 ≤ 0} := by
    norm_num [h]
  have hy : ((0,0) : ℝ × ℝ) ∈ {p ∈ Icc (-1 : ℝ) 0 ×ˢ Icc (0 : ℝ) 1 | p.2+h p.1 ≤ 0} := by
    norm_num [h, Set.mem_setOf_eq, Set.mem_prod, Set.mem_Icc, Prod.le_def]
  have hm := hq 0 hx hy (a := (1/2 : ℝ)) (b := (1/2 : ℝ)) (by norm_num) (by norm_num) (by norm_num)
  norm_num [h] at hm

def scalarFiber (y : ℝ) : Set ℝ := {x | x ∈ Icc (-1) 0 ∧ y+h x=0}
def linearizedCone (a : ℝ) : Set ℝ :=
  {v | ((3*a^2+1)/2)*v=0 ∧ (a = -1 → 0 ≤ v) ∧ (a = 0 → v ≤ 0)}

theorem scalarFiber_singleton {a y : ℝ} (ha : a ∈ Icc (-1) 0) (he : y+h a=0) :
    scalarFiber y = {a} := by
  ext x
  constructor
  · rintro ⟨hx,hxe⟩
    exact mem_singleton_iff.mpr (h_strictMono.injective (by linarith))
  · rintro rfl
    exact ⟨ha,he⟩

theorem linearizedCone_singleton (a : ℝ) : linearizedCone a = {0} := by
  ext v
  constructor
  · rintro ⟨hv,_,_⟩
    exact mem_singleton_iff.mpr ((mul_eq_zero.mp hv).resolve_left (ne_of_gt (h_deriv_positive a)))
  · rintro rfl
    simp [linearizedCone]

theorem fixed_fiber_abadie {a y : ℝ} (ha : a ∈ Icc (-1) 0) (he : y+h a=0) :
    posTangentConeAt (scalarFiber y) a = linearizedCone a := by
  rw [scalarFiber_singleton ha he, DICOPTControlGeometry.singleton_posTangentCone,
    linearizedCone_singleton]

theorem h_not_convex : ¬ ConvexOn ℝ (Icc (-1) 0) h := by
  intro hc
  have hx : (-1 : ℝ) ∈ Icc (-1) 0 := by norm_num
  have hy : (0 : ℝ) ∈ Icc (-1) 0 := by norm_num
  have hh := hc.2 hx hy (by norm_num : (0 : ℝ) ≤ 1/2)
    (by norm_num : (0 : ℝ) ≤ 1/2) (by norm_num)
  norm_num [h] at hh

theorem second_hard_minimum : IsMinimizer hardMaster hardObjective (-(1/2),0,2) := by
  constructor
  · norm_num [hardMaster]
  · rintro p ⟨hx,hy,ha,he⟩
    dsimp [hardObjective]
    linarith

theorem both_fixed_fiber_cones :
    posTangentConeAt (scalarFiber 1) (-1) = {0} ∧ linearizedCone (-1) = {0} ∧
    posTangentConeAt (scalarFiber 0) 0 = {0} ∧ linearizedCone 0 = {0} := by
  refine ⟨?_, linearizedCone_singleton _, ?_, linearizedCone_singleton _⟩
  · rw [fixed_fiber_abadie (by norm_num : (-1 : ℝ) ∈ Icc (-1) 0) (by norm_num [h]),
      linearizedCone_singleton]
  · rw [fixed_fiber_abadie (by norm_num : (0 : ℝ) ∈ Icc (-1) 0) (by norm_num [h]),
      linearizedCone_singleton]


end Chapter02.DICOPTQuasiconvex
