module

public import Chapter02
public import Mathlib.Analysis.LocallyConvex.Separation
public import Mathlib.LinearAlgebra.StdBasis
public import Mathlib.Tactic.FunProp
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.FieldSimp

@[expose] public section

/-! Nonlinear Slater on an arbitrary convex domain. The theorem derives
nonnegative multipliers and a partial-Lagrangian minimum on the domain;
it makes no affine strict-feasibility or ambient stationarity assumption. -/

noncomputable section
open scoped BigOperators Topology
namespace Chapter02

def slaterUpperImage {n l : ℕ} (P : Set (RealVector n))
    (f : RealVector n → ℝ) (g : Fin l → RealVector n → ℝ)
    (p : RealVector n) : Set (RealVector (l+1)) :=
  {u | ∃ x ∈ P, f x - f p < u 0 ∧ ∀ j, g j x < u j.succ}

theorem slaterUpperImage_isOpen {n l : ℕ} (P : Set (RealVector n))
    (f : RealVector n → ℝ) (g : Fin l → RealVector n → ℝ)
    (p : RealVector n) : IsOpen (slaterUpperImage P f g p) := by
  have heq : slaterUpperImage P f g p =
      ⋃ x ∈ P, {u | f x - f p < u 0} ∩ ⋂ j, {u | g j x < u j.succ} := by
    ext u
    simp [slaterUpperImage, and_comm, and_left_comm, and_assoc]
  rw [heq]
  exact isOpen_iUnion fun x => isOpen_iUnion fun _ =>
    (isOpen_lt continuous_const (continuous_apply 0)).inter
      (isOpen_iInter_of_finite fun j =>
        isOpen_lt continuous_const (continuous_apply j.succ))

theorem slaterUpperImage_convex {n l : ℕ} (P : Set (RealVector n))
    (f : RealVector n → ℝ) (g : Fin l → RealVector n → ℝ)
    (p : RealVector n) (hP : Convex ℝ P) (hf : ConvexOn ℝ P f)
    (hg : ∀ j, ConvexOn ℝ P (g j)) : Convex ℝ (slaterUpperImage P f g p) := by
  intro u hu v hv a b ha hb hab
  obtain ⟨x,hx,hfx,hgx⟩ := hu
  obtain ⟨y,hy,hfy,hgy⟩ := hv
  refine ⟨a • x + b • y, hP hx hy ha hb hab, ?_, ?_⟩
  · have hc := hf.2 hx hy ha hb hab
    have hs : a * (f x-f p) + b * (f y-f p) < a * u 0 + b * v 0 := by
      rcases lt_or_eq_of_le ha with ha' | ha'
      · exact add_lt_add_of_lt_of_le (mul_lt_mul_of_pos_left hfx ha')
          (mul_le_mul_of_nonneg_left hfy.le hb)
      · have hb' : 0 < b := by linarith
        exact add_lt_add_of_le_of_lt (mul_le_mul_of_nonneg_left hfx.le ha)
          (mul_lt_mul_of_pos_left hfy hb')
    change f (a • x + b • y) - f p < a * u 0 + b * v 0
    change f (a • x + b • y) ≤ a * f x + b * f y at hc
    have hfp : a * f p + b * f p = f p := by rw [← add_mul, hab, one_mul]
    nlinarith only [hs, hc, hfp]
  · intro j
    have hc := (hg j).2 hx hy ha hb hab
    change g j (a • x + b • y) ≤ a * g j x + b * g j y at hc
    change g j (a • x + b • y) < a * u j.succ + b * v j.succ
    apply lt_of_le_of_lt hc
    rcases lt_or_eq_of_le ha with ha' | ha'
    · exact add_lt_add_of_lt_of_le (mul_lt_mul_of_pos_left (hgx j) ha')
        (mul_le_mul_of_nonneg_left (hgy j).le hb)
    · have hb' : 0 < b := by linarith
      exact add_lt_add_of_le_of_lt (mul_le_mul_of_nonneg_left (hgx j).le ha)
        (mul_lt_mul_of_pos_left (hgy j) hb')

theorem slaterUpperImage_nonempty {n l : ℕ} (P : Set (RealVector n))
    (f : RealVector n → ℝ) (g : Fin l → RealVector n → ℝ)
    (p : RealVector n) (hP : P.Nonempty) : (slaterUpperImage P f g p).Nonempty := by
  obtain ⟨x,hx⟩ := hP
  refine ⟨Fin.cons (f x-f p+1) (fun j => g j x+1), x, hx, ?_, ?_⟩
  · simp
  · intro j
    simp

theorem slaterUpperImage_zero_not_mem {n l : ℕ} (P : Set (RealVector n))
    (f : RealVector n → ℝ) (g : Fin l → RealVector n → ℝ)
    (p : RealVector n)
    (hmin : IsMinimizer {x ∈ P | ∀ j, g j x ≤ 0} f p) :
    (0 : RealVector (l+1)) ∉ slaterUpperImage P f g p := by
  rintro ⟨x,hx,hfx,hgx⟩
  have h := hmin.2 x ⟨hx, fun j => (hgx j).le⟩
  change f x-f p < 0 at hfx
  linarith

theorem slaterFunctional_coordinates {k : ℕ} (L : RealVector k →L[ℝ] ℝ)
    (u : RealVector k) : L u = ∑ i, L (Pi.single i 1) * u i := by
  classical
  have h := congrArg L ((Pi.basisFun ℝ (Fin k)).sum_repr u)
  simpa [map_sum, map_smul, mul_comm] using h.symm

theorem slaterUpperImage_mono {n l : ℕ} (P : Set (RealVector n))
    (f : RealVector n → ℝ) (g : Fin l → RealVector n → ℝ)
    (p : RealVector n) {u v : RealVector (l+1)}
    (hu : u ∈ slaterUpperImage P f g p) (huv : u ≤ v) :
    v ∈ slaterUpperImage P f g p := by
  obtain ⟨x,hx,hf,hg⟩ := hu
  exact ⟨x,hx,hf.trans_le (huv 0),fun j => (hg j).trans_le (huv j.succ)⟩

theorem slater_separator_coefficients_nonneg {n l : ℕ} (P : Set (RealVector n))
    (f : RealVector n → ℝ) (g : Fin l → RealVector n → ℝ)
    (p : RealVector n) (L : RealVector (l+1) →L[ℝ] ℝ)
    (hne : (slaterUpperImage P f g p).Nonempty)
    (hsep : ∀ u ∈ slaterUpperImage P f g p, 0 < L u) :
    ∀ i, 0 ≤ L (Pi.single i 1) := by
  classical
  obtain ⟨u,hu⟩ := hne
  intro i
  by_contra hi
  have hi' : L (Pi.single i 1) < 0 := lt_of_not_ge hi
  let t : ℝ := -(L u+1) / L (Pi.single i 1)
  have ht : 0 ≤ t := le_of_lt (div_pos_of_neg_of_neg (by linarith [hsep u hu]) hi')
  have hv : u + t • (Pi.single i 1 : RealVector (l+1)) ∈ slaterUpperImage P f g p := by
    apply slaterUpperImage_mono P f g p hu
    intro j
    change u j ≤ u j + t * (Pi.single i 1 : RealVector (l+1)) j
    by_cases hji : j = i
    · subst j
      simpa using ht
    · simp [Pi.single_eq_of_ne hji]
  have hs := hsep _ hv
  have heq : L (u + t • (Pi.single i 1 : RealVector (l+1))) = -1 := by
    simp only [map_add, map_smul, smul_eq_mul]
    dsimp [t]
    rw [div_mul_cancel₀ _ (ne_of_lt hi')]
    ring
  linarith

theorem slater_separator_boundary {n l : ℕ} (P : Set (RealVector n))
    (f : RealVector n → ℝ) (g : Fin l → RealVector n → ℝ)
    (p : RealVector n) (L : RealVector (l+1) →L[ℝ] ℝ)
    (hsep : ∀ u ∈ slaterUpperImage P f g p, 0 < L u)
    {x : RealVector n} (hx : x ∈ P) :
    0 ≤ L (Fin.cons (f x-f p) (fun j => g j x)) := by
  let v : RealVector (l+1) := Fin.cons (f x-f p) (fun j => g j x)
  have hc : Continuous (fun e : ℝ => L (v + e • (1 : RealVector (l+1)))) := by
    fun_prop
  have ht := hc.continuousAt.tendsto.mono_left
    (show nhdsWithin (0 : ℝ) (Set.Ioi 0) ≤ nhds 0 from inf_le_left)
  have he : ∀ᶠ e : ℝ in nhdsWithin 0 (Set.Ioi 0),
      0 ≤ L (v + e • (1 : RealVector (l+1))) := by
    filter_upwards [self_mem_nhdsWithin] with e he
    apply (hsep _ ?_).le
    refine ⟨x,hx,?_,?_⟩
    · change f x-f p < f x-f p+e*1
      simpa using he
    · intro j
      change g j x < g j x+e*1
      simpa using he
  simpa [v] using ge_of_tendsto ht he

theorem slater_separator_objective_pos {n l : ℕ} (P : Set (RealVector n))
    (f : RealVector n → ℝ) (g : Fin l → RealVector n → ℝ)
    (p : RealVector n) (L : RealVector (l+1) →L[ℝ] ℝ)
    (hne : (slaterUpperImage P f g p).Nonempty)
    (hsep : ∀ u ∈ slaterUpperImage P f g p, 0 < L u)
    (hslater : ∃ z ∈ P, ∀ j, g j z < 0) :
    0 < L (Pi.single 0 1) := by
  classical
  have ha := slater_separator_coefficients_nonneg P f g p L hne hsep
  by_contra hpos
  have hzero : L (Pi.single 0 1) = 0 := le_antisymm (le_of_not_gt hpos) (ha 0)
  obtain ⟨z,hz,hgz⟩ := hslater
  have hb := slater_separator_boundary P f g p L hsep hz
  rw [slaterFunctional_coordinates, Fin.sum_univ_succ] at hb
  simp only [Fin.cons_zero, Fin.cons_succ, hzero, zero_mul, zero_add] at hb
  have hterms : ∀ j ∈ Finset.univ, L (Pi.single j.succ 1) * g j z ≤ 0 := by
    intro j _
    exact mul_nonpos_of_nonneg_of_nonpos (ha j.succ) (hgz j).le
  have hsum : ∑ j, L (Pi.single j.succ 1) * g j z = 0 :=
    le_antisymm (Finset.sum_nonpos hterms) hb
  have htail : ∀ j : Fin l, L (Pi.single j.succ 1) = 0 := by
    intro j
    have he := (Finset.sum_eq_zero_iff_of_nonpos hterms).1 hsum j (Finset.mem_univ j)
    exact (mul_eq_zero.mp he).resolve_right (ne_of_lt (hgz j))
  have hall : ∀ i : Fin (l+1), L (Pi.single i 1) = 0 := by
    intro i
    exact Fin.cases hzero htail i
  obtain ⟨u,hu⟩ := hne
  have hu' := hsep u hu
  rw [slaterFunctional_coordinates] at hu'
  simp [hall] at hu'

theorem convex_slater_partialLagrangian_minimum
    {n l : ℕ} (P : Set (RealVector n))
    (f : RealVector n → ℝ) (g : Fin l → RealVector n → ℝ)
    (p : RealVector n)
    (hP : Convex ℝ P) (hf : ConvexOn ℝ P f)
    (hg : ∀ j, ConvexOn ℝ P (g j))
    (hmin : IsMinimizer {x ∈ P | ∀ j, g j x ≤ 0} f p)
    (hslater : ∃ z ∈ P, ∀ j, g j z < 0) :
    ∃ lambda : Fin l → ℝ,
      (∀ j, 0 ≤ lambda j) ∧
      (∀ j, lambda j * g j p = 0) ∧
      IsMinimizer P (fun x => f x + ∑ j, lambda j * g j x) p := by
  classical
  have hne := slaterUpperImage_nonempty P f g p ⟨p,hmin.1.1⟩
  obtain ⟨L,hL⟩ := geometric_hahn_banach_point_open
    (slaterUpperImage_convex P f g p hP hf hg)
    (slaterUpperImage_isOpen P f g p)
    (slaterUpperImage_zero_not_mem P f g p hmin)
  have hsep : ∀ u ∈ slaterUpperImage P f g p, 0 < L u := by simpa using hL
  have ha := slater_separator_coefficients_nonneg P f g p L hne hsep
  have ha0 := slater_separator_objective_pos P f g p L hne hsep hslater
  let lambda : Fin l → ℝ := fun j => L (Pi.single j.succ 1) / L (Pi.single 0 1)
  have hlambda : ∀ j, 0 ≤ lambda j := fun j => div_nonneg (ha j.succ) ha0.le
  have hsupport : ∀ x ∈ P, f p ≤ f x + ∑ j, lambda j * g j x := by
    intro x hx
    have hb := slater_separator_boundary P f g p L hsep hx
    rw [slaterFunctional_coordinates, Fin.sum_univ_succ] at hb
    simp only [Fin.cons_zero, Fin.cons_succ] at hb
    have hm : L (Pi.single 0 1) * (∑ j, lambda j * g j x) =
        ∑ j, L (Pi.single j.succ 1) * g j x := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j _
      dsimp [lambda]
      field_simp
    nlinarith only [hb, hm, ha0]
  have hterms : ∀ j ∈ Finset.univ, lambda j * g j p ≤ 0 := by
    intro j _
    exact mul_nonpos_of_nonneg_of_nonpos (hlambda j) (hmin.1.2 j)
  have hsum : ∑ j, lambda j * g j p = 0 := by
    have hp := hsupport p hmin.1.1
    have hs := Finset.sum_nonpos hterms
    linarith
  have hcomp : ∀ j, lambda j * g j p = 0 := by
    intro j
    exact (Finset.sum_eq_zero_iff_of_nonpos hterms).1 hsum j (Finset.mem_univ j)
  refine ⟨lambda,hlambda,hcomp,hmin.1.1,?_⟩
  intro x hx
  simpa [hsum] using hsupport x hx

/-- The empty family and zero-dimensional ambient space instantiate the actual
existence theorem, with no nonempty-row typeclass hidden in normalization. -/
theorem slater_zero_dimensions_zero_rows_control :
    ∃ lambda : Fin 0 → ℝ,
      (∀ j, 0 ≤ lambda j) ∧
      IsMinimizer (Set.univ : Set (RealVector 0))
        (fun _ => (0 : ℝ) + ∑ j, lambda j * (0 : ℝ)) 0 := by
  obtain ⟨lambda,hl,_,hm⟩ := convex_slater_partialLagrangian_minimum
    (Set.univ : Set (RealVector 0)) (fun _ => (0 : ℝ))
    (fun _ : Fin 0 => fun _ => (0 : ℝ)) 0 convex_univ
    (convexOn_const 0 convex_univ) (fun _ => convexOn_const 0 convex_univ)
    (by simp [IsMinimizer]) (by exact ⟨0,Set.mem_univ _,fun j => Fin.elim0 j⟩)
  exact ⟨lambda,hl,hm⟩

/-- A singleton convex domain uses the same separation theorem although the
domain's opposing affine inequalities cannot both be strict. -/
theorem slater_singleton_domain_control :
    (¬ ∃ x : RealVector 1, x 0 < 0 ∧ -x 0 < 0) ∧
    ∃ lambda : Fin 1 → ℝ,
      (∀ j, 0 ≤ lambda j) ∧ lambda 0 = 0 ∧
      IsMinimizer ({0} : Set (RealVector 1))
        (fun x => x 0 + ∑ j, lambda j * (-1 : ℝ)) 0 := by
  refine ⟨by rintro ⟨x,hx,hx'⟩; linarith, ?_⟩
  have hf : ConvexOn ℝ ({0} : Set (RealVector 1)) (fun x => x 0) := by
    refine ⟨convex_singleton _, ?_⟩
    intro x hx y hy a b _ _ _
    simp only [Set.mem_singleton_iff] at hx hy
    subst x
    subst y
    simp
  obtain ⟨lambda,hl,hcomp,hm⟩ := convex_slater_partialLagrangian_minimum
    ({0} : Set (RealVector 1)) (fun x => x 0)
    (fun _ : Fin 1 => fun _ => (-1 : ℝ)) 0 (convex_singleton _) hf
    (fun _ => convexOn_const (-1) (convex_singleton _))
    (by simp [IsMinimizer]) (by exact ⟨0,rfl,fun _ => by norm_num⟩)
  exact ⟨lambda,hl,by simpa using hcomp 0,hm⟩

/-- A real nonzero multiplier is obtained by existence, then forced to one by
the resulting unconstrained Lagrangian minimum for min(-x) subject to x≤0. -/
theorem slater_nonzero_multiplier_control :
    ∃ lambda : Fin 1 → ℝ,
      (∀ j, 0 ≤ lambda j) ∧ lambda 0 = 1 ∧
      IsMinimizer (Set.univ : Set (RealVector 1))
        (fun x => -x 0 + ∑ j, lambda j * x 0) 0 := by
  have hf : ConvexOn ℝ (Set.univ : Set (RealVector 1)) (fun x => -x 0) := by
    refine ⟨convex_univ, ?_⟩
    intro x _ y _ a b _ _ _
    change -(a * x 0 + b * y 0) ≤ a * (-x 0) + b * (-y 0)
    linarith
  have hg : ConvexOn ℝ (Set.univ : Set (RealVector 1)) (fun x => x 0) := by
    refine ⟨convex_univ, ?_⟩
    intro x _ y _ a b _ _ _
    exact le_rfl
  have hmin : IsMinimizer {x : RealVector 1 | x ∈ Set.univ ∧ ∀ _ : Fin 1, x 0 ≤ 0}
      (fun x => -x 0) 0 := by
    refine ⟨by simp, ?_⟩
    intro x hx
    have hx0 := hx.2 0
    change -(0 : ℝ) ≤ -x 0
    linarith
  obtain ⟨lambda,hl,_,hm⟩ := convex_slater_partialLagrangian_minimum
    (Set.univ : Set (RealVector 1)) (fun x => -x 0)
    (fun _ : Fin 1 => fun x => x 0) 0 convex_univ hf (fun _ => hg) hmin
    ⟨fun _ => -1,Set.mem_univ _,fun _ => by norm_num⟩
  have hp := hm.2 (fun _ => 1) (Set.mem_univ _)
  have hn := hm.2 (fun _ => -1) (Set.mem_univ _)
  simp only [Fin.sum_univ_one, Pi.zero_apply, neg_zero, mul_zero, add_zero,
    mul_one, mul_neg_one] at hp hn
  exact ⟨lambda,hl,by linarith,hm⟩

#print axioms slaterUpperImage_isOpen
#print axioms slaterUpperImage_convex
#print axioms slaterUpperImage_nonempty
#print axioms slaterUpperImage_zero_not_mem
#print axioms slaterFunctional_coordinates
#print axioms slaterUpperImage_mono
#print axioms slater_separator_coefficients_nonneg
#print axioms slater_separator_boundary
#print axioms slater_separator_objective_pos
#print axioms convex_slater_partialLagrangian_minimum
#print axioms slater_zero_dimensions_zero_rows_control
#print axioms slater_singleton_domain_control
#print axioms slater_nonzero_multiplier_control

end Chapter02
