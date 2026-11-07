module

public import Chapter07UnseededModel
public import Chapter06LevelControlData

@[expose] public section

/-! Exact invented nonlinear controls for source initialization and restoration.
These are rational mathematical examples, not historical numerical experiments. -/
noncomputable section
open scoped BigOperators
open Chapter02 Chapter06.Level
namespace Chapter07.UnseededControl

abbrev P := Point 1 1
def pt (x y : ℝ) : P := Chapter06.LevelControl.pt x y
def iy (y : ℤ) : IntVector 1 := Chapter06.LevelControl.iy y

theorem pt_intCast (x : ℝ) (y : ℤ) : (pt x (y : ℝ)).2 = intCast (iy y) := rfl

def boxData (f g : P → ℝ) : Data 1 1 1 4 where
  f := f
  g := fun _ => g
  A := Chapter06.LevelControl.d.A
  B := Chapter06.LevelControl.d.B
  b := fun i => if i.val=2 then 0 else 1

theorem box_hard_iff (f g : P → ℝ) (p : P) : p ∈ (boxData f g).hard ↔
    -1 ≤ p.1 0 ∧ p.1 0 ≤ 1 ∧ 0 ≤ p.2 0 ∧ p.2 0 ≤ 1 := by
  constructor
  · intro h
    have h0 := h ⟨0, by decide⟩; have h1 := h ⟨1, by decide⟩
    have h2 := h ⟨2, by decide⟩; have h3 := h ⟨3, by decide⟩
    norm_num [boxData, Chapter06.LevelControl.d, LinearForm] at h0 h1 h2 h3
    exact ⟨by linarith, h1, by linarith, h3⟩
  · rintro ⟨hx0,hx1,hy0,hy1⟩ i
    fin_cases i <;> norm_num [boxData, Chapter06.LevelControl.d, LinearForm] <;> linarith

theorem box_hard_eq (f g : P → ℝ) :
    (boxData f g).hard = Set.Icc (pt (-1) 0) (pt 1 1) := by
  ext p
  rw [box_hard_iff]
  simp [Set.mem_Icc, Prod.le_def, Pi.le_def, pt, Chapter06.LevelControl.pt,
    Fin.forall_fin_one, and_assoc, and_left_comm, and_comm]

theorem box_hard_compact (f g : P → ℝ) : IsCompact (boxData f g).hard := by
  rw [box_hard_eq]
  exact isCompact_Icc

theorem fiber_y {l r : ℕ} {d : Data 1 1 l r} {y : IntVector 1} {p : P}
    (hp : p ∈ d.hardFiber y) : p.2 0 = (y 0 : ℝ) := congrFun hp.2 0

theorem int_zero_one (y : IntVector 1) (h0 : (0:ℝ) ≤ y 0) (h1 : (y 0 : ℝ) ≤ 1) :
    y = iy 0 ∨ y = iy 1 := by
  have h0' : 0 ≤ y 0 := by exact_mod_cast h0
  have h1' : y 0 ≤ 1 := by exact_mod_cast h1
  have hc : y 0 = 0 ∨ y 0 = 1 := by omega
  rcases hc with h | h
  · left; funext i; fin_cases i; exact h
  · right; funext i; fin_cases i; exact h

theorem box_integer_cases (f g : P → ℝ) {p : P}
    (hp : p ∈ (boxData f g).mixed) : p.2 0 = 0 ∨ p.2 0 = 1 := by
  obtain ⟨y,hy⟩ := hp.2
  have he : p.2 0 = (y 0 : ℝ) := congrFun hy 0
  have hb := (box_hard_iff f g p).mp hp.1
  rcases int_zero_one y (by linarith) (by linarith) with h | h
  · left; simpa [h, iy, Chapter06.LevelControl.iy] using he
  · right; simpa [h, iy, Chapter06.LevelControl.iy] using he

theorem box_targets (f g : P → ℝ) (hr : Regularity (boxData f g)) :
    targets (boxData f g) hr = {iy 0, iy 1} := by
  classical
  ext y
  rw [mem_targets]
  simp only [Finset.mem_insert, Finset.mem_singleton]
  constructor
  · rintro ⟨p,hp,hy⟩
    have he : p.2 0 = (y 0 : ℝ) := congrFun hy 0
    have hb := (box_hard_iff f g p).mp hp
    exact int_zero_one y (by linarith) (by linarith)
  · rintro (rfl | rfl)
    · exact ⟨pt 0 0, (box_hard_iff _ _ _).mpr (by norm_num [pt,Chapter06.LevelControl.pt]), by simpa using pt_intCast 0 0⟩
    · exact ⟨pt 0 1, (box_hard_iff _ _ _).mpr (by norm_num [pt,Chapter06.LevelControl.pt]), by simpa using pt_intCast 0 1⟩

theorem box_target_count (f g : P → ℝ) (hr : Regularity (boxData f g)) :
    (targets (boxData f g) hr).card = 2 := by
  rw [box_targets]
  have hne : iy 0 ≠ iy 1 := by intro h; have hh := congrFun h 0; norm_num [iy,Chapter06.LevelControl.iy] at hh
  simp [hne]

theorem selected_single_iff {r : ℕ} (d : Data 1 1 1 r) (a q : P) (rho : ℝ)
    (ha : d.g 0 a = rho) :
    selectedRows d a rho q ↔ tangent (d.g 0) a q ≤ 0 := by
  constructor
  · intro h; exact h 0 ha
  · intro h j _
    fin_cases j
    exact h

namespace Feasible

def f (p : P) : ℝ := p.2 0 - p.1 0
def g (p : P) : ℝ := (p.1 0)^2 + 7/16 - p.2 0
def d := boxData f g
def a0 : P := pt (1/2) (11/16)
def restored : P := pt 0 0
def optimum : P := pt (3/4) 1

theorem objective_C2 : ContDiff ℝ 2 d.f := by
  change ContDiff ℝ 2 (fun p : P => p.2 0-p.1 0)
  fun_prop

theorem soft_C2 (j : Fin 1) : ContDiff ℝ 2 (d.g j) := by
  change ContDiff ℝ 2 (fun p : P => (p.1 0)^2+7/16-p.2 0)
  fun_prop

theorem objective_convex : ConvexOn ℝ Set.univ d.f := by
  refine ⟨convex_univ, ?_⟩
  intro p _ q _ a b _ _ _
  change (a*p.2 0+b*q.2 0)-(a*p.1 0+b*q.1 0) ≤
    a*(p.2 0-p.1 0)+b*(q.2 0-q.1 0)
  ring_nf
  exact le_rfl

theorem soft_convex (j : Fin 1) : ConvexOn ℝ Set.univ (d.g j) := by
  refine ⟨convex_univ, ?_⟩
  intro p _ q _ a b ha hb hab
  change (a*p.1 0+b*q.1 0)^2+7/16-(a*p.2 0+b*q.2 0) ≤
    a*((p.1 0)^2+7/16-p.2 0)+b*((q.1 0)^2+7/16-q.2 0)
  have h := mul_nonneg (mul_nonneg ha hb) (sq_nonneg (p.1 0-q.1 0))
  have hb' : b=1-a := by linarith
  subst b
  nlinarith

theorem fiber_zero_infeasible : ¬ (d.feasibleFiber (iy 0)).Nonempty := by
  rintro ⟨p,hp⟩
  have hy := fiber_y hp.1
  have hg := hp.2 0
  norm_num [iy, Chapter06.LevelControl.iy] at hy
  change (p.1 0)^2+7/16-p.2 0 ≤ 0 at hg
  nlinarith [sq_nonneg (p.1 0)]

theorem fiber_slater (y : IntVector 1) (hne : (d.feasibleFiber y).Nonempty) :
    ∃ p ∈ d.hardFiber y, ∀ j, d.g j p < 0 := by
  obtain ⟨p,hp⟩ := hne
  have hy := fiber_y hp.1
  have hb := (box_hard_iff f g p).mp hp.1.1
  rcases int_zero_one y (by linarith) (by linarith) with he | he
  · exact (fiber_zero_infeasible ⟨p, he ▸ hp⟩).elim
  · subst y
    refine ⟨pt 0 1, ⟨(box_hard_iff _ _ _).mpr ?_, by simpa using pt_intCast 0 1⟩, ?_⟩
    · norm_num [pt, Chapter06.LevelControl.pt]
    · intro j; norm_num [d, boxData, g, pt, Chapter06.LevelControl.pt]

def regularity : Regularity d where
  hard_compact := box_hard_compact f g
  hard_nonempty := ⟨restored, (box_hard_iff _ _ _).mpr (by norm_num [restored,pt,Chapter06.LevelControl.pt])⟩
  objective_convex := objective_convex
  objective_C1 := objective_C2.of_le (by norm_num)
  constraint_convex := soft_convex
  constraint_C1 := fun j => (soft_C2 j).of_le (by norm_num)
  fiber_slater := fiber_slater

theorem initializer_minimum : IsMinimizer (Unseeded.relaxation d) d.f a0 := by
  refine ⟨⟨(box_hard_iff _ _ _).mpr ?_, ?_⟩, ?_⟩
  · norm_num [a0,pt,Chapter06.LevelControl.pt]
  · intro j; norm_num [d,boxData,g,a0,pt,Chapter06.LevelControl.pt]
  · intro p hp
    have hg := hp.2 0
    change (p.1 0)^2+7/16-p.2 0 ≤ 0 at hg
    change 11/16-1/2 ≤ p.2 0-p.1 0
    nlinarith [sq_nonneg (p.1 0-1/2)]

theorem restoration_minimum :
    IsMinimizer (d.restoration (iy 0)) Prod.snd (restored,7/16) := by
  refine ⟨⟨⟨(box_hard_iff _ _ _).mpr ?_,by simpa [restored] using pt_intCast 0 0⟩,?_,by norm_num⟩,?_⟩
  · norm_num [restored,pt,Chapter06.LevelControl.pt]
  · intro j; norm_num [d,boxData,g,restored,pt,Chapter06.LevelControl.pt]
  · intro z hz
    have hy := fiber_y hz.1
    have hg := hz.2.1 0
    norm_num [iy,Chapter06.LevelControl.iy] at hy
    change (z.1.1 0)^2+7/16-z.1.2 0 ≤ z.2 at hg
    change (7/16:ℝ) ≤ z.2
    nlinarith [sq_nonneg (z.1.1 0)]

theorem feasible_minimum : IsMinimizer (d.feasibleFiber (iy 1)) d.f optimum := by
  refine ⟨⟨⟨(box_hard_iff _ _ _).mpr ?_,by simpa [optimum] using pt_intCast (3/4) 1⟩,?_⟩,?_⟩
  · norm_num [optimum,pt,Chapter06.LevelControl.pt]
  · intro j; norm_num [d,boxData,g,optimum,pt,Chapter06.LevelControl.pt]
  · intro p hp
    have hy := fiber_y hp.1
    have hg := hp.2 0
    norm_num [iy,Chapter06.LevelControl.iy] at hy
    change (p.1 0)^2+7/16-p.2 0 ≤ 0 at hg
    have hx : p.1 0 ≤ 3/4 := by nlinarith [sq_nonneg (p.1 0-3/4)]
    change 1-3/4 ≤ p.2 0-p.1 0
    linarith

def restoredEvent : Event d := ⟨iy 0,restored,some (7/16),fiber_zero_infeasible,restoration_minimum⟩
def feasibleEvent : Event d := ⟨iy 1,optimum,none,feasible_minimum⟩

theorem fderiv_f_apply (a h : P) : fderiv ℝ d.f a h = h.2 0-h.1 0 := by
  have he : d.f = fun p => Chapter06.LevelControl.Y p-Chapter06.LevelControl.X p := by
    funext p; simp [d,boxData,f]
  have hh := (Chapter06.LevelControl.Y.hasFDerivAt (x := a)).fun_sub
    (Chapter06.LevelControl.X.hasFDerivAt (x := a))
  rw [he,hh.fderiv]
  simp

theorem fderiv_g_apply (j : Fin 1) (a h : P) :
    fderiv ℝ (d.g j) a h = 2*a.1 0*h.1 0-h.2 0 := by
  have he : d.g j = fun p => Chapter06.LevelControl.X p*Chapter06.LevelControl.X p +
      7/16-Chapter06.LevelControl.Y p := by funext p; simp [d,boxData,g,pow_two]
  have hh := (((Chapter06.LevelControl.X.hasFDerivAt (x := a)).fun_mul
    (Chapter06.LevelControl.X.hasFDerivAt (x := a))).add_const (7/16)).fun_sub
    (Chapter06.LevelControl.Y.hasFDerivAt (x := a))
  rw [he,hh.fderiv]
  simp
  ring

theorem objective_tangent (a q : P) : tangent d.f a q = q.2 0-q.1 0 := by
  unfold tangent
  rw [fderiv_f_apply]
  change a.2 0-a.1 0+((q.2 0-a.2 0)-(q.1 0-a.1 0)) = _
  ring

theorem soft_tangent (j : Fin 1) (a q : P) :
    tangent (d.g j) a q = 2*a.1 0*q.1 0-(a.1 0)^2+7/16-q.2 0 := by
  unfold tangent
  rw [fderiv_g_apply]
  change (a.1 0)^2+7/16-a.2 0 +
    (2*a.1 0*(q.1 0-a.1 0)-(q.2 0-a.2 0)) = _
  ring

end Feasible
namespace Infeasible

def f (p : P) : ℝ := (p.1 0)^2
def g (p : P) : ℝ := (p.1 0)^2+(p.2 0-1/2)^2-1/16
def d := boxData f g
def a0 : P := pt 0 (1/2)
def restored0 : P := pt 0 0
def restored1 : P := pt 0 1

theorem objective_C2 : ContDiff ℝ 2 d.f := by
  change ContDiff ℝ 2 (fun p : P => (p.1 0)^2)
  fun_prop

theorem soft_C2 (j : Fin 1) : ContDiff ℝ 2 (d.g j) := by
  change ContDiff ℝ 2 (fun p : P => (p.1 0)^2+(p.2 0-1/2)^2-1/16)
  fun_prop

theorem objective_convex : ConvexOn ℝ Set.univ d.f := by
  refine ⟨convex_univ,?_⟩
  intro p _ q _ a b ha hb hab
  change (a*p.1 0+b*q.1 0)^2 ≤ a*(p.1 0)^2+b*(q.1 0)^2
  have h := mul_nonneg (mul_nonneg ha hb) (sq_nonneg (p.1 0-q.1 0))
  have hb' : b=1-a := by linarith
  subst b
  nlinarith

theorem soft_convex (j : Fin 1) : ConvexOn ℝ Set.univ (d.g j) := by
  refine ⟨convex_univ,?_⟩
  intro p _ q _ a b ha hb hab
  change (a*p.1 0+b*q.1 0)^2+(a*p.2 0+b*q.2 0-1/2)^2-1/16 ≤
    a*((p.1 0)^2+(p.2 0-1/2)^2-1/16)+b*((q.1 0)^2+(q.2 0-1/2)^2-1/16)
  have h := mul_nonneg (mul_nonneg ha hb)
    (add_nonneg (sq_nonneg (p.1 0-q.1 0)) (sq_nonneg (p.2 0-q.2 0)))
  have hb' : b=1-a := by linarith
  subst b
  nlinarith

theorem fiber_zero_infeasible : ¬ (d.feasibleFiber (iy 0)).Nonempty := by
  rintro ⟨p,hp⟩
  have hy := fiber_y hp.1
  have hg := hp.2 0
  norm_num [iy,Chapter06.LevelControl.iy] at hy
  change (p.1 0)^2+(p.2 0-1/2)^2-1/16 ≤ 0 at hg
  nlinarith [sq_nonneg (p.1 0)]

theorem fiber_one_infeasible : ¬ (d.feasibleFiber (iy 1)).Nonempty := by
  rintro ⟨p,hp⟩
  have hy := fiber_y hp.1
  have hg := hp.2 0
  norm_num [iy,Chapter06.LevelControl.iy] at hy
  change (p.1 0)^2+(p.2 0-1/2)^2-1/16 ≤ 0 at hg
  nlinarith [sq_nonneg (p.1 0)]

theorem all_fibers_infeasible (y : IntVector 1) : ¬ (d.feasibleFiber y).Nonempty := by
  rintro ⟨p,hp⟩
  have hy := fiber_y hp.1
  have hb := (box_hard_iff f g p).mp hp.1.1
  rcases int_zero_one y (by linarith) (by linarith) with he | he
  · exact fiber_zero_infeasible ⟨p,he ▸ hp⟩
  · exact fiber_one_infeasible ⟨p,he ▸ hp⟩

def regularity : Regularity d where
  hard_compact := box_hard_compact f g
  hard_nonempty := ⟨restored0,(box_hard_iff _ _ _).mpr (by norm_num [restored0,pt,Chapter06.LevelControl.pt])⟩
  objective_convex := objective_convex
  objective_C1 := objective_C2.of_le (by norm_num)
  constraint_convex := soft_convex
  constraint_C1 := fun j => (soft_C2 j).of_le (by norm_num)
  fiber_slater := fun y hne => (all_fibers_infeasible y hne).elim

theorem initializer_minimum : IsMinimizer (Unseeded.relaxation d) d.f a0 := by
  refine ⟨⟨(box_hard_iff _ _ _).mpr ?_,?_⟩,?_⟩
  · norm_num [a0,pt,Chapter06.LevelControl.pt]
  · intro j; norm_num [d,boxData,g,a0,pt,Chapter06.LevelControl.pt]
  · intro p _
    change (0:ℝ)^2 ≤ (p.1 0)^2
    nlinarith [sq_nonneg (p.1 0)]

theorem restoration_zero_minimum :
    IsMinimizer (d.restoration (iy 0)) Prod.snd (restored0,3/16) := by
  refine ⟨⟨⟨(box_hard_iff _ _ _).mpr ?_,by simpa [restored0] using pt_intCast 0 0⟩,?_,by norm_num⟩,?_⟩
  · norm_num [restored0,pt,Chapter06.LevelControl.pt]
  · intro j; norm_num [d,boxData,g,restored0,pt,Chapter06.LevelControl.pt]
  · intro z hz
    have hy := fiber_y hz.1
    have hg := hz.2.1 0
    norm_num [iy,Chapter06.LevelControl.iy] at hy
    change (z.1.1 0)^2+(z.1.2 0-1/2)^2-1/16 ≤ z.2 at hg
    change (3/16:ℝ) ≤ z.2
    nlinarith [sq_nonneg (z.1.1 0)]

theorem restoration_one_minimum :
    IsMinimizer (d.restoration (iy 1)) Prod.snd (restored1,3/16) := by
  refine ⟨⟨⟨(box_hard_iff _ _ _).mpr ?_,by simpa [restored1] using pt_intCast 0 1⟩,?_,by norm_num⟩,?_⟩
  · norm_num [restored1,pt,Chapter06.LevelControl.pt]
  · intro j; norm_num [d,boxData,g,restored1,pt,Chapter06.LevelControl.pt]
  · intro z hz
    have hy := fiber_y hz.1
    have hg := hz.2.1 0
    norm_num [iy,Chapter06.LevelControl.iy] at hy
    change (z.1.1 0)^2+(z.1.2 0-1/2)^2-1/16 ≤ z.2 at hg
    change (3/16:ℝ) ≤ z.2
    nlinarith [sq_nonneg (z.1.1 0)]

def event0 : Event d := ⟨iy 0,restored0,some (3/16),fiber_zero_infeasible,restoration_zero_minimum⟩
def event1 : Event d := ⟨iy 1,restored1,some (3/16),fiber_one_infeasible,restoration_one_minimum⟩

theorem fderiv_f_apply (a h : P) : fderiv ℝ d.f a h = 2*a.1 0*h.1 0 := by
  have he : d.f = fun p => Chapter06.LevelControl.X p*Chapter06.LevelControl.X p := by
    funext p; simp [d,boxData,f,pow_two]
  have hh := (Chapter06.LevelControl.X.hasFDerivAt (x := a)).fun_mul
    (Chapter06.LevelControl.X.hasFDerivAt (x := a))
  rw [he,hh.fderiv]
  simp
  ring

theorem fderiv_g_apply (j : Fin 1) (a h : P) :
    fderiv ℝ (d.g j) a h = 2*a.1 0*h.1 0+2*(a.2 0-1/2)*h.2 0 := by
  have he : d.g j = fun p => Chapter06.LevelControl.X p*Chapter06.LevelControl.X p +
      (Chapter06.LevelControl.Y p-1/2)*(Chapter06.LevelControl.Y p-1/2)-1/16 := by
    funext p; simp [d,boxData,g,pow_two]
  have hx := (Chapter06.LevelControl.X.hasFDerivAt (x := a)).fun_mul
    (Chapter06.LevelControl.X.hasFDerivAt (x := a))
  have hy := (Chapter06.LevelControl.Y.hasFDerivAt (x := a)).sub_const (1/2)
  have hh := (hx.fun_add (hy.fun_mul hy)).sub_const (1/16)
  rw [he,hh.fderiv]
  simp
  ring

theorem objective_tangent (a q : P) :
    tangent d.f a q = 2*a.1 0*q.1 0-(a.1 0)^2 := by
  unfold tangent
  rw [fderiv_f_apply]
  change (a.1 0)^2+2*a.1 0*(q.1 0-a.1 0) = _
  ring

theorem soft_tangent (j : Fin 1) (a q : P) : tangent (d.g j) a q =
    2*a.1 0*q.1 0-(a.1 0)^2+(2*a.2 0-1)*q.2 0-(a.2 0)^2+3/16 := by
  unfold tangent
  rw [fderiv_g_apply]
  change (a.1 0)^2+(a.2 0-1/2)^2-1/16 +
    (2*a.1 0*(q.1 0-a.1 0)+2*(a.2 0-1/2)*(q.2 0-a.2 0)) = _
  ring

end Infeasible
end Chapter07.UnseededControl

#print axioms Chapter07.UnseededControl.box_hard_compact
#print axioms Chapter07.UnseededControl.box_target_count
#print axioms Chapter07.UnseededControl.Feasible.regularity
#print axioms Chapter07.UnseededControl.Feasible.initializer_minimum
#print axioms Chapter07.UnseededControl.Feasible.fiber_zero_infeasible
#print axioms Chapter07.UnseededControl.Feasible.restoration_minimum
#print axioms Chapter07.UnseededControl.Feasible.feasible_minimum
#print axioms Chapter07.UnseededControl.Feasible.restoredEvent
#print axioms Chapter07.UnseededControl.Feasible.feasibleEvent
#print axioms Chapter07.UnseededControl.Feasible.objective_tangent
#print axioms Chapter07.UnseededControl.Feasible.soft_tangent
#print axioms Chapter07.UnseededControl.Infeasible.regularity
#print axioms Chapter07.UnseededControl.Infeasible.initializer_minimum
#print axioms Chapter07.UnseededControl.Infeasible.all_fibers_infeasible
#print axioms Chapter07.UnseededControl.Infeasible.restoration_zero_minimum
#print axioms Chapter07.UnseededControl.Infeasible.restoration_one_minimum
#print axioms Chapter07.UnseededControl.Infeasible.event0
#print axioms Chapter07.UnseededControl.Infeasible.event1
#print axioms Chapter07.UnseededControl.Infeasible.objective_tangent
#print axioms Chapter07.UnseededControl.Infeasible.soft_tangent
