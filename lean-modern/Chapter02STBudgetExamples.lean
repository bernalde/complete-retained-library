module

public import Chapter02STSourceDriver
public import Chapter02STBudget
public import Mathlib.Tactic
public import Mathlib.Analysis.Calculus.Deriv.Pow

@[expose] public section

/-! P3 and finite-allowance controls for the separately named source repair.
The recurrence facts are preparation for actual raw process traces; they do
not by themselves certify an algorithm or its source initialization. -/
noncomputable section
open Chapter02
open scoped BigOperators
namespace Chapter02STBudgetExamples

def p3Point (y : ℝ) : RealVector 1 := fun _ => y
def p3I : Finset (Fin 1) := Finset.univ

def p3Data : BBPolyData 1 1 2 where
  coefficient := ![![-1],![1]]
  rhs := ![0,2]
  c := fun z _ => (z 0)^2-2
  f := fun z => -z 0

def p3Coord : RealVector 1 →L[ℝ] ℝ := ContinuousLinearMap.proj 0

theorem p3_polyhedron_iff (z : RealVector 1) :
    z ∈ p3Data.polyhedron ↔ 0 ≤ z 0 ∧ z 0 ≤ 2 := by
  simp [BBPolyData.polyhedron,p3Data,Fin.forall_fin_succ]

theorem p3_polyhedron_bounded : Bornology.IsBounded p3Data.polyhedron := by
  apply (isCompact_Icc : IsCompact (Set.Icc (0 : RealVector 1) 2)).isBounded.subset
  intro z hz
  have hh := (p3_polyhedron_iff z).mp hz
  exact ⟨fun i => by fin_cases i; exact hh.1, fun i => by fin_cases i; exact hh.2⟩

theorem p3_encloses_two : p3Data.Encloses 2 := by
  refine ⟨by norm_num,?_⟩
  intro z hz i
  fin_cases i
  have hh := (p3_polyhedron_iff z).mp hz
  apply abs_le.mpr
  change -2 ≤ z 0 ∧ z 0 ≤ 2
  exact ⟨by linarith,hh.2⟩

theorem p3_objective_convex : ConvexOn ℝ Set.univ p3Data.f := by
  refine ⟨convex_univ,?_⟩
  intro x _ y _ a b _ _ _
  simp [p3Data]

theorem p3_rows_convex : ∀ j, ConvexOn ℝ Set.univ (fun z => p3Data.c z j) := by
  intro j
  refine ⟨convex_univ,?_⟩
  intro x _ y _ a b ha hb hab
  have ht := mul_nonneg (mul_nonneg ha hb) (sq_nonneg (x 0-y 0))
  change (a*x 0+b*y 0)^2-2 ≤ a*((x 0)^2-2)+b*((y 0)^2-2)
  nlinarith [sq_nonneg (x 0-y 0)]

theorem p3_objective_smooth : ContDiff ℝ 2 p3Data.f := by
  exact (contDiff_apply ℝ (fun _ => ℝ) (0 : Fin 1)).neg

theorem p3_rows_smooth : ContDiff ℝ 2 p3Data.c := by
  apply contDiff_pi.mpr
  intro j
  exact ((contDiff_apply ℝ (fun _ => ℝ) (0 : Fin 1)).pow 2).sub contDiff_const

theorem p3_objective_tangent (a z : RealVector 1) :
    stTangent p3Data.f a z = -z 0 := by
  have hd : HasFDerivAt p3Data.f (-p3Coord) a := p3Coord.hasFDerivAt.neg
  rw [stTangent,hd.fderiv]
  change -a 0 + -(z 0-a 0) = -z 0
  ring

theorem p3_constraint_tangent (a z : RealVector 1) :
    stTangent (fun x => p3Data.c x 0) a z = 2*(a 0)*(z 0)-(a 0)^2-2 := by
  have hd := ((hasDerivAt_pow 2 (a 0)).comp_hasFDerivAt a p3Coord.hasFDerivAt).sub_const 2
  change HasFDerivAt (fun x : RealVector 1 => (x 0)^2-2)
    (((2 : ℝ) * (a 0)^1) • p3Coord) a at hd
  change stTangent (fun x : RealVector 1 => (x 0)^2-2) a z = _
  simp [stTangent,hd.fderiv,p3Coord]
  ring

theorem p3_fiber_singleton (a : RealVector 1) (ha : a ∈ p3Data.polyhedron) :
    stSourceFiber p3Data p3I a = {a} := by
  ext z
  constructor
  · intro hz
    apply Set.mem_singleton_iff.mpr
    funext i
    exact hz.2 ⟨i,Finset.mem_univ i⟩
  · rintro rfl
    exact ⟨ha,fun _ => rfl⟩

def p3Batch (y : ℝ) (restoration : Bool) : STSourceBatch 1 :=
  ⟨p3Point y,restoration⟩

theorem p3_point_integral (k : ℤ) : STSourceIntegral p3I (p3Point k) :=
  fun _ => ⟨k,rfl⟩

theorem p3_initial_batch_valid : stSourceBatchValid p3Data p3I (fun _ => 1)
    (p3Batch 0 false) := by
  refine ⟨by simpa [p3Batch] using p3_point_integral 0,?_⟩
  change IsMinimizer (stSourceNonlinearFiber p3Data p3I (p3Point 0))
    p3Data.f (p3Point 0)
  have hx : p3Point 0 ∈ p3Data.polyhedron := (p3_polyhedron_iff _).mpr (by norm_num [p3Point])
  have he := p3_fiber_singleton (p3Point 0) hx
  refine ⟨⟨by rw [he]; exact Set.mem_singleton _,fun _ => by norm_num [p3Data,p3Point]⟩,?_⟩
  intro z hz
  have hz' : z = p3Point 0 := by simpa only [he,Set.mem_singleton_iff] using hz.1
  rw [hz']

theorem p3_infeasible_batch_valid : stSourceBatchValid p3Data p3I (fun _ => 1)
    (p3Batch 2 true) := by
  refine ⟨by simpa [p3Batch] using p3_point_integral 2,?_⟩
  change stSourceNonlinearFiber p3Data p3I (p3Point 2) = ∅ ∧
    IsMinimizer (stSourceFiber p3Data p3I (p3Point 2))
      (weightedPositive (fun _ => 1) (fun j z => p3Data.c z j)) (p3Point 2)
  have hx : p3Point 2 ∈ p3Data.polyhedron := (p3_polyhedron_iff _).mpr (by norm_num [p3Point])
  have he := p3_fiber_singleton (p3Point 2) hx
  constructor
  · apply Set.eq_empty_iff_forall_notMem.mpr
    intro z hz
    have hz' : z = p3Point 2 := by simpa only [he,Set.mem_singleton_iff] using hz.1
    have hg := hz.2 0
    rw [hz'] at hg
    norm_num [p3Data,p3Point] at hg
  · rw [he]
    exact ⟨Set.mem_singleton _,fun z hz => by rw [Set.mem_singleton_iff.mp hz]⟩

theorem p3_original_optimum : IsMinimizer (p3Data.feasible p3I) p3Data.f (p3Point 1) := by
  refine ⟨⟨(p3_polyhedron_iff _).mpr (by norm_num [p3Point]),
    fun _ => by norm_num [p3Data,p3Point],fun _ => ⟨1,by simp [p3Point]⟩⟩,?_⟩
  intro z hz
  obtain ⟨k,hk⟩ := hz.2.2 ⟨0,Finset.mem_univ 0⟩
  have hx := (p3_polyhedron_iff z).mp hz.1
  have hg := hz.2.1 0
  change (z 0)^2-2 ≤ 0 at hg
  have hlt : z 0 < 2 := by nlinarith
  have hklt : k < 2 := by exact_mod_cast (hk ▸ hlt)
  have hkle : k ≤ 1 := by omega
  have hzle : z 0 ≤ 1 := by rw [← hk]; exact_mod_cast hkle
  change -(1 : ℝ) ≤ -z 0
  linarith

theorem p3_feasible_rows_strict (z : RealVector 1) (hz : z ∈ p3Data.feasible p3I) :
    ∀ j, p3Data.c z j < 0 := by
  have hlo := ((p3_polyhedron_iff z).mp hz.1).1
  have hval := p3_original_optimum.2 z hz
  change -(1 : ℝ) ≤ -z 0 at hval
  intro j
  change (z 0)^2-2 < 0
  nlinarith [sq_nonneg (z 0)]

theorem p3_fiber_slater : STSourceFiberSlater p3Data p3I := by
  intro a hi hne
  obtain ⟨z,hz⟩ := hne
  have hf : z ∈ p3Data.feasible p3I := by
    refine ⟨hz.1.1,hz.2,?_⟩
    intro i
    obtain ⟨k,hk⟩ := hi i
    exact ⟨k,hk.trans (hz.1.2 i).symm⟩
  exact ⟨z,hz.1,p3_feasible_rows_strict z hf⟩

def p3Next (q : ℝ) : ℝ := (q^2+2)/(2*q)

theorem p3_next_properties {q : ℝ} (hlo : 1 < q) (hhi : q ≤ 3/2) (hres : 2 < q^2) :
    1 < p3Next q ∧ p3Next q < q ∧ p3Next q ≤ 3/2 ∧ 2 < (p3Next q)^2 := by
  have hq : 0 < q := by linarith
  have hd : 0 < 2*q := by positivity
  have h1 : 1 < p3Next q := by
    rw [p3Next,lt_div_iff₀ hd]
    nlinarith [sq_nonneg (q-1)]
  have h2 : p3Next q < q := by
    rw [p3Next,div_lt_iff₀ hd]
    nlinarith
  have hid : (p3Next q)^2-2 = (q^2-2)^2/(4*q^2) := by
    unfold p3Next
    field_simp
    ring
  have hp : 0 < (q^2-2)^2/(4*q^2) :=
    div_pos (sq_pos_of_pos (by linarith)) (by positivity)
  exact ⟨h1,h2,h2.le.trans hhi,by linarith⟩

def p3Trial : ℕ → ℝ
  | 0 => 3/2
  | k+1 => p3Next (p3Trial k)

theorem p3_trial_properties (k : ℕ) :
    1 < p3Trial k ∧ p3Trial k ≤ 3/2 ∧ 2 < (p3Trial k)^2 := by
  induction k with
  | zero => norm_num [p3Trial]
  | succ k ih =>
    have hh := p3_next_properties ih.1 ih.2.1 ih.2.2
    exact ⟨hh.1,hh.2.2.1,hh.2.2.2⟩

theorem p3_trial_strict_decrease (k : ℕ) : p3Trial (k+1) < p3Trial k :=
  (p3_next_properties (p3_trial_properties k).1 (p3_trial_properties k).2.1
    (p3_trial_properties k).2.2).2.1

theorem p3_trial_antitone : Antitone p3Trial :=
  antitone_nat_of_succ_le (fun k => (p3_trial_strict_decrease k).le)

theorem p3_trial_fractional (k : ℕ) : BBFractional (p3Trial k) := by
  intro h
  obtain ⟨j,hj⟩ := h
  have hp := p3_trial_properties k
  have hl : (1 : ℤ) < j := by exact_mod_cast (hj ▸ hp.1)
  have hlt : p3Trial k < 2 := by linarith [hp.2.1]
  have hu : j < 2 := by exact_mod_cast (hj ▸ hlt)
  omega

def p3Seeds (k : ℕ) : List (RealVector 1) :=
  (List.range k).map (fun j => p3Point (p3Trial j))

def p3Anchors (k : ℕ) : List (RealVector 1) := p3Seeds k ++ [p3Point 0,p3Point 2]
def p3Policy : STSourcePolicy := .gap (1/4)
def p3Root : BBExtendedNode {i : Fin 1 // i ∈ p3I} := .root
def p3LPPoint (k : ℕ) : RealVector 1 × ℝ := (p3Point (p3Trial k),-p3Trial k)

theorem p3_rows_iff (a : ℝ) (z : RealVector 1) :
    stSourceRows p3Data (p3Point a) z ↔ 2*a*(z 0)-a^2-2 ≤ 0 := by
  constructor
  · intro h
    have hh := h 0
    change stTangent (fun x => p3Data.c x 0) (p3Point a) z ≤ 0 at hh
    simpa only [p3_constraint_tangent,p3Point] using hh
  · intro h j
    fin_cases j
    change stTangent (fun x => p3Data.c x 0) (p3Point a) z ≤ 0
    simpa only [p3_constraint_tangent,p3Point] using h

theorem p3_rows_next_iff {a : ℝ} (ha : 0 < a) (z : RealVector 1) :
    stSourceRows p3Data (p3Point a) z ↔ z 0 ≤ p3Next a := by
  rw [p3_rows_iff,p3Next,le_div_iff₀ (by positivity : 0 < 2*a)]
  constructor <;> intro h <;> nlinarith

theorem p3_seeds_succ (k : ℕ) :
    p3Seeds (k+1) = p3Seeds k ++ [p3Point (p3Trial k)] := by
  simp [p3Seeds,List.range_succ]

theorem p3_trial_all_rows (k : ℕ) :
    ∀ a ∈ p3Anchors k, stSourceRows p3Data a (p3Point (p3Trial k)) := by
  intro a ha
  rcases List.mem_append.mp ha with ha | ha
  · obtain ⟨j,hj,rfl⟩ := List.mem_map.mp ha
    have hjk : j+1 ≤ k := Nat.succ_le_of_lt (List.mem_range.mp hj)
    apply (p3_rows_next_iff (by linarith [(p3_trial_properties j).1]) _).mpr
    exact p3_trial_antitone hjk
  · simp only [List.mem_cons,List.not_mem_nil,or_false] at ha
    rcases ha with rfl | rfl
    · rw [p3_rows_iff]; norm_num
    · rw [p3_rows_iff]
      have h := (p3_trial_properties k).2.1
      change 2*2*p3Trial k-2^2-2 ≤ 0
      nlinarith

theorem p3_all_rows_upper (k : ℕ) (z : RealVector 1)
    (h : ∀ a ∈ p3Anchors k, stSourceRows p3Data a z) : z 0 ≤ p3Trial k := by
  cases k with
  | zero =>
    have hh := (p3_rows_iff 2 z).mp (h (p3Point 2) (by simp [p3Anchors]))
    change z 0 ≤ 3/2
    nlinarith
  | succ k =>
    have hmem : p3Point (p3Trial k) ∈ p3Anchors (k+1) := by
      simp [p3Anchors,p3_seeds_succ]
    exact (p3_rows_next_iff (by linarith [(p3_trial_properties k).1]) z).mp
      (h _ hmem)

theorem p3_every_fractional_lp_minimum (k : ℕ) :
    IsMinimizer (stSourceLP p3Data p3Root (p3Anchors k) p3Policy (some 0))
      Prod.snd (p3LPPoint k) := by
  have hp := p3_trial_properties k
  constructor
  · apply (st_source_lp_mem_iff _ _ _ _ _ _).mpr
    refine ⟨(p3_polyhedron_iff _).mpr ?_,BBExtendedNode.holds_root _,
      p3_trial_all_rows k,?_,?_⟩
    · change 0 ≤ p3Trial k ∧ p3Trial k ≤ 2
      constructor <;> linarith
    · intro a _
      rw [p3_objective_tangent]
      exact le_rfl
    · change -p3Trial k ≤ 0-1/4
      linarith
  · intro z hz
    have hm := (st_source_lp_mem_iff _ _ _ _ _ _).mp hz
    have hy := p3_all_rows_upper k z.1 hm.2.2.1
    have ho := hm.2.2.2.1 (p3Point 0) (by simp [p3Anchors])
    rw [p3_objective_tangent] at ho
    change -p3Trial k ≤ z.2
    linarith

theorem p3_zero_not_optimal : ¬ IsMinimizer (p3Data.feasible p3I) p3Data.f (p3Point 0) := by
  intro h
  have hh := h.2 (p3Point 1) p3_original_optimum.1
  norm_num [p3Data,p3Point] at hh

theorem p3_one_still_admitted : p3Policy.Admits (some 0) (p3Data.f (p3Point 1)) := by
  norm_num [p3Policy,STSourcePolicy.Admits,p3Data,p3Point]

def p3Repeated (k : ℕ) : STSourceState p3I :=
  ⟨p3Seeds k,[p3Batch 0 false,p3Batch 2 true],some (p3Point 0),[p3Root],none⟩

/-- Two explicit readings of the optional fractional-cut arm. Core cycles are
literal repaired-source cycles; an extra cut cycle uses an actual current LP
minimum and either reinserts or drops the selected occurrence. There is no
round allowance. This relation is used only for the retained source control. -/
inductive OptionalCutProcess (keep : Bool) (D : BBPolyData N l r)
    (I : Finset (Fin N)) (w : Fin l → ℝ) (policy : STSourcePolicy) :
    STSourceState I → STSourceState I → Prop
  | core {s t} (h : STSourceProcess D I w policy s t) : OptionalCutProcess keep D I w policy s t
  | cut {seeds : List (RealVector N)} {H : List (STSourceBatch N)}
      {inc : Option (RealVector N)} {pre post : List (BBExtendedNode {i : Fin N // i ∈ I})}
      {B : BBExtendedNode {i : Fin N // i ∈ I}} {q : RealVector N × ℝ}
      (i : {i : Fin N // i ∈ I})
      (hq : IsMinimizer (stSourceLP D B (seeds ++ H.map STSourceBatch.anchor)
        policy (inc.map D.f)) Prod.snd q) (hf : BBFractional (q.1 i)) :
      OptionalCutProcess keep D I w policy
        ⟨seeds,H,inc,pre ++ B :: post,none⟩
        ⟨seeds ++ [q.1],H,inc,(if keep then [B] else []) ++ (pre ++ post),none⟩

theorem p3_unrestricted_cut_step (k : ℕ) :
    OptionalCutProcess true p3Data p3I (fun _ => 1) p3Policy
      (p3Repeated k) (p3Repeated (k+1)) := by
  have hh := OptionalCutProcess.cut (keep:=true) (D:=p3Data) (I:=p3I)
    (w:=fun _ => 1) (policy:=p3Policy) (seeds:=p3Seeds k)
    (H:=[p3Batch 0 false,p3Batch 2 true]) (inc:=some (p3Point 0))
    (pre:=[]) (post:=[]) (B:=p3Root) (q:=p3LPPoint k) ⟨0,Finset.mem_univ 0⟩
    (by simpa [p3Batch,p3Data,p3Point,p3Anchors] using p3_every_fractional_lp_minimum k)
    (p3_trial_fractional k)
  simpa [p3Repeated,p3_seeds_succ,p3LPPoint] using hh

theorem p3_unrestricted_infinite_from_repeated :
    ∃ s : ℕ → STSourceState p3I, s 0 = p3Repeated 0 ∧
      ∀ k, OptionalCutProcess true p3Data p3I (fun _ => 1) p3Policy (s k) (s (k+1)) :=
  ⟨p3Repeated,rfl,p3_unrestricted_cut_step⟩

def p3Dropped : STSourceState p3I :=
  ⟨[p3Point (p3Trial 0)],[p3Batch 0 false,p3Batch 2 true],some (p3Point 0),[],none⟩

theorem p3_dropped_cut_step :
    OptionalCutProcess false p3Data p3I (fun _ => 1) p3Policy (p3Repeated 0) p3Dropped := by
  have hh := OptionalCutProcess.cut (keep:=false) (D:=p3Data) (I:=p3I)
    (w:=fun _ => 1) (policy:=p3Policy) (seeds:=[])
    (H:=[p3Batch 0 false,p3Batch 2 true]) (inc:=some (p3Point 0))
    (pre:=[]) (post:=[]) (B:=p3Root) (q:=p3LPPoint 0) ⟨0,Finset.mem_univ 0⟩
    (by simpa [p3Batch,p3Data,p3Point,p3Anchors,p3Seeds] using p3_every_fractional_lp_minimum 0)
    (p3_trial_fractional 0)
  simpa [p3Repeated,p3Dropped,p3LPPoint,p3Seeds] using hh

theorem p3_dropped_breaks_coverage :
    ¬ STSourceInvariant p3Data p3I (fun _ => 1) p3Policy p3Dropped := by
  intro h
  have hm := h.coverage (p3Point 1) p3_original_optimum.1
    (by simpa [stSourceInc,p3Dropped,p3Data,p3Point] using p3_one_still_admitted)
  simp [stSourceFrontier,p3Dropped] at hm

theorem p3_first_lp_minimum :
    IsMinimizer (stSourceLP p3Data p3Root [p3Point 0] p3Policy (some 0))
      Prod.snd (p3Point 2,-2) := by
  constructor
  · apply (st_source_lp_mem_iff _ _ _ _ _ _).mpr
    refine ⟨(p3_polyhedron_iff _).mpr (by norm_num [p3Point]),
      BBExtendedNode.holds_root _,?_,?_,?_⟩
    · intro a ha
      have he := List.mem_singleton.mp ha
      rw [he,p3_rows_iff]
      norm_num
    · intro a _
      rw [p3_objective_tangent]
      exact le_rfl
    · norm_num [p3Policy,STSourcePolicy.Admits]
  · intro z hz
    have hm := (st_source_lp_mem_iff _ _ _ _ _ _).mp hz
    have hy := ((p3_polyhedron_iff z.1).mp hm.1).2
    have ho := hm.2.2.2.1 (p3Point 0) (List.mem_singleton_self _)
    rw [p3_objective_tangent] at ho
    change -2 ≤ z.2
    linarith

theorem p3_source_initialized : STSourceInitialize p3Data p3I (fun _ => 1)
    (some (stSourceInitial p3Data p3I (p3Batch 0 false))) := by
  exact STSourceInitialize.seeded (p3Point 0) (p3Batch 0 false)
    ((p3_polyhedron_iff _).mpr (by norm_num [p3Point]))
    (by simpa using p3_point_integral 0) p3_initial_batch_valid (fun _ => rfl)

theorem p3_first_actual_callback : STSourceProcess p3Data p3I (fun _ => 1) p3Policy
    (stSourceInitial p3Data p3I (p3Batch 0 false)) (p3Repeated 0) := by
  let working : STSourceState p3I :=
    ⟨[],[p3Batch 0 false],some (p3Point 0),[],some p3Root⟩
  refine ⟨working,?_,?_⟩
  · simpa [stSourceInitial,stSourceBatchInc,stSourceBest,p3Batch,p3Root,working] using
      (STSourceSelect.choose [] [p3Batch 0 false] (some (p3Point 0)) [] [] p3Root)
  · have hh := STSourceResolve.callback (D:=p3Data) (I:=p3I) (w:=fun _ => 1)
      (policy:=p3Policy) (seeds:=[]) (H:=[p3Batch 0 false]) (inc:=some (p3Point 0))
      (live:=[]) (B:=p3Root) (q:=(p3Point 2,-2)) (b:=p3Batch 2 true)
      (by simpa [p3Batch,p3Data,p3Point] using p3_first_lp_minimum)
      (by simpa using p3_point_integral 2) p3_infeasible_batch_valid (fun _ => rfl)
    simpa [working,p3Repeated,p3Seeds,stSourceBatchInc,p3Batch] using hh

def p3UnrestrictedRun : ℕ → STSourceState p3I
  | 0 => stSourceInitial p3Data p3I (p3Batch 0 false)
  | k+1 => p3Repeated k

theorem p3_source_initialized_infinite_execution :
    STSourceInitialize p3Data p3I (fun _ => 1) (some (p3UnrestrictedRun 0)) ∧
      ∀ k, OptionalCutProcess true p3Data p3I (fun _ => 1) p3Policy
        (p3UnrestrictedRun k) (p3UnrestrictedRun (k+1)) := by
  refine ⟨p3_source_initialized,?_⟩
  intro k
  cases k with
  | zero => exact .core p3_first_actual_callback
  | succ k => exact p3_unrestricted_cut_step k

theorem p3_source_initialized_dropped_failure :
    STSourceInitialize p3Data p3I (fun _ => 1)
      (some (stSourceInitial p3Data p3I (p3Batch 0 false))) ∧
    OptionalCutProcess false p3Data p3I (fun _ => 1) p3Policy
      (stSourceInitial p3Data p3I (p3Batch 0 false)) (p3Repeated 0) ∧
    OptionalCutProcess false p3Data p3I (fun _ => 1) p3Policy (p3Repeated 0) p3Dropped ∧
    p3Dropped.live = [] ∧ p3Dropped.working = none ∧
    p3Dropped.incumbent = some (p3Point 0) ∧
    ¬ IsMinimizer (p3Data.feasible p3I) p3Data.f (p3Point 0) :=
  ⟨p3_source_initialized,.core p3_first_actual_callback,p3_dropped_cut_step,
    rfl,rfl,rfl,p3_zero_not_optimal⟩

def p3Index : {i : Fin 1 // i ∈ p3I} := ⟨0,Finset.mem_univ 0⟩
def p3Left : BBExtendedNode {i : Fin 1 // i ∈ p3I} := p3Root.left p3Index (3/2)
def p3Right : BBExtendedNode {i : Fin 1 // i ∈ p3I} := p3Root.right p3Index (3/2)

theorem p3_trial_floor (k : ℕ) : Int.floor (p3Trial k) = 1 := by
  apply Int.floor_eq_iff.mpr
  have hh := p3_trial_properties k
  constructor <;> norm_num <;> linarith [hh.1,hh.2.1]

theorem p3_trial_ceil (k : ℕ) : Int.ceil (p3Trial k) = 2 := by
  apply Int.ceil_eq_iff.mpr
  have hh := p3_trial_properties k
  constructor <;> norm_num <;> linarith [hh.1,hh.2.1]

theorem p3_floor_three_halves : Int.floor ((3 : ℝ)/2) = 1 := p3_trial_floor 0
theorem p3_ceil_three_halves : Int.ceil ((3 : ℝ)/2) = 2 := p3_trial_ceil 0

theorem p3_trial_left (k : ℕ) : p3Root.left p3Index (p3Trial k) = p3Left := by
  simp [p3Left,BBExtendedNode.left,p3_trial_floor,p3_floor_three_halves]

theorem p3_trial_right (k : ℕ) : p3Root.right p3Index (p3Trial k) = p3Right := by
  simp [p3Right,BBExtendedNode.right,p3_trial_ceil,p3_ceil_three_halves]

theorem p3_left_holds_iff (z : RealVector 1) :
    p3Left.Holds (fun i => z i) ↔ z 0 ≤ 1 := by
  constructor
  · intro h
    have hh := (h p3Index).2
    simpa [p3Left,p3Root,p3Index,BBExtendedNode.left,p3_floor_three_halves] using hh
  · intro h i
    have hi : i = p3Index := Subtype.ext (Subsingleton.elim _ _)
    subst i
    simp [p3Left,p3Root,p3Index,BBExtendedNode.root,BBExtendedNode.left,p3_floor_three_halves,h]

theorem p3_right_holds_iff (z : RealVector 1) :
    p3Right.Holds (fun i => z i) ↔ 2 ≤ z 0 := by
  constructor
  · intro h
    have hh := (h p3Index).1
    simp only [p3Right,BBExtendedNode.right,Function.update_self,p3_ceil_three_halves] at hh
    exact WithBot.coe_le_coe.mp hh
  · intro h i
    have hi : i = p3Index := Subtype.ext (Subsingleton.elim _ _)
    subst i
    refine ⟨?_,le_top⟩
    simp only [p3Right,BBExtendedNode.right,Function.update_self,p3_ceil_three_halves]
    exact WithBot.coe_le_coe.mpr h

theorem p3_left_lp_minimum (k : ℕ) :
    IsMinimizer (stSourceLP p3Data p3Left (p3Anchors k) p3Policy (some 0))
      Prod.snd (p3Point 1,-1) := by
  constructor
  · exact st_source_feasible_lp p3Data p3Left (p3Anchors k) p3Policy (some 0)
      p3_objective_convex (p3_objective_smooth.differentiable (by norm_num)) p3_rows_convex
      (fun j => (contDiff_pi.mp p3_rows_smooth j).differentiable (by norm_num))
      p3_original_optimum.1 ((p3_left_holds_iff _).mpr (by norm_num [p3Point]))
      p3_one_still_admitted
  · intro z hz
    have hh := (st_source_lp_mem_iff _ _ _ _ _ _).mp hz
    have hy := (p3_left_holds_iff z.1).mp hh.2.1
    have ho := hh.2.2.2.1 (p3Point 0) (by simp [p3Anchors])
    rw [p3_objective_tangent] at ho
    change -1 ≤ z.2
    linarith

theorem p3_right_lp_empty (k : ℕ) (inc : Option ℝ) :
    stSourceLP p3Data p3Right (p3Anchors k) p3Policy inc = ∅ := by
  apply Set.eq_empty_iff_forall_notMem.mpr
  intro z hz
  have hh := (st_source_lp_mem_iff _ _ _ _ _ _).mp hz
  have hy := (p3_right_holds_iff z.1).mp hh.2.1
  have hu := p3_all_rows_upper k z.1 hh.2.2.1
  linarith [(p3_trial_properties k).2.1]

theorem p3_improving_batch_valid : stSourceBatchValid p3Data p3I (fun _ => 1)
    (p3Batch 1 false) := by
  refine ⟨?_,?_⟩
  · intro i; exact ⟨1,by simp [p3Batch,p3Point]⟩
  · change IsMinimizer (stSourceNonlinearFiber p3Data p3I (p3Point 1))
      p3Data.f (p3Point 1)
    have he := p3_fiber_singleton (p3Point 1) p3_original_optimum.1.1
    refine ⟨⟨⟨p3_original_optimum.1.1,fun _ => rfl⟩,p3_original_optimum.1.2.1⟩,?_⟩
    intro z hz
    have heq : z = p3Point 1 := by simpa only [he,Set.mem_singleton_iff] using hz.1
    rw [heq]

theorem p3_left_improved_lp_empty (H : List (RealVector 1)) (hH : H ≠ []) :
    stSourceLP p3Data p3Left H p3Policy (some (-1)) = ∅ := by
  apply Set.eq_empty_iff_forall_notMem.mpr
  intro z hz
  have hh := (st_source_lp_mem_iff _ _ _ _ _ _).mp hz
  obtain ⟨a,ha⟩ := List.exists_mem_of_ne_nil H hH
  have ho := hh.2.2.2.1 a ha
  rw [p3_objective_tangent] at ho
  have hy := (p3_left_holds_iff z.1).mp hh.2.1
  have hc := hh.2.2.2.2
  change z.2 ≤ -1-1/4 at hc
  linarith

theorem p3_right_improved_lp_empty (k : ℕ) :
    stSourceLP p3Data p3Right (p3Anchors k ++ [p3Point 1]) p3Policy (some (-1)) = ∅ := by
  rw [st_source_lp_append,p3_right_lp_empty]
  simp

def p3BRepeated (_cap k allowance : ℕ) : STBudgetState p3I :=
  ⟨p3Seeds k,[p3Batch 0 false,p3Batch 2 true],some (p3Point 0),[⟨p3Root,allowance⟩],none⟩
def p3BSplit (cap k : ℕ) : STBudgetState p3I :=
  ⟨p3Seeds k,[p3Batch 0 false,p3Batch 2 true],some (p3Point 0),
    [⟨p3Left,cap⟩,⟨p3Right,cap⟩],none⟩
def p3BImproved (cap k : ℕ) : STBudgetState p3I :=
  ⟨p3Seeds k,[p3Batch 0 false,p3Batch 2 true,p3Batch 1 false],some (p3Point 1),
    [⟨p3Left,cap⟩,⟨p3Right,cap⟩],none⟩
def p3BRight (cap k : ℕ) : STBudgetState p3I :=
  ⟨p3Seeds k,[p3Batch 0 false,p3Batch 2 true,p3Batch 1 false],some (p3Point 1),
    [⟨p3Right,cap⟩],none⟩
def p3BDone (k : ℕ) : STBudgetState p3I :=
  ⟨p3Seeds k,[p3Batch 0 false,p3Batch 2 true,p3Batch 1 false],some (p3Point 1),[],none⟩

theorem p3_budget_initialized (cap : ℕ) :
    STBudgetInitialize p3Data p3I (fun _ => 1) cap
      (some (stBudgetInitial p3Data p3I cap (p3Batch 0 false))) :=
  STBudgetInitialize.seeded (p3Point 0) (p3Batch 0 false)
    ((p3_polyhedron_iff _).mpr (by norm_num [p3Point]))
    (by simpa using p3_point_integral 0) p3_initial_batch_valid (fun _ => rfl)

theorem p3_budget_first_callback (cap : ℕ) :
    STBudgetProcess p3Data p3I (fun _ => 1) p3Policy cap
      (stBudgetInitial p3Data p3I cap (p3Batch 0 false)) (p3BRepeated cap 0 cap) := by
  let working : STBudgetState p3I :=
    ⟨[],[p3Batch 0 false],some (p3Point 0),[],some ⟨p3Root,cap⟩⟩
  refine ⟨working,?_,?_⟩
  · simpa [stBudgetInitial,stSourceBatchInc,stSourceBest,p3Batch,p3Root,working] using
      (STBudgetSelect.choose [] [p3Batch 0 false] (some (p3Point 0)) [] [] ⟨p3Root,cap⟩)
  · have hh := STBudgetResolve.callback (D:=p3Data) (I:=p3I) (w:=fun _ => 1)
      (policy:=p3Policy) (cap:=cap) (seeds:=[]) (H:=[p3Batch 0 false])
      (inc:=some (p3Point 0)) (live:=[]) (B:=⟨p3Root,cap⟩)
      (q:=(p3Point 2,-2)) (b:=p3Batch 2 true)
      (by simpa [p3Batch,p3Data,p3Point] using p3_first_lp_minimum)
      (by simpa using p3_point_integral 2) p3_infeasible_batch_valid (fun _ => rfl)
    simpa [working,p3BRepeated,p3Seeds,stSourceBatchInc,p3Batch] using hh

theorem p3_budget_cut (cap k allowance : ℕ) (ha : 0 < allowance) :
    STBudgetProcess p3Data p3I (fun _ => 1) p3Policy cap
      (p3BRepeated cap k allowance) (p3BRepeated cap (k+1) (allowance-1)) := by
  let working : STBudgetState p3I :=
    ⟨p3Seeds k,[p3Batch 0 false,p3Batch 2 true],some (p3Point 0),[],
      some ⟨p3Root,allowance⟩⟩
  refine ⟨working,?_,?_⟩
  · exact STBudgetSelect.choose _ _ _ [] [] _
  · have hh := STBudgetResolve.cut (D:=p3Data) (I:=p3I) (w:=fun _ => 1)
      (policy:=p3Policy) (cap:=cap) (seeds:=p3Seeds k)
      (H:=[p3Batch 0 false,p3Batch 2 true]) (inc:=some (p3Point 0))
      (live:=[]) (B:=⟨p3Root,allowance⟩) (q:=p3LPPoint k) p3Index
      (by simpa [p3Batch,p3Data,p3Point,p3Anchors] using p3_every_fractional_lp_minimum k)
      (p3_trial_fractional k) ha
    simpa [working,p3BRepeated,p3_seeds_succ,p3LPPoint] using hh

theorem p3_budget_branch (cap k allowance : ℕ) :
    STBudgetProcess p3Data p3I (fun _ => 1) p3Policy cap
      (p3BRepeated cap k allowance) (p3BSplit cap k) := by
  let working : STBudgetState p3I :=
    ⟨p3Seeds k,[p3Batch 0 false,p3Batch 2 true],some (p3Point 0),[],
      some ⟨p3Root,allowance⟩⟩
  refine ⟨working,?_,?_⟩
  · exact STBudgetSelect.choose _ _ _ [] [] _
  · have hh := STBudgetResolve.branch (D:=p3Data) (I:=p3I) (w:=fun _ => 1)
      (policy:=p3Policy) (cap:=cap) (seeds:=p3Seeds k)
      (H:=[p3Batch 0 false,p3Batch 2 true]) (inc:=some (p3Point 0))
      (live:=[]) (B:=⟨p3Root,allowance⟩) (q:=p3LPPoint k) p3Index
      (by simpa [p3Batch,p3Data,p3Point,p3Anchors] using p3_every_fractional_lp_minimum k)
      (p3_trial_fractional k)
    simpa [working,p3BRepeated,p3BSplit,p3LPPoint,p3Point,p3_trial_left,p3_trial_right] using hh

theorem p3_budget_improve (cap k : ℕ) :
    STBudgetProcess p3Data p3I (fun _ => 1) p3Policy cap
      (p3BSplit cap k) (p3BImproved cap k) := by
  let working : STBudgetState p3I :=
    ⟨p3Seeds k,[p3Batch 0 false,p3Batch 2 true],some (p3Point 0),[⟨p3Right,cap⟩],
      some ⟨p3Left,cap⟩⟩
  refine ⟨working,?_,?_⟩
  · exact STBudgetSelect.choose _ _ _ [] [⟨p3Right,cap⟩] _
  · have hh := STBudgetResolve.callback (D:=p3Data) (I:=p3I) (w:=fun _ => 1)
      (policy:=p3Policy) (cap:=cap) (seeds:=p3Seeds k)
      (H:=[p3Batch 0 false,p3Batch 2 true]) (inc:=some (p3Point 0))
      (live:=[⟨p3Right,cap⟩]) (B:=⟨p3Left,cap⟩) (q:=(p3Point 1,-1)) (b:=p3Batch 1 false)
      (by simpa [p3Batch,p3Data,p3Point,p3Anchors] using p3_left_lp_minimum k)
      (by intro i; exact ⟨1,by simp [p3Point]⟩) p3_improving_batch_valid (fun _ => rfl)
    simpa [working,p3BSplit,p3BImproved,stSourceBatchInc,stSourceBest,p3Batch,p3Data,p3Point] using hh

theorem p3_budget_close_left (cap k : ℕ) :
    STBudgetProcess p3Data p3I (fun _ => 1) p3Policy cap
      (p3BImproved cap k) (p3BRight cap k) := by
  let working : STBudgetState p3I :=
    ⟨p3Seeds k,[p3Batch 0 false,p3Batch 2 true,p3Batch 1 false],some (p3Point 1),
      [⟨p3Right,cap⟩],some ⟨p3Left,cap⟩⟩
  refine ⟨working,?_,?_⟩
  · exact STBudgetSelect.choose _ _ _ [] [⟨p3Right,cap⟩] _
  · apply STBudgetResolve.empty
    exact p3_left_improved_lp_empty _ (by simp)

theorem p3_budget_close_right (cap k : ℕ) :
    STBudgetProcess p3Data p3I (fun _ => 1) p3Policy cap
      (p3BRight cap k) (p3BDone k) := by
  let working : STBudgetState p3I :=
    ⟨p3Seeds k,[p3Batch 0 false,p3Batch 2 true,p3Batch 1 false],some (p3Point 1),[],
      some ⟨p3Right,cap⟩⟩
  refine ⟨working,?_,?_⟩
  · exact STBudgetSelect.choose _ _ _ [] [] _
  · apply STBudgetResolve.empty
    simpa [p3Anchors,p3Batch,p3Data,p3Point,List.append_assoc] using p3_right_improved_lp_empty k

theorem p3_budget_zero_trace : STBudgetTrace p3Data p3I (fun _ => 1) p3Policy 0 5
    (stBudgetInitial p3Data p3I 0 (p3Batch 0 false)) (p3BDone 0) :=
  .cons (p3_budget_first_callback 0) (.cons (p3_budget_branch 0 0 0)
    (.cons (p3_budget_improve 0 0) (.cons (p3_budget_close_left 0 0)
      (.cons (p3_budget_close_right 0 0) (.nil _)))))

theorem p3_budget_one_trace : STBudgetTrace p3Data p3I (fun _ => 1) p3Policy 1 6
    (stBudgetInitial p3Data p3I 1 (p3Batch 0 false)) (p3BDone 1) :=
  .cons (p3_budget_first_callback 1) (.cons (p3_budget_cut 1 0 1 (by decide))
    (.cons (p3_budget_branch 1 1 0) (.cons (p3_budget_improve 1 1)
      (.cons (p3_budget_close_left 1 1) (.cons (p3_budget_close_right 1 1) (.nil _))))))

theorem p3_budget_zero_microtrace : STBudgetMicroTrace p3Data p3I (fun _ => 1) p3Policy 0 10
    (stBudgetInitial p3Data p3I 0 (p3Batch 0 false)) (p3BDone 0) :=
  st_budget_trace_micro p3Data (fun _ => 1) p3Policy 0 p3_budget_zero_trace

theorem p3_budget_one_microtrace : STBudgetMicroTrace p3Data p3I (fun _ => 1) p3Policy 1 12
    (stBudgetInitial p3Data p3I 1 (p3Batch 0 false)) (p3BDone 1) :=
  st_budget_trace_micro p3Data (fun _ => 1) p3Policy 1 p3_budget_one_trace

theorem p3_budget_final_stop (k : ℕ) : STBudgetStop (p3BDone k) (some (p3Point 1)) :=
  .exhausted rfl rfl

theorem p3_budget_final_optimal (k : ℕ) :
    (p3BDone k).incumbent = some (p3Point 1) ∧
      IsMinimizer (p3Data.feasible p3I) p3Data.f (p3Point 1) :=
  ⟨rfl,p3_original_optimum⟩

theorem p3_each_cut_excludes_its_trial (k : ℕ) :
    ¬ stSourceRows p3Data (p3Point (p3Trial k)) (p3Point (p3Trial k)) := by
  intro h
  have hh := (p3_rows_iff (p3Trial k) _).mp h
  change 2*p3Trial k*p3Trial k-(p3Trial k)^2-2 ≤ 0 at hh
  nlinarith [(p3_trial_properties k).2.2]

theorem p3_repeated_no_stop (k : ℕ) (out : Option (RealVector 1)) :
    ¬ STSourceStop (p3Repeated k) out := by
  intro h
  cases h with
  | exhausted hw hl => simp [p3Repeated] at hl

theorem p3_source_initialized_no_stop (k : ℕ) (out : Option (RealVector 1)) :
    ¬ STSourceStop (p3UnrestrictedRun k) out := by
  cases k with
  | zero =>
    intro h
    cases h with
    | exhausted hw hl => simp [p3UnrestrictedRun,stSourceInitial] at hl
  | succ k => exact p3_repeated_no_stop k out

end Chapter02STBudgetExamples

#print axioms Chapter02STBudgetExamples.p3_polyhedron_iff
#print axioms Chapter02STBudgetExamples.p3_polyhedron_bounded
#print axioms Chapter02STBudgetExamples.p3_encloses_two
#print axioms Chapter02STBudgetExamples.p3_objective_convex
#print axioms Chapter02STBudgetExamples.p3_rows_convex
#print axioms Chapter02STBudgetExamples.p3_objective_smooth
#print axioms Chapter02STBudgetExamples.p3_rows_smooth
#print axioms Chapter02STBudgetExamples.p3_objective_tangent
#print axioms Chapter02STBudgetExamples.p3_constraint_tangent
#print axioms Chapter02STBudgetExamples.p3_fiber_singleton
#print axioms Chapter02STBudgetExamples.p3_point_integral
#print axioms Chapter02STBudgetExamples.p3_initial_batch_valid
#print axioms Chapter02STBudgetExamples.p3_infeasible_batch_valid
#print axioms Chapter02STBudgetExamples.p3_original_optimum
#print axioms Chapter02STBudgetExamples.p3_feasible_rows_strict
#print axioms Chapter02STBudgetExamples.p3_fiber_slater
#print axioms Chapter02STBudgetExamples.p3_next_properties
#print axioms Chapter02STBudgetExamples.p3_trial_properties
#print axioms Chapter02STBudgetExamples.p3_trial_strict_decrease
#print axioms Chapter02STBudgetExamples.p3_trial_antitone
#print axioms Chapter02STBudgetExamples.p3_trial_fractional
#print axioms Chapter02STBudgetExamples.p3_rows_iff
#print axioms Chapter02STBudgetExamples.p3_rows_next_iff
#print axioms Chapter02STBudgetExamples.p3_seeds_succ
#print axioms Chapter02STBudgetExamples.p3_trial_all_rows
#print axioms Chapter02STBudgetExamples.p3_all_rows_upper
#print axioms Chapter02STBudgetExamples.p3_every_fractional_lp_minimum
#print axioms Chapter02STBudgetExamples.p3_zero_not_optimal
#print axioms Chapter02STBudgetExamples.p3_one_still_admitted
#print axioms Chapter02STBudgetExamples.p3_unrestricted_cut_step
#print axioms Chapter02STBudgetExamples.p3_unrestricted_infinite_from_repeated
#print axioms Chapter02STBudgetExamples.p3_dropped_cut_step
#print axioms Chapter02STBudgetExamples.p3_dropped_breaks_coverage
#print axioms Chapter02STBudgetExamples.p3_first_lp_minimum
#print axioms Chapter02STBudgetExamples.p3_source_initialized
#print axioms Chapter02STBudgetExamples.p3_first_actual_callback
#print axioms Chapter02STBudgetExamples.p3_source_initialized_infinite_execution
#print axioms Chapter02STBudgetExamples.p3_source_initialized_dropped_failure
#print axioms Chapter02STBudgetExamples.p3_trial_floor
#print axioms Chapter02STBudgetExamples.p3_trial_ceil
#print axioms Chapter02STBudgetExamples.p3_floor_three_halves
#print axioms Chapter02STBudgetExamples.p3_ceil_three_halves
#print axioms Chapter02STBudgetExamples.p3_trial_left
#print axioms Chapter02STBudgetExamples.p3_trial_right
#print axioms Chapter02STBudgetExamples.p3_left_holds_iff
#print axioms Chapter02STBudgetExamples.p3_right_holds_iff
#print axioms Chapter02STBudgetExamples.p3_left_lp_minimum
#print axioms Chapter02STBudgetExamples.p3_right_lp_empty
#print axioms Chapter02STBudgetExamples.p3_improving_batch_valid
#print axioms Chapter02STBudgetExamples.p3_left_improved_lp_empty
#print axioms Chapter02STBudgetExamples.p3_right_improved_lp_empty
#print axioms Chapter02STBudgetExamples.p3_budget_initialized
#print axioms Chapter02STBudgetExamples.p3_budget_first_callback
#print axioms Chapter02STBudgetExamples.p3_budget_cut
#print axioms Chapter02STBudgetExamples.p3_budget_branch
#print axioms Chapter02STBudgetExamples.p3_budget_improve
#print axioms Chapter02STBudgetExamples.p3_budget_close_left
#print axioms Chapter02STBudgetExamples.p3_budget_close_right
#print axioms Chapter02STBudgetExamples.p3_budget_zero_trace
#print axioms Chapter02STBudgetExamples.p3_budget_one_trace
#print axioms Chapter02STBudgetExamples.p3_budget_zero_microtrace
#print axioms Chapter02STBudgetExamples.p3_budget_one_microtrace
#print axioms Chapter02STBudgetExamples.p3_budget_final_stop
#print axioms Chapter02STBudgetExamples.p3_budget_final_optimal
#print axioms Chapter02STBudgetExamples.p3_each_cut_excludes_its_trial
#print axioms Chapter02STBudgetExamples.p3_repeated_no_stop
#print axioms Chapter02STBudgetExamples.p3_source_initialized_no_stop
