module

public import Chapter03OAKKTBoundaryData

@[expose] public section

noncomputable section
open scoped BigOperators
open Chapter02 Chapter06
namespace Chapter03.OAKKTBoundary

/-- One-slot master for the all-row seed, before adding the current slot. -/
def zeroSeedHistory : TangentFamily 1 0 2 1 where
  origin := fun _ => zeroPoint 1
  selected := fun _ => Set.univ
  derivative := fun _ => zeroDerivative (zeroPoint 1)

/-- The complete two-slot row-selection control. `weak=true` implements >=0;
`weak=false` is the contrasting >0 selection. -/
def zeroHistory (weak : Bool) : TangentFamily 1 0 2 2 where
  origin := ![zeroPoint 1,zeroPoint (1/2)]
  selected := fun i => if i=0 then Set.univ else
    if weak then {j | 0 ≤ zeroData.g j (zeroPoint (1/2))}
    else {j | 0 < zeroData.g j (zeroPoint (1/2))}
  derivative := fun i => zeroDerivative (![zeroPoint 1,zeroPoint (1/2)] i)

theorem zero_history_distinct_slots : (0 : Fin 2) ≠ 1 := by decide

theorem zero_history_actual_derivatives (weak : Bool) (i j : Fin 2) :
    HasFDerivAt (zeroData.g j) ((zeroHistory weak).derivative i j)
      ((zeroHistory weak).origin i) := zero_derivative _ j

theorem zero_objective_derivative (p : Point 1 0) :
    HasFDerivAt (fun _ : Point 1 0 => (0 : ℝ)) (0 : Point 1 0 →L[ℝ] ℝ) p := hasFDerivAt_const 0 p

theorem zero_current_weak_selection : (zeroHistory true).selected 1 = Set.univ := by
  ext j
  fin_cases j <;> norm_num [zeroHistory,zeroData,zeroPoint,vec]

theorem zero_current_strict_selection : (zeroHistory false).selected 1 = {0} := by
  ext j
  fin_cases j <;> norm_num [zeroHistory,zeroData,zeroPoint,vec]

theorem zero_seed_master_admits :
    (zeroPoint 0,0) ∈ EpigraphMaster zeroData (fun _ => 0) zeroSeedHistory
      (fun _ => 0) Set.univ := by
  refine ⟨⟨⟨⟨Set.mem_univ _,?_⟩,fun j => Fin.elim0 j⟩,0,?_,?_⟩,?_⟩
  · intro i j hj
    fin_cases i; fin_cases j <;>
      norm_num [zeroSeedHistory,zeroData,zeroPoint,vec,zeroDerivative]
  · intro i; exact Fin.elim0 i
  · funext i; exact Fin.elim0 i
  · intro i; simp

theorem zero_strict_full_master_admits :
    (zeroPoint 0,0) ∈ EpigraphMaster zeroData (fun _ => 0) (zeroHistory false)
      (fun _ => 0) Set.univ := by
  refine ⟨⟨⟨⟨Set.mem_univ _,?_⟩,fun j => Fin.elim0 j⟩,0,?_,?_⟩,?_⟩
  · intro i j hj
    fin_cases i <;> fin_cases j <;>
      norm_num [zeroHistory,zeroData,zeroPoint,vec,zeroDerivative] at hj <;>
      norm_num [zeroHistory,zeroData,zeroPoint,vec,zeroDerivative]
  · intro i; exact Fin.elim0 i
  · funext i; exact Fin.elim0 i
  · intro i; simp

/-- Direct inspection of the actual full master, additional to the generic KKT
consumer supplied in the source-boundary module. -/
theorem zero_weak_full_master_empty :
    EpigraphMaster zeroData (fun _ => 0) (zeroHistory true)
      (fun _ => 0) Set.univ = ∅ := by
  apply Set.eq_empty_iff_forall_notMem.mpr
  intro p hp
  have h0 := hp.1.1.1.2 1 0 (by rw [zero_current_weak_selection]; trivial)
  have h1 := hp.1.1.1.2 1 1 (by rw [zero_current_weak_selection]; trivial)
  change zeroData.g 0 (zeroPoint (1/2))+
    zeroDerivative (zeroPoint (1/2)) 0 (p.1-zeroPoint (1/2)) ≤ 0 at h0
  change zeroData.g 1 (zeroPoint (1/2))+
    zeroDerivative (zeroPoint (1/2)) 1 (p.1-zeroPoint (1/2)) ≤ 0 at h1
  rw [(zero_current_tangents p.1).1] at h0
  rw [(zero_current_tangents p.1).2] at h1
  linarith

end Chapter03.OAKKTBoundary
