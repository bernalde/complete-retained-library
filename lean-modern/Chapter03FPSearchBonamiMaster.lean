module

public import Chapter03FPSearchBonamiData
public import Chapter03FPSearchSource

@[expose] public section

/-! Exact basic repeated masters and the enhanced first exclusion for the held
degenerate example. Assertions concern mathematical minima, not solver traces. -/
noncomputable section
open scoped BigOperators RealInnerProductSpace
open Chapter02 Chapter03.FP
namespace Chapter03.FPSearch.Bonami

def failed : Event 2 1 := ⟨integer 1,seed⟩
def repeated (k : ℕ) : State 2 1 := ⟨seed,List.replicate k failed⟩

theorem initial_rows_iff (p : P) :
    (∀ j, tangent data seed j p ≤ 0) ↔ p.1 1=0 ∧ p.2 0 ≤ p.1 0 := by
  norm_num [tangent,data,row,rowD,seed,point,xc,yc,Fin.forall_fin_succ]
  constructor
  · rintro ⟨h0,h1,h2⟩; exact ⟨by linarith,by linarith⟩
  · rintro ⟨h0,h1⟩; exact ⟨by linarith,by linarith,by linarith⟩

theorem repeated_rows_iff (k : ℕ) (p : P) :
    Rows data (repeated k) p ↔ p.1 1=0 ∧ p.2 0 ≤ p.1 0 := by
  constructor
  · intro h; exact (initial_rows_iff p).mp h.1
  · intro h
    have hi := (initial_rows_iff p).mpr h
    refine ⟨hi,?_⟩
    intro e he j hj
    have heq : e=failed := (List.mem_replicate.mp he).2
    subst e
    exact hi j

theorem repeated_master_iff (k : ℕ) (p : P) :
    p ∈ master data .basic (repeated k) ↔
      (p.2 0=0 ∨ p.2 0=1) ∧ p.1 1=0 ∧ p.2 0 ≤ p.1 0 := by
  constructor
  · rintro ⟨hb,hi,hr,hn⟩
    obtain ⟨q,hq⟩ := hi
    have he : p.2 0=(q 0:ℝ) := congrFun hq 0
    have hb' : 0 ≤ (q 0:ℝ) ∧ (q 0:ℝ) ≤ 1 := by simpa only [data,base,Set.mem_setOf_eq,he] using hb
    have hv := FPUnboundedControls.binary_value hb'.1 hb'.2
    refine ⟨?_,(repeated_rows_iff k p).mp hr⟩
    rcases hv with h|h <;> simp [he,h]
  · rintro ⟨hi,hr⟩
    refine ⟨?_,?_,(repeated_rows_iff k p).mpr hr,by simp⟩
    · rcases hi with h|h <;> simp [data,base,h]
    · rcases hi with h|h
      · refine ⟨integer 0,?_⟩; funext j; fin_cases j; simpa [integer,intCast] using h
      · refine ⟨integer 1,?_⟩; funext j; fin_cases j; simpa [integer,intCast] using h

theorem repeated_reference (k : ℕ) : (repeated k).reference=seed := by
  cases k with
  | zero => rfl
  | succ k => simp [State.reference,repeated,List.replicate_succ',failed]

theorem repeated_master_one (k : ℕ) :
    IsMinimizer (master data .basic (repeated k)) (masterCost (repeated k)) masterOne := by
  refine ⟨(repeated_master_iff k masterOne).mpr (by norm_num [masterOne,point]),?_⟩
  intro p hp
  have hi := ((repeated_master_iff k p).mp hp).1
  simp only [masterCost,repeated_reference,FPUnboundedControls.scalar_l1]
  rcases hi with h|h <;> norm_num [masterOne,seed,point,h]

theorem failed_normal (p : P) : failed.normal p=(1/2-(1:ℝ))*(p.2 0-1/2) := by
  simp [Event.normal,failed,seed,point,integer,Chapter03.yMap,intY,intCast,
    PiLp.inner_apply,Fin.sum_univ_one,real_inner_eq_re_inner]
  ring

theorem first_enhanced_master_iff (p : P) :
    p ∈ master data .enhanced (repeated 1) ↔
      p.2 0=0 ∧ p.1 1=0 ∧ 0 ≤ p.1 0 := by
  constructor
  · rintro ⟨hb,hi,hr,hn⟩
    have hbmaster : p ∈ master data .basic (repeated 1) := ⟨hb,hi,hr,by simp⟩
    obtain ⟨ht,hv,hu⟩ := (repeated_master_iff 1 p).mp hbmaster
    have hn' := hn rfl failed (by simp [repeated])
    rw [failed_normal] at hn'
    have ht0 : p.2 0=0 := by rcases ht with h|h; exact h; rw [h] at hn'; norm_num at hn'
    exact ⟨ht0,hv,by linarith⟩
  · rintro ⟨ht,hv,hu⟩
    have h := (repeated_master_iff 1 p).mpr ⟨Or.inl ht,hv,by linarith⟩
    refine ⟨h.1,h.2.1,h.2.2.1,?_⟩
    intro hm e he
    have heq : e=failed := (List.mem_replicate.mp he).2
    subst e
    rw [failed_normal,ht]
    norm_num

theorem first_enhanced_zero :
    IsMinimizer (master data .enhanced (repeated 1)) (masterCost (repeated 1)) projectedZero := by
  refine ⟨(first_enhanced_master_iff projectedZero).mpr (by norm_num [projectedZero,point]),?_⟩
  intro p hp
  have ht := ((first_enhanced_master_iff p).mp hp).1
  simp only [masterCost,repeated_reference,FPUnboundedControls.scalar_l1]
  simp [projectedZero,point,ht]

theorem binary_target_bound (mode : Mode) :
    TargetBound data mode (integerBox_finite (fun _ : Fin 1 => (0:ℝ)) (fun _ => 1)).toFinset := by
  apply hard_box_target_bound
  intro p hp j
  fin_cases j
  exact hp

end Chapter03.FPSearch.Bonami
