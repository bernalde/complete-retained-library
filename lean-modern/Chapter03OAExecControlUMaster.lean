module

public import Chapter03OAExecControlCases

@[expose] public section

noncomputable section
open Chapter02 Chapter02DICOPTExamples Chapter03.OAKKT
open Chapter03.OAKKT.Controls
open scoped BigOperators
namespace Chapter03.OAExec.Controls.U

theorem master_iff (H : List (Event spec)) (hv : ∀e∈H,EventValid spec e) (z : P×ℝ) :
    z∈master spec seed H ↔
    (z.1.2 0=0 ∨ z.1.2 0=1) ∧ z.1.1 0≤z.2 ∧
    (event0∈H → z.1.1 0-z.1.2 0+1/4≤z.2 ∧
      -z.1.1 0-z.1.2 0≤0 ∧ z.1.1 0-z.1.2 0≤0) ∧
    (event1∈H → z.1.1 0+z.1.2 0-3/4≤z.2 ∧
      z.1.1 0+z.1.2 0-1≤0 ∧ -z.1.1 0+z.1.2 0-1≤0) := by
  constructor
  · intro hz
    obtain ⟨_,hy,_,hf,he,_⟩ := (master_mem_iff spec seed H z).mp hz
    refine ⟨(cylinder_binary z.1).mp hy,?_,fun h => (event0_rows z).mp (he event0 h),
      fun h => (event1_rows z).mp (he event1 h)⟩
    change objective seed+Df seed (z.1-seed)≤z.2 at hf
    rwa [seed_objective_tangent] at hf
  · rintro ⟨hy,hf,h0,h1⟩
    apply (master_mem_iff spec seed H z).mpr
    refine ⟨hard _,(cylinder_binary z.1).mpr hy,?_,?_,?_,?_⟩
    · apply (seed_rows z.1).mpr
      rcases hy with hy|hy <;> simp [hy]
    · change objective seed+Df seed (z.1-seed)≤z.2
      rwa [seed_objective_tangent]
    · intro e he
      rcases valid_event_cases (hv e he) with rfl|rfl
      · exact (event0_rows z).mpr (h0 he)
      · exact (event1_rows z).mpr (h1 he)
    · intro e he hn
      rcases valid_event_cases (hv e he) with rfl|rfl <;> exact False.elim (hn rfl)

theorem only0_minimum (H : List (Event spec)) (hv : ∀e∈H,EventValid spec e)
    (h0 : event0∈H) (h1 : event1∉H) :
    IsMinimizer (master spec seed H) Prod.snd (pt (-1) 1,-1) := by
  refine ⟨(master_iff H hv _).mpr (by norm_num [pt,scalar,h0,h1]),?_⟩
  intro z hz
  obtain ⟨hy,hf,hc,_⟩ := (master_iff H hv z).mp hz
  obtain ⟨ha,hb,hc⟩ := hc h0
  change (-1:ℝ)≤z.2
  rcases hy with hy|hy <;> linarith

theorem only1_minimum (H : List (Event spec)) (hv : ∀e∈H,EventValid spec e)
    (h0 : event0∉H) (h1 : event1∈H) :
    IsMinimizer (master spec seed H) Prod.snd (pt (-1) 0,-1) := by
  refine ⟨(master_iff H hv _).mpr (by norm_num [pt,scalar,h0,h1]),?_⟩
  intro z hz
  obtain ⟨hy,hf,_,hc⟩ := (master_iff H hv z).mp hz
  obtain ⟨ha,hb,hc⟩ := hc h1
  change (-1:ℝ)≤z.2
  rcases hy with hy|hy <;> linarith

theorem only0_unique (H : List (Event spec)) (hv : ∀e∈H,EventValid spec e)
    (h0 : event0∈H) (h1 : event1∉H) {z : P×ℝ}
    (hm : IsMinimizer (master spec seed H) Prod.snd z) : z=(pt (-1) 1,-1) := by
  have hh := hm.2 _ (only0_minimum H hv h0 h1).1
  change z.2≤-1 at hh
  obtain ⟨hy,hf,hc,_⟩ := (master_iff H hv z).mp hm.1
  obtain ⟨ha,hb,hc⟩ := hc h0
  rcases hy with hy|hy
  · exfalso; linarith
  · exact Prod.ext (point_ext (by norm_num [pt,scalar]; linarith) hy) (by change z.2=-1; linarith)

theorem only1_unique (H : List (Event spec)) (hv : ∀e∈H,EventValid spec e)
    (h0 : event0∉H) (h1 : event1∈H) {z : P×ℝ}
    (hm : IsMinimizer (master spec seed H) Prod.snd z) : z=(pt (-1) 0,-1) := by
  have hh := hm.2 _ (only1_minimum H hv h0 h1).1
  change z.2≤-1 at hh
  obtain ⟨hy,hf,_,hc⟩ := (master_iff H hv z).mp hm.1
  obtain ⟨ha,hb,hc⟩ := hc h1
  rcases hy with hy|hy
  · exact Prod.ext (point_ext (by norm_num [pt,scalar]; linarith) hy) (by change z.2=-1; linarith)
  · exfalso; linarith

theorem both_minimum (H : List (Event spec)) (hv : ∀e∈H,EventValid spec e)
    (h0 : event0∈H) (h1 : event1∈H) (b : ℝ) (hb : b=0 ∨ b=1) :
    IsMinimizer (master spec seed H) Prod.snd (pt 0 b,1/4) := by
  refine ⟨(master_iff H hv _).mpr ?_,?_⟩
  · rcases hb with rfl|rfl <;> norm_num [pt,scalar,h0,h1]
  · intro z hz
    obtain ⟨hy,hf,hc0,hc1⟩ := (master_iff H hv z).mp hz
    obtain ⟨ha,hb,hc⟩ := hc0 h0
    obtain ⟨hd,he,hf'⟩ := hc1 h1
    change (1/4:ℝ)≤z.2
    rcases hy with hy|hy <;> linarith

theorem both_minimizer_cases (H : List (Event spec)) (hv : ∀e∈H,EventValid spec e)
    (h0 : event0∈H) (h1 : event1∈H) {z : P×ℝ}
    (hm : IsMinimizer (master spec seed H) Prod.snd z) :
    z=(pt 0 0,1/4) ∨ z=(pt 0 1,1/4) := by
  have hh := hm.2 _ (both_minimum H hv h0 h1 0 (Or.inl rfl)).1
  change z.2≤1/4 at hh
  obtain ⟨hy,hf,hc0,hc1⟩ := (master_iff H hv z).mp hm.1
  obtain ⟨ha,hb,hc⟩ := hc0 h0
  obtain ⟨hd,he,hf'⟩ := hc1 h1
  rcases hy with hy|hy
  · left; exact Prod.ext (point_ext (by norm_num [pt,scalar]; linarith) hy) (by linarith)
  · right; exact Prod.ext (point_ext (by norm_num [pt,scalar]; linarith) hy) (by linarith)

theorem neither_unbounded (H : List (Event spec)) (hv : ∀e∈H,EventValid spec e)
    (h0 : event0∉H) (h1 : event1∉H) :
    ¬ BddBelow (Prod.snd '' master spec seed H) := by
  rintro ⟨a,ha⟩
  have hz : (pt (a-1) 0,a-1)∈master spec seed H :=
    (master_iff H hv _).mpr (by norm_num [pt,scalar,h0,h1])
  have hh := ha ⟨(pt (a-1) 0,a-1),hz,rfl⟩
  change a≤a-1 at hh
  linarith

theorem initial_nonempty : (master spec seed []).Nonempty := by
  refine ⟨(pt 0 0,0),(master_iff [] (by simp) _).mpr ?_⟩
  norm_num [pt,scalar]

theorem initial_unbounded : ¬ BddBelow (Prod.snd '' master spec seed []) :=
  neither_unbounded [] (by simp) (by simp) (by simp)

/-- The thesis's requested exact master minimizer does not exist here. -/
theorem initial_no_minimizer : ¬∃z,IsMinimizer (master spec seed []) Prod.snd z := by
  rintro ⟨z,hz⟩
  apply initial_unbounded
  refine ⟨z.2,?_⟩
  rintro a ⟨w,hw,rfl⟩
  exact hz.2 w hw

theorem bounded_master_attained (H : List (Event spec)) (hv : ∀e∈H,EventValid spec e)
    (hb : BddBelow (Prod.snd '' master spec seed H)) :
    ∃z,IsMinimizer (master spec seed H) Prod.snd z := by
  classical
  by_cases h0 : event0∈H
  · by_cases h1 : event1∈H
    · exact ⟨_,both_minimum H hv h0 h1 0 (Or.inl rfl)⟩
    · exact ⟨_,only0_minimum H hv h0 h1⟩
  · by_cases h1 : event1∈H
    · exact ⟨_,only1_minimum H hv h0 h1⟩
    · exact False.elim (neither_unbounded H hv h0 h1 hb)

end Chapter03.OAExec.Controls.U
