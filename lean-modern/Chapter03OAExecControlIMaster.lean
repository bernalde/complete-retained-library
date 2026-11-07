module

public import Chapter03OAExecControlCases

@[expose] public section

noncomputable section
open Chapter02 Chapter02DICOPTExamples Chapter03.OAKKT
open Chapter03.OAKKT.Controls
open scoped BigOperators
namespace Chapter03.OAExec.Controls.I

theorem master_iff (H : List (Event spec)) (hv : ∀e∈H,EventValid spec e) (z : P×ℝ) :
    z∈master spec seed H ↔
    (z.1.2 0=0 ∨ z.1.2 0=1) ∧ z.1.1 0-z.1.2 0+3/16≤0 ∧
    -z.1.1 0+z.1.2 0≤z.2 ∧
    (event0∈H → 7/16-z.1.2 0≤0 ∧ z.1.2 0≠0) ∧
    (event1∈H → (3/2)*z.1.1 0-z.1.2 0-1/8≤0) := by
  constructor
  · intro hz
    obtain ⟨_,hy,hg,hf,he,hn⟩ := (master_mem_iff spec seed H z).mp hz
    have hs := (seed_rows z.1).mp hg
    change objective seed+Df (z.1-seed)≤z.2 at hf
    rw [objective_tangent] at hf
    refine ⟨(cylinder_binary z.1).mp hy,hs.1,hf,?_,?_⟩
    · intro h0
      refine ⟨((event0_rows z).mp (he event0 h0)).2,?_⟩
      intro hz0
      exact hn event0 h0 (by simp [event0]) (by simpa [event0] using (scalar_zero_iff z.1.2).mpr hz0)
    · intro h1; exact ((event1_rows z).mp (he event1 h1)).2
  · rintro ⟨hy,hs,hf,h0,h1⟩
    apply (master_mem_iff spec seed H z).mpr
    refine ⟨hard _,(cylinder_binary z.1).mpr hy,?_,?_,?_,?_⟩
    · apply (seed_rows z.1).mpr
      refine ⟨hs,?_⟩
      rcases hy with hy|hy <;> simp [hy]
    · change objective seed+Df (z.1-seed)≤z.2
      rw [objective_tangent]; exact hf
    · intro e he
      rcases valid_event_cases (hv e he) with rfl|rfl
      · exact (event0_rows z).mpr ⟨hf,(h0 he).1⟩
      · exact (event1_rows z).mpr ⟨hf,h1 he⟩
    · intro e he hn hz0
      rcases valid_event_cases (hv e he) with rfl|rfl
      · apply (h0 he).2
        exact (scalar_zero_iff z.1.2).mp (by simpa [event0] using hz0)
      · exact hn rfl

theorem master_height_lower (H : List (Event spec)) (hv : ∀e∈H,EventValid spec e)
    {z : P×ℝ} (hz : z∈master spec seed H) : (3/16:ℝ)≤z.2 := by
  obtain ⟨_,hs,hf,_,_⟩ := (master_iff H hv z).mp hz
  linarith

theorem neither_minimum (H : List (Event spec)) (hv : ∀e∈H,EventValid spec e)
    (h0 : event0∉H) (h1 : event1∉H) (b : ℝ) (hb : b=0 ∨ b=1) :
    IsMinimizer (master spec seed H) Prod.snd (pt (b-3/16) b,3/16) := by
  refine ⟨(master_iff H hv _).mpr ?_,fun z hz => master_height_lower H hv hz⟩
  rcases hb with rfl|rfl <;> norm_num [pt,scalar,h0,h1]

theorem neither_minimizer_cases (H : List (Event spec)) (hv : ∀e∈H,EventValid spec e)
    (h0 : event0∉H) (h1 : event1∉H) {z : P×ℝ}
    (hm : IsMinimizer (master spec seed H) Prod.snd z) :
    z=(pt (-3/16) 0,3/16) ∨ z=(pt (13/16) 1,3/16) := by
  have hh := hm.2 _ (neither_minimum H hv h0 h1 0 (Or.inl rfl)).1
  change z.2≤3/16 at hh
  obtain ⟨hy,hs,hf,_,_⟩ := (master_iff H hv z).mp hm.1
  rcases hy with hy|hy
  · left; exact Prod.ext (point_ext (by norm_num [pt,scalar]; linarith) hy) (by linarith)
  · right; exact Prod.ext (point_ext (by norm_num [pt,scalar]; linarith) hy) (by linarith)

theorem only0_minimum (H : List (Event spec)) (hv : ∀e∈H,EventValid spec e)
    (h0 : event0∈H) (h1 : event1∉H) :
    IsMinimizer (master spec seed H) Prod.snd (pt (13/16) 1,3/16) := by
  refine ⟨(master_iff H hv _).mpr ?_,fun z hz => master_height_lower H hv hz⟩
  norm_num [pt,scalar,h0,h1]

theorem only0_unique (H : List (Event spec)) (hv : ∀e∈H,EventValid spec e)
    (h0 : event0∈H) (h1 : event1∉H) {z : P×ℝ}
    (hm : IsMinimizer (master spec seed H) Prod.snd z) : z=(pt (13/16) 1,3/16) := by
  have hh := hm.2 _ (only0_minimum H hv h0 h1).1
  change z.2≤3/16 at hh
  obtain ⟨hy,hs,hf,hc,_⟩ := (master_iff H hv z).mp hm.1
  have hc := hc h0
  rcases hy with hy|hy
  · exact False.elim (hc.2 hy)
  · exact Prod.ext (point_ext (by norm_num [pt,scalar]; linarith) hy) (by linarith)

theorem only1_minimum (H : List (Event spec)) (hv : ∀e∈H,EventValid spec e)
    (h0 : event0∉H) (h1 : event1∈H) :
    IsMinimizer (master spec seed H) Prod.snd (pt (-3/16) 0,3/16) := by
  refine ⟨(master_iff H hv _).mpr ?_,fun z hz => master_height_lower H hv hz⟩
  norm_num [pt,scalar,h0,h1]

theorem only1_unique (H : List (Event spec)) (hv : ∀e∈H,EventValid spec e)
    (h0 : event0∉H) (h1 : event1∈H) {z : P×ℝ}
    (hm : IsMinimizer (master spec seed H) Prod.snd z) : z=(pt (-3/16) 0,3/16) := by
  have hh := hm.2 _ (only1_minimum H hv h0 h1).1
  change z.2≤3/16 at hh
  obtain ⟨hy,hs,hf,_,hc⟩ := (master_iff H hv z).mp hm.1
  have hc := hc h1
  rcases hy with hy|hy
  · exact Prod.ext (point_ext (by norm_num [pt,scalar]; linarith) hy) (by linarith)
  · exfalso; linarith

theorem both_minimum (H : List (Event spec)) (hv : ∀e∈H,EventValid spec e)
    (h0 : event0∈H) (h1 : event1∈H) :
    IsMinimizer (master spec seed H) Prod.snd (pt (3/4) 1,1/4) := by
  refine ⟨(master_iff H hv _).mpr ?_,?_⟩
  · norm_num [pt,scalar,h0,h1]
  · intro z hz
    obtain ⟨hy,hs,hf,hc0,hc1⟩ := (master_iff H hv z).mp hz
    have hc0 := hc0 h0
    have hc1 := hc1 h1
    change (1/4:ℝ)≤z.2
    rcases hy with hy|hy
    · exact False.elim (hc0.2 hy)
    · linarith

theorem both_unique (H : List (Event spec)) (hv : ∀e∈H,EventValid spec e)
    (h0 : event0∈H) (h1 : event1∈H) {z : P×ℝ}
    (hm : IsMinimizer (master spec seed H) Prod.snd z) : z=(pt (3/4) 1,1/4) := by
  have hh := hm.2 _ (both_minimum H hv h0 h1).1
  change z.2≤1/4 at hh
  obtain ⟨hy,hs,hf,hc0,hc1⟩ := (master_iff H hv z).mp hm.1
  have hc0 := hc0 h0
  have hc1 := hc1 h1
  rcases hy with hy|hy
  · exact False.elim (hc0.2 hy)
  · exact Prod.ext (point_ext (by norm_num [pt,scalar]; linarith) hy) (by linarith)

theorem master_attained (H : List (Event spec)) (hv : ∀e∈H,EventValid spec e) :
    ∃z,IsMinimizer (master spec seed H) Prod.snd z := by
  classical
  by_cases h0 : event0∈H
  · by_cases h1 : event1∈H
    · exact ⟨_,both_minimum H hv h0 h1⟩
    · exact ⟨_,only0_minimum H hv h0 h1⟩
  · by_cases h1 : event1∈H
    · exact ⟨_,only1_minimum H hv h0 h1⟩
    · exact ⟨_,neither_minimum H hv h0 h1 0 (Or.inl rfl)⟩

end Chapter03.OAExec.Controls.I
