module

public import Chapter03OAExecInvariant
public import Chapter03OAExecArticleOtherMasters

@[expose] public section

noncomputable section
open Chapter02 Chapter02DICOPTExamples Chapter03.OAKKT
namespace Chapter03.OAExec.Article

theorem A_master_height_nonneg (H : List (Event Adata)) {z : P × ℝ}
    (hz : z ∈ master Adata (pt 0 (1/2)) H) : 0 ≤ z.2 := by
  have h := ((master_mem_iff _ _ _ _).mp hz).2.2.2.1
  simpa [Adata,Af,Adf,quadratic,quadraticD,pt,scalar] using h

/-- Every nonempty A master from valid actual restoration events attains
height zero. The integer point is extracted from the given nonemptiness, and
all original g tangents and mandatory no-goods are checked. -/
theorem A_master_attained (H : List (Event Adata))
    (hH : ∀ e ∈ H, EventValid Adata e)
    (hne : (master Adata (pt 0 (1/2)) H).Nonempty) :
    ∃ z, IsMinimizer (master Adata (pt 0 (1/2)) H) Prod.snd z := by
  obtain ⟨q,hq⟩ := hne
  obtain ⟨y,hy,hqy⟩ := master_integer hq
  have hno := ((master_mem_iff _ _ _ _).mp hq).2.2.2.2.2
  let z : P × ℝ := ((scalar 0,intCast y),0)
  refine ⟨z,?_,?_⟩
  · rw [master_mem_iff]
    refine ⟨?_,⟨y,hy,rfl⟩,?_,?_,?_,?_⟩
    · exact (box_hard (-1) 1 _ _).mpr (by norm_num [z,scalar])
    · intro j
      norm_num [Adata,A,boxModel,Adg,quadratic,quadraticD,pt,scalar]
    · norm_num [Adata,Af,Adf,quadratic,quadraticD,pt,scalar,z]
    · intro e he
      rw [A_event_rows e (hH e he) z]
      have hne : y 0 ≠ e.target 0 := by
        intro heq
        apply hno e he (by rw [(A_event_characterization e (hH e he)).1]; simp)
        rw [hqy]
        ext i
        fin_cases i
        simp [intCast,heq]
      rcases (binary_box (-1) 1 _ y).mp hy with hy | hy <;>
        rcases (binary_box (-1) 1 _ e.target).mp e.target_mem with hb | hb
      · exact (hne (hy.trans hb.symm)).elim
      · norm_num [z,LiteralG.tangent,intCast,hy,hb,scalar]
      · norm_num [z,LiteralG.tangent,intCast,hy,hb,scalar]
      · exact (hne (hy.trans hb.symm)).elim
    · intro e he hn
      have hh := hno e he hn
      simpa only [hqy] using hh
  · intro w hw
    exact A_master_height_nonneg H hw

theorem T_initial_fractional : ¬ integral (pt 0 (1/4)) := by
  rintro ⟨y,hy⟩
  have h := congrFun hy 0
  change (1/4:ℝ)=(y 0:ℝ) at h
  have hl : (0:ℤ)<y 0 := by exact_mod_cast (show (0:ℝ)<(y 0:ℝ) by linarith)
  have hu : y 0<(1:ℤ) := by exact_mod_cast (show (y 0:ℝ)<(1:ℝ) by linarith)
  omega

theorem T_seed_valid : SeedValid Tdata (pt 0 (1/4)) :=
  ⟨T_initial_minimum,Set.mem_univ _,T_initial_fractional⟩

theorem A_seed_valid : SeedValid Adata (pt 0 (1/2)) :=
  ⟨A_initial_minimum,Set.mem_univ _,G_initial_fractional⟩

theorem T_local_availability (epsilon : ℝ) :
    LocalAvailability Tdata (pt 0 (1/4)) epsilon where
  master_attainment s hs _ _ _ := T_master_attained s.history
    (reachable_invariant T_analytic T_seed_valid hs).history.2
  fixed_or_restoration s hs ho q := by
    obtain ⟨y,hy,he⟩ := master_integer q.mem
    exact ⟨T_event y hy,T_event_valid y hy,he⟩

theorem A_local_availability (epsilon : ℝ) :
    LocalAvailability Adata (pt 0 (1/2)) epsilon where
  master_attainment s hs _ hne _ := A_master_attained s.history
    (reachable_invariant A_analytic A_seed_valid hs).history.2 hne
  fixed_or_restoration s hs ho q := by
    obtain ⟨y,hy,he⟩ := master_integer q.mem
    exact ⟨A_event y hy,A_event_valid y hy,he⟩

theorem T_selectors_exist (epsilon : ℝ) :
    Nonempty (Selector Tdata (pt 0 (1/4)) epsilon) :=
  selector_inhabited (T_local_availability epsilon)

theorem A_selectors_exist (epsilon : ℝ) :
    Nonempty (Selector Adata (pt 0 (1/2)) epsilon) :=
  selector_inhabited (A_local_availability epsilon)

end Chapter03.OAExec.Article
