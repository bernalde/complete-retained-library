module

public import Chapter03PumpOAModel

@[expose] public section

/-! Exact syntactic transfer identities for the real pump and hard OA masters.
No prefix validity or analytic hypothesis is needed. All accepted source and
previously released master/availability modules remain unchanged. -/
noncomputable section
open Chapter02 Chapter03.OAKKT
namespace Chapter03.PumpOA
variable {n m l r : ℕ}

/-- The unchanged all-row seed slot is present in every finite pump epigraph. -/
theorem pump_epigraph_seed_only (d : OAExec.Data n m l r) (delta : ℝ)
    (P : FP.State n m) {z : Point n m × ℝ}
    (hz : z ∈ FP.epigraph (asFPDelta d delta) P) :
    z ∈ OAExec.epigraph d P.seed [] := by
  refine (OAExec.epigraph_mem_iff d P.seed [] z).mpr
    ⟨hz.1.1.2,hz.1.2,?_,?_,by simp⟩
  · intro j
    exact hz.1.1.1.2 ⟨0,by simp [FP.anchors]⟩ j (Set.mem_univ j)
  · exact hz.2 ⟨0,by simp [FP.anchors]⟩

theorem pump_initial_epigraph_eq (d : OAExec.Data n m l r) (delta : ℝ)
    (seed : Point n m) :
    FP.epigraph (asFPDelta d delta) (FP.initialState seed) =
      OAExec.epigraph d seed [] := by
  ext z
  constructor
  · exact pump_epigraph_seed_only d delta (FP.initialState seed)
  · intro hz
    obtain ⟨hl,hy,hg,hf,_⟩ := (OAExec.epigraph_mem_iff d seed [] z).mp hz
    refine ⟨⟨⟨⟨Set.mem_univ _,?_⟩,hl⟩,hy⟩,?_⟩
    · intro i j _
      have hi : i = ⟨0,by simp [FP.anchors,FP.initialState]⟩ := by
        apply Fin.ext
        change i.val = 0
        have hb : i.val < 1 := i.isLt
        omega
      subst i
      exact hg j
    · intro i
      have hi : i = ⟨0,by simp [FP.anchors,FP.initialState]⟩ := by
        apply Fin.ext
        change i.val = 0
        have hb : i.val < 1 := i.isLt
        omega
      subst i
      exact hf

/-- The actual initial pump distance master has no cutoff, normal or no-good
restriction beyond the exact all-row seed OA epigraph. -/
theorem pump_initial_master_eq (d : OAExec.Data n m l r) (delta : ℝ)
    (seed : Point n m) :
    FP.master (asFPDelta d delta) (FP.initialState seed) = OAExec.master d seed [] := by
  ext z
  simp only [FP.master,OAExec.master,Set.mem_setOf_eq]
  rw [pump_initial_epigraph_eq]
  simp [FP.retainedNormals,FP.noGoods,FP.Data.level,FP.Allows,FP.initialState,
    OAExec.noGoods]

/-- Empty new OA history transfers precisely the real filtered pump handoff. -/
theorem empty_suffix_master_eq (d : OAExec.Data n m l r) (delta : ℝ)
    (P : FP.State n m) :
    master d delta P [] = FP.handoff (asFPDelta d delta) P := by
  ext z
  constructor
  · exact fun h => h.1
  · intro h
    exact ⟨h,pump_epigraph_seed_only d delta P h.1,by simp [OAExec.noGoods]⟩

/-- An actual initial pump prefix adds no rows beyond the seed already
retained by every OA suffix; the suffix's own rows and no-goods remain. -/
theorem initial_prefix_master_eq (d : OAExec.Data n m l r) (delta : ℝ)
    (seed : Point n m) (H : List (OAExec.Event d)) :
    master d delta (FP.initialState seed) H = OAExec.master d seed H := by
  ext z
  constructor
  · exact fun h => h.2
  · intro h
    obtain ⟨hl,hy,hg,hf,_,_⟩ := (OAExec.master_mem_iff d seed H z).mp h
    have he : z ∈ OAExec.epigraph d seed [] :=
      (OAExec.epigraph_mem_iff d seed [] z).mpr ⟨hl,hy,hg,hf,by simp⟩
    have hp : z ∈ FP.epigraph (asFPDelta d delta) (FP.initialState seed) := by
      rwa [pump_initial_epigraph_eq]
    refine ⟨⟨hp,?_,?_⟩,h⟩
    · simp [FP.handoffNormals,FP.initialState]
    · simp [FP.noGoods,FP.initialState]

end Chapter03.PumpOA

#check Chapter03.PumpOA.pump_epigraph_seed_only
#print axioms Chapter03.PumpOA.pump_epigraph_seed_only
#check Chapter03.PumpOA.pump_initial_epigraph_eq
#print axioms Chapter03.PumpOA.pump_initial_epigraph_eq
#check Chapter03.PumpOA.pump_initial_master_eq
#print axioms Chapter03.PumpOA.pump_initial_master_eq
#check Chapter03.PumpOA.empty_suffix_master_eq
#print axioms Chapter03.PumpOA.empty_suffix_master_eq
#check Chapter03.PumpOA.initial_prefix_master_eq
#print axioms Chapter03.PumpOA.initial_prefix_master_eq
