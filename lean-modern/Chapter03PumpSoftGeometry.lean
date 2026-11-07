module

public import Chapter03PumpSoftModel

@[expose] public section

noncomputable section
open Chapter02 Chapter03.OAKKT Chapter03.OAExec Chapter03.OASoftMaster
namespace Chapter03.PumpSoft
variable {n m l r : ℕ}

theorem family_origins_domain {d : OAExec.Data n m l r}
    (h : OAExec.AvailabilityAssumptions d) {delta : ℝ} {P : FP.State n m}
    (hP : FP.Invariant (PumpOA.asFPDelta d delta) P)
    {H : List (OAExec.Event d)} (hH : OAExec.ValidHistory d P.seed H) :
    ∀ i, (family d delta P H).origin i ∈ d.domain := by
  intro i
  refine Fin.addCases ?_ ?_ i
  · intro j
    rw [family_prefix_origin]
    rw [h.domain_base]
    exact FP.relaxation_subset_base (PumpOA.asFPDelta d delta)
      (FP.anchors_relaxation _ hP _ (List.get_mem _ j))
  · intro j
    rw [family_suffix_origin]
    exact (hH.2 _ (List.get_mem _ j)).1

theorem original_embed_mem {d : OAExec.Data n m l r}
    (h : OAExec.AvailabilityAssumptions d) {delta : ℝ} {P : FP.State n m}
    (hP : FP.Invariant (PumpOA.asFPDelta d delta) P)
    {H : List (OAExec.Event d)} (hH : OAExec.ValidHistory d P.seed H)
    {p : Point n m} (hp : p ∈ d.original) (hk : keep P H p) :
    embed d.f (family d delta P H) p ∈ warmMaster d delta P H := by
  apply embed_of_hard_epigraph (keep := keep P H) _ hk
  exact source_epigraph_contains_on_domain d.model d.f (family d delta P H)
    (familyDf d delta P H) d.domain h.analytic.convex_g h.analytic.convex_f
    (family_origins_domain h hP hH)
    (fun i j _ => h.analytic.derivative_g _ (family_origins_domain h hP hH i) j)
    (fun i => h.analytic.derivative_f _ (family_origins_domain h hP hH i))
    h.analytic.original_domain hp

theorem improving_embed_mem {d : OAExec.Data n m l r}
    (h : OAExec.AvailabilityAssumptions d) {delta : ℝ} (hd : 0 ≤ delta)
    {P : FP.State n m} (hP : FP.Invariant (PumpOA.asFPDelta d delta) P)
    {s : OAExec.State d} (hs : PumpOA.Invariant d P s)
    {p : Point n m} (hp : p ∈ d.original) (hi : PumpOA.Improves d s p) :
    embed d.f (family d delta P s.history) p ∈ warmMaster d delta P s.history := by
  have hm := PumpOA.improving_mem h hd hP hs hp hi
  exact original_embed_mem h hP hs.history hp ⟨hm.1.2.1,hm.1.2.2,hm.2.2⟩

def eventHistory {d : OAExec.Data n m l r}
    (h : OAExec.AvailabilityAssumptions d) {delta : ℝ} {P : FP.State n m}
    (hP : FP.Invariant (PumpOA.asFPDelta d delta) P)
    {H : List (OAExec.Event d)} (hH : OAExec.ValidHistory d P.seed H) (i : Fin H.length) :
    History d.model d.f d.nonlinear (family d delta P H) (familyDf d delta P H)
      (H.get i).x (intCast (H.get i).target) where
  seed := Fin.castAdd H.length (seedIndex d delta P)
  current := Fin.natAdd (prefixCount d delta P) i
  distinct := by
    intro he
    have hv := congrArg Fin.val he
    simp [seedIndex] at hv
    have := prefixCount_pos d delta P
    omega
  initial_all := by simp
  current_origin := by simp [OAExec.Event.anchor]
  current_selected := by simp [OAExec.Event.anchor,OAExec.Data.selected]
  affine := d.affine_of_not_nonlinear
  g_derivative i j := h.analytic.derivative_g _ (family_origins_domain h hP hH i) j
  f_derivative i := h.analytic.derivative_f _ (family_origins_domain h hP hH i)

end Chapter03.PumpSoft
