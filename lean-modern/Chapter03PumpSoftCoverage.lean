module

public import Chapter03PumpSoftGeometry

@[expose] public section

noncomputable section
open Chapter02 Chapter03.OAKKT Chapter03.OAExec Chapter03.OASoftMaster
open Chapter03.OASoftMaster.StoredPolicy
namespace Chapter03.PumpSoft
variable {n m l r : ℕ}

theorem transport_global_coverage {d : OAExec.Data n m l r} {delta : ℝ}
    {P : FP.State n m} {H : List (OAExec.Event d)}
    (W : Occurrence (prefixFamily d delta P) → ℝ) (Q : Policy d H)
    (hs : SeedAgreement d delta P W Q)
    {x : RealVector n} {y : RealVector m} (K : FixedKKT d.model d.f x y)
    (S : Finset (Fin l)) (occ : S → Occurrence (OAExec.family d P.seed H))
    (hc : GlobalSupportedCoverage K (OAExec.family d P.seed H) (Q.weight P.seed) S occ) :
    GlobalSupportedCoverage K (family d delta P H) (weight d delta P W Q) S
      (fun j => suffixOccurrence d delta P H (occ j)) := by
  refine ⟨(suffixOccurrence_injective d delta P H).comp hc.1,?_,?_,hc.2.2.2⟩
  · intro j q
    simpa [suffixOccurrence,suffix_origin,suffix_derivative] using hc.2.1 j q
  · intro j
    rw [weight_suffix d delta P W Q hs]
    exact hc.2.2.1 j

theorem warm_success_cost_bddBelow {d : OAExec.Data n m l r}
    (h : OAExec.AvailabilityAssumptions d) {delta : ℝ} {P : FP.State n m}
    (hP : FP.Invariant (PumpOA.asFPDelta d delta) P)
    {H : List (OAExec.Event d)} (hH : OAExec.ValidHistory d P.seed H)
    (W : Occurrence (prefixFamily d delta P) → ℝ) (hW : ∀o,0≤W o)
    (Q : Policy d H) (hs : SeedAgreement d delta P W Q)
    (i : Fin H.length) (hn : (H.get i).restoration = none) :
    BddBelow (cost (weight d delta P W Q) '' warmMaster d delta P H) := by
  let K := (Q.generation i).certificate hn
  have hc := transport_global_coverage W Q hs K _ _
    (Q.event_global_coverage h.analytic P.seed hH.1 i hn)
  let value : IntVector m → ℝ := fun y =>
    d.f (H.get i).anchor + OAExec.fullKKTFunctional K (0,intCast y-intCast (H.get i).target)
  obtain ⟨b,hb⟩ := ((integerBox_finite d.model.lo d.model.hi).image value).bddBelow
  refine ⟨b,?_⟩
  rintro v ⟨q,hq,rfl⟩
  obtain ⟨y,hy,hqy⟩ := hq.2.1
  have hlo : b ≤ value y := hb ⟨y,hy,rfl⟩
  have hhi := globally_supported_kkt_cost_lower (eventHistory h hP hH i) K hc
    (weight_nonneg d delta P W hW Q) hq
  rw [hqy] at hhi
  exact hlo.trans hhi

theorem warm_revisit_alpha {d : OAExec.Data n m l r}
    (h : OAExec.AvailabilityAssumptions d) {delta : ℝ} {P : FP.State n m}
    (hP : FP.Invariant (PumpOA.asFPDelta d delta) P)
    {H : List (OAExec.Event d)} (hH : OAExec.ValidHistory d P.seed H)
    (W : Occurrence (prefixFamily d delta P) → ℝ) (hW : ∀o,0≤W o)
    (Q : Policy d H) (hs : SeedAgreement d delta P W Q)
    (i : Fin H.length) (hn : (H.get i).restoration = none)
    (z : Candidate (family d delta P H))
    (hm : IsMinimizer (warmMaster d delta P H) (cost (weight d delta P W Q)) z)
    (hy : z.1.2 = intCast (H.get i).target) :
    z.2.1 = d.f (H.get i).anchor := by
  let K := (Q.generation i).certificate hn
  have hc := transport_global_coverage W Q hs K _ _
    (Q.event_global_coverage h.analytic P.seed hH.1 i hn)
  have hp := OAExec.event_feasible (hH.2 _ (List.get_mem H i)) hn
  have hk : keep P H (H.get i).anchor :=
    (keep_same_y P H z.1 (H.get i).anchor hy).mp hm.1.2.2.1
  have hem := original_embed_mem h hP hH hp hk
  have hub := hm.2 _ hem
  rw [cost_embed] at hub
  have hlo := supported_weighted_kkt_comparison (eventHistory h hP hH i) K
    (hc.to_local hp.2) (weight_nonneg d delta P W hW Q) hm.1 hy
  have hnonneg := penalty_nonneg (weight_nonneg d delta P W hW Q) hm.1
  have hzero : penalty (weight d delta P W Q) z = 0 := by
    change z.2.1 + penalty (weight d delta P W Q) z ≤ d.f (H.get i).anchor at hub
    linarith! only [hub,hlo,hnonneg]
  simp only [cost,hzero,add_zero] at hub
  rw [hzero,zero_div,add_zero] at hlo
  exact le_antisymm hub hlo

end Chapter03.PumpSoft
