module

public import Chapter02DICOPTKKT
public import Chapter02ESH

@[expose] public section

noncomputable section
open scoped BigOperators
namespace Chapter02.DICOPT
variable {n m e l r : ℕ} (d : Data n m e l r)

/-- Literal zero-slack embedding; alpha is f(x), not an invented bounded height. -/
def masterEmbed (H : List (Anchor d)) (x : RealVector n) (y : RealVector m) : MasterPoint d H :=
  ⟨x,y,d.f x,fun _ => 0,fun _ _ => 0,fun _ _ => 0⟩

theorem master_embed (H : List (Anchor d)) (R : Finset (BVector m))
    {x : RealVector n} {y : RealVector m} (hx : d.Feasible x y) (hy : Binary y)
    (hR : ∀ b ∈ R,noGoodRow b y ≤ 0) : masterEmbed d H x y ∈ masterFeasible d H R := by
  refine ⟨⟨hx.1,hy,hR⟩,fun _ => le_rfl,fun _ _ => le_rfl,fun _ _ => le_rfl,?_,?_,?_⟩
  · intro k
    exact sub_nonpos.mpr (source_tangents (H.get k).kkt (H.get k).convex hx).1
  · intro k i
    exact (source_tangents (H.get k).kkt (H.get k).convex hx).2.1 i
  · intro k i
    exact (source_tangents (H.get k).kkt (H.get k).convex hx).2.2 i

@[simp] theorem master_embed_objective (H : List (Anchor d)) (x : RealVector n)
    (y : RealVector m) : masterObjective d H (masterEmbed d H x y) = d.objective x y := by
  simp [masterObjective,masterEmbed,Data.objective]

theorem master_remaining_bound (H : List (Anchor d)) (R : Finset (BVector m))
    {v : ℝ} (hv : IsLowerBound (masterFeasible d H R) (masterObjective d H) v)
    {x : RealVector n} {y : RealVector m} (hx : d.Feasible x y) (hy : Binary y)
    (hR : ∀ b ∈ R,noGoodRow b y ≤ 0) : v ≤ d.objective x y := by
  simpa using hv (masterEmbed d H x y) (master_embed d H R hx hy hR)

variable {d}

theorem history_index_nonempty (H : List (Anchor d)) (hne : H ≠ []) : Nonempty (Fin H.length) :=
  ⟨⟨0,List.length_pos_iff.mpr hne⟩⟩

def historyMax (H : List (Anchor d)) (hne : H ≠ []) (x : RealVector n) : ℝ :=
  @eshMaximum (RealVector n) (Fin H.length) _ (history_index_nonempty H hne)
    (fun k => objTangent d (H.get k).kkt.jet) x

theorem historyMax_le_iff (H : List (Anchor d)) (hne : H ≠ []) (x : RealVector n) (v : ℝ) :
    historyMax H hne x ≤ v ↔ ∀ k,objTangent d (H.get k).kkt.jet x ≤ v := by
  letI := history_index_nonempty H hne
  exact eshMaximum_le_iff _ x v

theorem historyMax_attained (H : List (Anchor d)) (hne : H ≠ []) (x : RealVector n) :
    ∃ k, historyMax H hne x = objTangent d (H.get k).kkt.jet x := by
  letI := history_index_nonempty H hne
  exact eshMaximum_attained _ x

theorem objTangent_continuous {x0 : RealVector n} (j : Jet d x0) :
    Continuous (objTangent d j) := by
  unfold objTangent
  fun_prop

theorem eqTangent_continuous {x0 : RealVector n} (j : Jet d x0) (lam : RealVector e)
    (i : Fin e) : Continuous (fun z : RealVector n × RealVector m => eqTangent d j lam i z.1 z.2) := by
  unfold eqTangent dot
  fun_prop

theorem ineqTangent_continuous {x0 : RealVector n} (j : Jet d x0) (i : Fin l) :
    Continuous (fun z : RealVector n × RealVector m => ineqTangent d j i z.1 z.2) := by
  unfold ineqTangent dot
  fun_prop

theorem historyMax_continuous (H : List (Anchor d)) (hne : H ≠ []) :
    Continuous (historyMax H hne) := by
  letI := history_index_nonempty H hne
  exact eshMaximum_continuous fun k => objTangent_continuous (H.get k).kkt.jet

def reducedObjective (H : List (Anchor d)) (hne : H ≠ [])
    (z : RealVector n × RealVector m) : ℝ :=
  dot d.c z.2 + historyMax H hne z.1 +
    (∑ k,∑ i,(H.get k).weights.eq i * max (eqTangent d (H.get k).kkt.jet (H.get k).kkt.lambda i z.1 z.2) 0) +
    (∑ k,∑ i,(H.get k).weights.ineq i * max (ineqTangent d (H.get k).kkt.jet i z.1 z.2) 0)

def reducedLift (H : List (Anchor d)) (hne : H ≠ [])
    (z : RealVector n × RealVector m) : MasterPoint d H where
  x := z.1
  y := z.2
  alpha := historyMax H hne z.1
  s := fun _ => 0
  p := fun k i => max (eqTangent d (H.get k).kkt.jet (H.get k).kkt.lambda i z.1 z.2) 0
  q := fun k i => max (ineqTangent d (H.get k).kkt.jet i z.1 z.2) 0

theorem reducedLift_feasible (H : List (Anchor d)) (hne : H ≠ []) (R : Finset (BVector m))
    {z : RealVector n × RealVector m} (hz : z ∈ hardDomain d R) :
    reducedLift H hne z ∈ masterFeasible d H R := by
  refine ⟨hz,fun _ => le_rfl,fun _ _ => le_max_right _ _,fun _ _ => le_max_right _ _,?_,?_,?_⟩
  · intro k
    exact sub_nonpos.mpr ((historyMax_le_iff H hne z.1 _).mp le_rfl k)
  · intro k i
    exact le_max_left _ _
  · intro k i
    exact le_max_left _ _

@[simp] theorem reducedLift_objective (H : List (Anchor d)) (hne : H ≠ [])
    (z : RealVector n × RealVector m) :
    masterObjective d H (reducedLift H hne z) = reducedObjective H hne z := by
  simp [masterObjective,reducedLift,reducedObjective]

theorem reducedObjective_le (H : List (Anchor d)) (hne : H ≠ []) (R : Finset (BVector m))
    {z : MasterPoint d H} (hz : z ∈ masterFeasible d H R) :
    reducedObjective H hne (z.x,z.y) ≤ masterObjective d H z := by
  have hws : ∀ k,0 ≤ (H.get k).weights.obj*z.s k := by
    intro k
    have hw : 1 < (H.get k).weights.obj := by simpa using (H.get k).weights.obj_gt
    exact mul_nonneg (by linarith) (hz.2.1 k)
  obtain ⟨j,hj⟩ := historyMax_attained H hne z.x
  have hwo : 1 < (H.get j).weights.obj := by simpa using (H.get j).weights.obj_gt
  have hsingle := Finset.single_le_sum (fun k (_ : k ∈ Finset.univ) => hws k) (Finset.mem_univ j)
  have hs := hz.2.1 j
  have hcut := hz.2.2.2.2.1 j
  have hmax : historyMax H hne z.x ≤ z.alpha + ∑ k,(H.get k).weights.obj*z.s k := by
    rw [hj]
    nlinarith
  have hp : (∑ k,∑ i,(H.get k).weights.eq i * max (eqTangent d (H.get k).kkt.jet (H.get k).kkt.lambda i z.x z.y) 0) ≤
      ∑ k,∑ i,(H.get k).weights.eq i*z.p k i := by
    apply Finset.sum_le_sum
    intro k _
    apply Finset.sum_le_sum
    intro i _
    apply mul_le_mul_of_nonneg_left
    · exact max_le (hz.2.2.2.2.2.1 k i) (hz.2.2.1 k i)
    · exact (abs_nonneg _).trans ((H.get k).weights.eq_gt i).le
  have hq : (∑ k,∑ i,(H.get k).weights.ineq i * max (ineqTangent d (H.get k).kkt.jet i z.x z.y) 0) ≤
      ∑ k,∑ i,(H.get k).weights.ineq i*z.q k i := by
    apply Finset.sum_le_sum
    intro k _
    apply Finset.sum_le_sum
    intro i _
    apply mul_le_mul_of_nonneg_left
    · exact max_le (hz.2.2.2.2.2.2 k i) (hz.2.2.2.1 k i)
    · exact (abs_nonneg _).trans ((H.get k).weights.ineq_gt i).le
  dsimp [reducedObjective,masterObjective]
  simp only [List.get_eq_getElem] at hp hq hmax
  linarith

theorem reducedObjective_continuous (H : List (Anchor d)) (hne : H ≠ []) :
    Continuous (reducedObjective H hne) := by
  unfold reducedObjective
  apply Continuous.add
  · apply Continuous.add
    · exact (by unfold dot; fun_prop : Continuous (fun z : RealVector n × RealVector m => dot d.c z.2)).add
        ((historyMax_continuous H hne).comp continuous_fst)
    · apply continuous_finset_sum
      intro k _
      apply continuous_finset_sum
      intro i _
      exact continuous_const.mul ((eqTangent_continuous (H.get k).kkt.jet (H.get k).kkt.lambda i).max continuous_const)
  · apply continuous_finset_sum
    intro k _
    apply continuous_finset_sum
    intro i _
    exact continuous_const.mul ((ineqTangent_continuous (H.get k).kkt.jet i).max continuous_const)

theorem hardDomain_compact (R : Finset (BVector m)) : IsCompact (hardDomain d R) := by
  have ha : ∀ i, Continuous (fun z : RealVector n × RealVector m => d.affineRow i z.1 z.2) := by
    intro i
    unfold Data.affineRow dot
    fun_prop
  have hn : ∀ b, Continuous (fun z : RealVector n × RealVector m => noGoodRow b z.2) := by
    intro b
    unfold noGoodRow
    apply Continuous.sub
    · apply Continuous.sub
      · apply continuous_finset_sum
        intro i _
        split_ifs <;> fun_prop
      · apply continuous_finset_sum
        intro i _
        split_ifs <;> fun_prop
    · exact continuous_const
  have hclosed : IsClosed (hardDomain d R) := by
    unfold hardDomain Data.Hard Binary
    simp only [Set.setOf_and,Set.setOf_forall]
    exact ((isClosed_Icc.preimage continuous_fst).inter
      (isClosed_iInter fun i => isClosed_le (ha i) continuous_const)).inter
      ((isClosed_iInter fun i =>
        (isClosed_eq ((continuous_apply i).comp continuous_snd) continuous_const).union
        (isClosed_eq ((continuous_apply i).comp continuous_snd) continuous_const)).inter
        (isClosed_iInter fun b => isClosed_iInter fun _ => isClosed_le (hn b) continuous_const))
  apply (isCompact_Icc.prod (isCompact_Icc : IsCompact (Set.Icc (0 : RealVector m) 1))).of_isClosed_subset hclosed
  intro z hz
  refine ⟨hz.1.1,?_,?_⟩
  · intro i
    rcases hz.2.1 i with h|h <;> simp [h]
  · intro i
    rcases hz.2.1 i with h|h <;> simp [h]

/-- Attained actual unrestricted-epigraph master, derived from compact reduction. -/
theorem master_attained (H : List (Anchor d)) (hne : H ≠ []) (R : Finset (BVector m))
    (hR : (hardDomain d R).Nonempty) :
    ∃ z,IsMinimizer (masterFeasible d H R) (masterObjective d H) z := by
  obtain ⟨z,hz,hmin⟩ := compact_feasible_attainment (hardDomain_compact R) hR
    (reducedObjective_continuous H hne).continuousOn
  refine ⟨reducedLift H hne z,reducedLift_feasible H hne R hz,?_⟩
  intro w hw
  rw [reducedLift_objective]
  exact (hmin (w.x,w.y) hw.1).trans (reducedObjective_le H hne R hw)

theorem master_empty_of_hard_empty (H : List (Anchor d)) (R : Finset (BVector m))
    (hR : hardDomain d R = ∅) : masterFeasible d H R = ∅ := by
  apply Set.eq_empty_iff_forall_notMem.mpr
  intro z hz
  have h := hz.1
  rw [hR] at h
  exact h

/-- Qualified source sufficiency, all-index history embedding, and actual master attainment.
No uniform AP-to-hard exactness or heuristic stopping claim is included. -/
theorem source_convex_master_guarantees (H : List (Anchor d)) (hne : H ≠ [])
    (R : Finset (BVector m)) :
    (∀ (x : RealVector n) (y : RealVector m) (k : FixedKKT d x y), SignedConvex d k →
      IsMinimizer (d.fiber y) (fun v => d.objective v y) x) ∧
    (∀ (x : RealVector n) (y : RealVector m) (k : JointKKT d x y), SignedConvex d k.toFixedKKT →
      IsMinimizer d.relaxed (fun z => d.objective z.1 z.2) (x,y)) ∧
    (∀ (x : RealVector n) (y : RealVector m), d.Feasible x y → Binary y →
      (∀ b ∈ R,noGoodRow b y ≤ 0) → masterEmbed d H x y ∈ masterFeasible d H R ∧
        masterObjective d H (masterEmbed d H x y)=d.objective x y) ∧
    ((hardDomain d R).Nonempty → ∃ z,IsMinimizer (masterFeasible d H R) (masterObjective d H) z) ∧
    (hardDomain d R=∅ → masterFeasible d H R=∅) :=
  ⟨fun _ _ k hc => k.global_min hc,fun _ _ k hc => k.global_min hc,
    fun x y hx hy hR => ⟨master_embed d H R hx hy hR,master_embed_objective d H x y⟩,
    master_attained H hne R,master_empty_of_hard_empty H R⟩

end Chapter02.DICOPT
#print axioms Chapter02.DICOPT.source_convex_master_guarantees
