module

public import Chapter03PumpOAModel

@[expose] public section

/-! Exact finite weak-affine rows for the retained pump handoff intersected
with the new hard OA master. The prefix is arbitrary finite data: no pump
correctness, convexity, attainment or progress assumption occurs here. -/
noncomputable section
open scoped BigOperators RealInnerProductSpace
open Chapter02 Chapter03.OAKKT
namespace Chapter03.PumpOA
variable {n m l r : ℕ}

abbrev PumpIndex (d : OAExec.Data n m l r) (delta : ℝ) (P : FP.State n m) :=
  Fin (FP.anchors (asFPDelta d delta) P).length

def pumpOrigin (d : OAExec.Data n m l r) (delta : ℝ) (P : FP.State n m)
    (i : PumpIndex d delta P) : Point n m :=
  ((FP.anchors (asFPDelta d delta) P).get i).point

abbrev PumpSelected (d : OAExec.Data n m l r) (delta : ℝ) (P : FP.State n m) :=
  {ij : PumpIndex d delta P × Fin l //
    ij.2 ∈ (FP.family (asFPDelta d delta) P).selected ij.1}

/-- Exactly the failed projection rows strictly before the last success;
with no success, every failed projection row remains. -/
abbrev RetainedNormalIndex (P : FP.State n m) :=
  {i : Fin P.history.length // (P.history.get i).success = none ∧
    ∀ k, P.lastSuccess = some k → i.val < k}

def normalLinear (e : FP.Event n m) : Point n m →L[ℝ] ℝ :=
  (innerSL ℝ (yMap n m e.projection - FP.intY e.target)).comp
    (LinearMap.toContinuousLinearMap (yMap n m))

theorem normalLinear_apply (e : FP.Event n m) (p : Point n m) :
    normalLinear e p = inner ℝ (yMap n m e.projection - FP.intY e.target) (yMap n m p) := rfl

theorem normalLinear_sub (e : FP.Event n m) (p : Point n m) :
    normalLinear e p - normalLinear e e.projection = e.normal p := by
  simp only [normalLinear_apply, FP.Event.normal, inner_sub_right]

abbrev MasterRowIndex (d : OAExec.Data n m l r) (delta : ℝ) (P : FP.State n m)
    (H : List (OAExec.Event d)) :=
  OAExec.MasterRowIndex d P.seed H ⊕
    ((PumpIndex d delta P ⊕ PumpSelected d delta P) ⊕ RetainedNormalIndex P)

def masterRow (d : OAExec.Data n m l r) (delta : ℝ) (P : FP.State n m)
    (H : List (OAExec.Event d)) :
    MasterRowIndex d delta P H → (Point n m × ℝ) →L[ℝ] ℝ :=
  Sum.elim (OAExec.masterRow d P.seed H)
    (Sum.elim (Sum.elim
      (fun i => (d.Df (pumpOrigin d delta P i)).comp
        (ContinuousLinearMap.fst ℝ (Point n m) ℝ) -
        ContinuousLinearMap.snd ℝ (Point n m) ℝ)
      (fun ij => (d.Dg (pumpOrigin d delta P ij.val.1) ij.val.2).comp
        (ContinuousLinearMap.fst ℝ (Point n m) ℝ)))
      (fun i => -(normalLinear (P.history.get i.val)).comp
        (ContinuousLinearMap.fst ℝ (Point n m) ℝ)))

def masterRowBound (d : OAExec.Data n m l r) (delta : ℝ) (P : FP.State n m)
    (H : List (OAExec.Event d)) : MasterRowIndex d delta P H → ℝ :=
  Sum.elim (OAExec.masterRowBound d P.seed H)
    (Sum.elim (Sum.elim
      (fun i => d.Df (pumpOrigin d delta P i) (pumpOrigin d delta P i) -
        d.f (pumpOrigin d delta P i))
      (fun ij => d.Dg (pumpOrigin d delta P ij.val.1) ij.val.2
        (pumpOrigin d delta P ij.val.1) -
        d.model.g ij.val.2 (pumpOrigin d delta P ij.val.1)))
      (fun i => -normalLinear (P.history.get i.val) (P.history.get i.val).projection))

/-- Both exclusion families act on whole integer assignments. Successful
pump fibers may be feasible; new OA exclusions certify empty fibers elsewhere. -/
def noGoods {d : OAExec.Data n m l r} (P : FP.State n m)
    (H : List (OAExec.Event d)) (p : Point n m) : Prop :=
  FP.noGoods P p ∧ OAExec.noGoods H p

/-- Both directions retain every pump tangent, exactly the filtered normal
rows, all new OA rows, hard rows, integer bounds and both no-good families. -/
theorem master_rows_iff (d : OAExec.Data n m l r) (delta : ℝ) (P : FP.State n m)
    (H : List (OAExec.Event d)) (z : Point n m × ℝ) :
    z ∈ master d delta P H ↔
      (∀ i, masterRow d delta P H i z ≤ masterRowBound d delta P H i) ∧
      z.1 ∈ IntegerCylinder (n := n) d.model.lo d.model.hi ∧ noGoods P H z.1 := by
  constructor
  · rintro ⟨hp,ho⟩
    obtain ⟨hr,hy,hn⟩ := (OAExec.master_rows_iff d P.seed H z).mp ho
    refine ⟨?_,hy,hp.2.2,hn⟩
    intro i
    rcases i with i | ((i | ij) | i)
    · exact hr i
    · have hh := hp.1.2 i
      change d.f (pumpOrigin d delta P i) +
        d.Df (pumpOrigin d delta P i) (z.1-pumpOrigin d delta P i) ≤ z.2 at hh
      change d.Df (pumpOrigin d delta P i) z.1-z.2 ≤
        d.Df (pumpOrigin d delta P i) (pumpOrigin d delta P i)-
          d.f (pumpOrigin d delta P i)
      rw [map_sub] at hh
      linarith
    · have hh := hp.1.1.1.1.2 ij.val.1 ij.val.2 ij.property
      change d.model.g ij.val.2 (pumpOrigin d delta P ij.val.1) +
        d.Dg (pumpOrigin d delta P ij.val.1) ij.val.2
          (z.1-pumpOrigin d delta P ij.val.1) ≤ 0 at hh
      change d.Dg (pumpOrigin d delta P ij.val.1) ij.val.2 z.1 ≤
        d.Dg (pumpOrigin d delta P ij.val.1) ij.val.2 (pumpOrigin d delta P ij.val.1)-
          d.model.g ij.val.2 (pumpOrigin d delta P ij.val.1)
      rw [map_sub] at hh
      linarith
    · have hh := hp.2.1 i.val i.property.1 i.property.2
      change -normalLinear (P.history.get i.val) z.1 ≤
        -normalLinear (P.history.get i.val) (P.history.get i.val).projection
      rw [← normalLinear_sub] at hh
      linarith
  · rintro ⟨hr,hy,hn⟩
    have ho : z ∈ OAExec.master d P.seed H :=
      (OAExec.master_rows_iff d P.seed H z).mpr
        ⟨fun i => hr (Sum.inl i),hy,hn.2⟩
    refine ⟨⟨?_,?_,hn.1⟩,ho⟩
    · refine ⟨⟨⟨⟨Set.mem_univ _,?_⟩,ho.1.1.1.2⟩,hy⟩,?_⟩
      · intro i j hj
        have hh := hr (Sum.inr (Sum.inl (Sum.inr ⟨(i,j),hj⟩)))
        change d.Dg (pumpOrigin d delta P i) j z.1 ≤
          d.Dg (pumpOrigin d delta P i) j (pumpOrigin d delta P i)-
            d.model.g j (pumpOrigin d delta P i) at hh
        change d.model.g j (pumpOrigin d delta P i) +
          d.Dg (pumpOrigin d delta P i) j (z.1-pumpOrigin d delta P i) ≤ 0
        rw [map_sub]
        linarith
      · intro i
        have hh := hr (Sum.inr (Sum.inl (Sum.inl i)))
        change d.Df (pumpOrigin d delta P i) z.1-z.2 ≤
          d.Df (pumpOrigin d delta P i) (pumpOrigin d delta P i)-
            d.f (pumpOrigin d delta P i) at hh
        change d.f (pumpOrigin d delta P i) +
          d.Df (pumpOrigin d delta P i) (z.1-pumpOrigin d delta P i) ≤ z.2
        rw [map_sub]
        linarith
    · intro i hi hk
      have hh := hr (Sum.inr (Sum.inr ⟨i,hi,hk⟩))
      change -normalLinear (P.history.get i) z.1 ≤
        -normalLinear (P.history.get i) (P.history.get i).projection at hh
      rw [← normalLinear_sub]
      linarith

end Chapter03.PumpOA

#print axioms Chapter03.PumpOA.normalLinear_sub
#print axioms Chapter03.PumpOA.master_rows_iff
