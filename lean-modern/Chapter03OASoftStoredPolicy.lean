module

public import Chapter03OASoftAvailability

@[expose] public section

/-! A concrete stored generation-certificate policy on chronological OA histories.
The same chosen certificate is retained; future coverage is a theorem, not a
policy field. Hard affine entailment remains a separate source qualification. -/
noncomputable section
open scoped BigOperators
open Chapter02 Chapter03.OAKKT
namespace Chapter03.OASoftMaster.StoredPolicy
variable {n m l r : ℕ} {d : OAExec.Data n m l r}

/-- Generation data contains an actual chosen certificate for a successful solve.
The certificate need not be the existential witness inside EventValid. -/
structure Generation (d : OAExec.Data n m l r) (e : OAExec.Event d) where
  valid : OAExec.EventValid d e
  certificate : e.restoration = none → FixedKKT d.model d.f e.x (intCast e.target)
  hard : ∀ hn j, j ∉ d.nonlinear → (certificate hn).lambda j ≠ 0 →
    ∀ q ∈ d.model.linearRegion,
      q ∈ IntegerCylinder (n := n) d.model.lo d.model.hi →
      d.model.g j e.anchor + (certificate hn).Dg j (q-e.anchor) ≤ 0

/-- Exactly1000 times the supplied generation multiplier; restoration weights0.
This is an explicit sufficient policy, not a software-marginal identification. -/
def Generation.rowWeight {e : OAExec.Event d} (G : Generation d e) (j : Fin l) : ℝ := by
  classical
  exact if hn : e.restoration = none then 1000 * (G.certificate hn).lambda j else 0

theorem Generation.rowWeight_nonneg {e : OAExec.Event d} (G : Generation d e)
    (j : Fin l) : 0 ≤ G.rowWeight j := by
  classical
  unfold Generation.rowWeight
  split
  · exact mul_nonneg (by norm_num) ((G.certificate _).lambda_nonneg j)
  · exact le_rfl

@[simp] theorem Generation.rowWeight_success {e : OAExec.Event d}
    (G : Generation d e) (hn : e.restoration = none) (j : Fin l) :
    G.rowWeight j = 1000 * (G.certificate hn).lambda j := by
  classical
  simp [Generation.rowWeight,hn]

def Generation.transport {e e' : OAExec.Event d} (h : e = e')
    (G : Generation d e) : Generation d e' := h ▸ G

@[simp] theorem Generation.transport_weight {e e' : OAExec.Event d}
    (h : e = e') (G : Generation d e) (j : Fin l) :
    (G.transport h).rowWeight j = G.rowWeight j := by cases h; rfl

/-- Distinct chronological entries retain distinct generation data even when
anchors or target values repeat. No coverage or objective comparison is a field. -/
structure Policy (d : OAExec.Data n m l r) (H : List (OAExec.Event d)) where
  seedWeight : Fin l → ℝ
  seed_nonneg : ∀ j, 0 ≤ seedWeight j
  generation : (i : Fin H.length) → Generation d (H.get i)

def Policy.slotWeight {H : List (OAExec.Event d)} (P : Policy d H) :
    Fin (H.length+1) → Fin l → ℝ :=
  Fin.cases P.seedWeight (fun i => (P.generation i).rowWeight)

def Policy.weight {H : List (OAExec.Event d)} (P : Policy d H) (seed : Point n m)
    (o : Occurrence (OAExec.family d seed H)) : ℝ := P.slotWeight o.1.1 o.1.2

theorem Policy.weight_nonneg {H : List (OAExec.Event d)} (P : Policy d H)
    (seed : Point n m) (o : Occurrence (OAExec.family d seed H)) :
    0 ≤ P.weight seed o := by
  change 0 ≤ P.slotWeight o.1.1 o.1.2
  generalize o.1.1 = i
  refine Fin.cases (P.seed_nonneg _) (fun a => (P.generation a).rowWeight_nonneg _) i

theorem Policy.validHistory {H : List (OAExec.Event d)} (P : Policy d H)
    {seed : Point n m} (hs : seed ∈ d.domain) : OAExec.ValidHistory d seed H := by
  refine ⟨hs,?_⟩
  intro e he
  obtain ⟨i,rfl⟩ := List.mem_iff_get.mp he
  exact (P.generation i).valid

/-- Old chronological index, with its numerical value unchanged. -/
def oldIndex (H : List (OAExec.Event d)) (e : OAExec.Event d)
    (i : Fin H.length) : Fin (H++[e]).length := ⟨i.val,by simp⟩

def newIndex (H : List (OAExec.Event d)) (e : OAExec.Event d) :
    Fin (H++[e]).length := ⟨H.length,by simp⟩

@[simp] theorem get_oldIndex (H : List (OAExec.Event d)) (e : OAExec.Event d)
    (i : Fin H.length) : (H++[e]).get (oldIndex H e i) = H.get i := by
  simp only [List.get_eq_getElem,oldIndex]
  exact List.getElem_append_left i.isLt

@[simp] theorem get_newIndex (H : List (OAExec.Event d)) (e : OAExec.Event d) :
    (H++[e]).get (newIndex H e) = e := by
  simp [newIndex,List.getElem_append_right]

/-- Every old seed/event slot embeds into the extended chronological family. -/
def slotInjection (H : List (OAExec.Event d)) (e : OAExec.Event d) :
    Fin (H.length+1) → Fin ((H++[e]).length+1) :=
  Fin.cases 0 (fun i => (oldIndex H e i).succ)

theorem slotInjection_injective (H : List (OAExec.Event d)) (e : OAExec.Event d) :
    Function.Injective (slotInjection H e) := by
  intro i j h
  apply Fin.ext
  have hv := congrArg Fin.val h
  have val_eq (a : Fin (H.length+1)) : (slotInjection H e a).val = a.val := by
    refine Fin.cases rfl (fun _ => rfl) a
  simpa only [val_eq] using hv

@[simp] theorem append_origin (seed : Point n m) (H : List (OAExec.Event d))
    (e : OAExec.Event d) (i : Fin (H.length+1)) :
    (OAExec.family d seed (H++[e])).origin (slotInjection H e i) =
      (OAExec.family d seed H).origin i := by
  refine Fin.cases rfl ?_ i
  intro a
  change ((H++[e]).get (oldIndex H e a)).anchor = (H.get a).anchor
  rw [get_oldIndex]

@[simp] theorem append_selected (seed : Point n m) (H : List (OAExec.Event d))
    (e : OAExec.Event d) (i : Fin (H.length+1)) :
    (OAExec.family d seed (H++[e])).selected (slotInjection H e i) =
      (OAExec.family d seed H).selected i := by
  refine Fin.cases rfl ?_ i
  intro a
  change d.selected ((H++[e]).get (oldIndex H e a)).anchor = d.selected (H.get a).anchor
  rw [get_oldIndex]

@[simp] theorem append_derivative (seed : Point n m) (H : List (OAExec.Event d))
    (e : OAExec.Event d) (i : Fin (H.length+1)) (j : Fin l) :
    (OAExec.family d seed (H++[e])).derivative (slotInjection H e i) j =
      (OAExec.family d seed H).derivative i j := by
  change d.Dg ((OAExec.family d seed (H++[e])).origin (slotInjection H e i)) j = _
  rw [append_origin]
  rfl

@[simp] theorem append_objective_derivative (seed : Point n m) (H : List (OAExec.Event d))
    (e : OAExec.Event d) (i : Fin (H.length+1)) :
    OAExec.familyDf d seed (H++[e]) (slotInjection H e i) = OAExec.familyDf d seed H i := by
  unfold OAExec.familyDf
  rw [append_origin]

def occurrenceInjection (seed : Point n m) (H : List (OAExec.Event d))
    (e : OAExec.Event d) (o : Occurrence (OAExec.family d seed H)) :
    Occurrence (OAExec.family d seed (H++[e])) :=
  ⟨(slotInjection H e o.1.1,o.1.2),by rw [append_selected]; exact o.2⟩

theorem occurrenceInjection_injective (seed : Point n m) (H : List (OAExec.Event d))
    (e : OAExec.Event d) : Function.Injective (occurrenceInjection seed H e) := by
  intro u v h
  apply Subtype.ext
  apply Prod.ext
  · apply slotInjection_injective H e
    exact congrArg (fun a => a.1.1) h
  · exact congrArg (fun a => a.1.2) h

/-- Actual append implementation: old entries are transported, never recertified. -/
def Policy.append {H : List (OAExec.Event d)} (P : Policy d H)
    (e : OAExec.Event d) (G : Generation d e) : Policy d (H++[e]) where
  seedWeight := P.seedWeight
  seed_nonneg := P.seed_nonneg
  generation i := if h : i.val < H.length then
    (P.generation ⟨i.val,h⟩).transport (by
      simpa [oldIndex] using (get_oldIndex H e ⟨i.val,h⟩).symm)
    else G.transport (by
      have hi : i = newIndex H e := by apply Fin.ext; have := i.isLt; simp at this; simp [newIndex]; omega
      subst i
      exact (get_newIndex H e).symm)

/-- The retained generation record is the original record, with only event-index
transport. In particular the chosen certificate is not selected again. -/
theorem Policy.append_generation_old {H : List (OAExec.Event d)} (P : Policy d H)
    (e : OAExec.Event d) (G : Generation d e) (i : Fin H.length) :
    (P.append e G).generation (oldIndex H e i) =
      (P.generation i).transport (get_oldIndex H e i).symm := by
  classical
  simp [Policy.append,oldIndex,i.isLt]

theorem Policy.append_generation_new {H : List (OAExec.Event d)} (P : Policy d H)
    (e : OAExec.Event d) (G : Generation d e) :
    (P.append e G).generation (newIndex H e) = G.transport (get_newIndex H e).symm := by
  classical
  simp [Policy.append,newIndex]

@[simp] theorem Policy.append_slotWeight {H : List (OAExec.Event d)} (P : Policy d H)
    (e : OAExec.Event d) (G : Generation d e) (i : Fin (H.length+1)) (j : Fin l) :
    (P.append e G).slotWeight (slotInjection H e i) j = P.slotWeight i j := by
  refine Fin.cases rfl ?_ i
  intro a
  change ((P.append e G).generation (oldIndex H e a)).rowWeight j = (P.generation a).rowWeight j
  rw [P.append_generation_old,Generation.transport_weight]

@[simp] theorem Policy.append_weight {H : List (OAExec.Event d)} (P : Policy d H)
    (e : OAExec.Event d) (G : Generation d e) (seed : Point n m)
    (o : Occurrence (OAExec.family d seed H)) :
    (P.append e G).weight seed (occurrenceInjection seed H e o) = P.weight seed o := by
  exact P.append_slotWeight e G o.1.1 o.1.2



/-- Coverage of every retained successful event is derived from its stored chosen
certificate, literal nonlinear selection and generation-time weights. -/
theorem Policy.event_coverage {H : List (OAExec.Event d)} (P : Policy d H)
    (a : OAExec.Analytic d) (seed : Point n m) (hs : seed ∈ d.domain)
    (i : Fin H.length) (hn : (H.get i).restoration = none) :
    let K := (P.generation i).certificate hn
    SupportedCoverage K (OAExec.family d seed H) (P.weight seed)
      (nonlinearSupport K d.nonlinear)
      (currentOccurrence (OAExec.eventHistory d a seed H (P.validHistory hs) i) K) := by
  dsimp only
  apply current_occurrence_coverage
  · intro j
    change 1000 * ((P.generation i).certificate hn).lambda j ≤ (P.generation i).rowWeight j
    rw [Generation.rowWeight_success _ hn]
  · intro j hj hn' q hq hy
    exact (P.generation i).hard hn j hj hn' q hq
      ⟨(H.get i).target,(H.get i).target_mem,hy⟩

/-- Direct persistence proof for any established local coverage. It uses actual
append preservation, not a future-coverage assumption in the policy. -/
theorem Policy.coverage_append {H : List (OAExec.Event d)} (P : Policy d H)
    (e : OAExec.Event d) (G : Generation d e) (seed : Point n m)
    {x : RealVector n} {y : RealVector m} (K : FixedKKT d.model d.f x y)
    {S : Finset (Fin l)} {occ : S → Occurrence (OAExec.family d seed H)}
    (hc : SupportedCoverage K (OAExec.family d seed H) (P.weight seed) S occ) :
    SupportedCoverage K (OAExec.family d seed (H++[e])) ((P.append e G).weight seed)
      S (fun j => occurrenceInjection seed H e (occ j)) := by
  refine ⟨(occurrenceInjection_injective seed H e).comp hc.1,?_,?_,hc.2.2.2⟩
  · intro j q
    change _ = d.model.g (occ j).1.2
      ((OAExec.family d seed (H++[e])).origin (slotInjection H e (occ j).1.1)) +
      (OAExec.family d seed (H++[e])).derivative (slotInjection H e (occ j).1.1)
        (occ j).1.2 (q-(OAExec.family d seed (H++[e])).origin (slotInjection H e (occ j).1.1))
    rw [append_origin,append_derivative]
    exact hc.2.1 j q
  · intro j
    rw [P.append_weight]
    exact hc.2.2.1 j

/-- A freshly appended successful entry is covered using the exact generation
record supplied to append, whose identity is append_generation_new. -/
theorem Policy.new_event_coverage {H : List (OAExec.Event d)} (P : Policy d H)
    (e : OAExec.Event d) (G : Generation d e) (hn : e.restoration = none)
    (a : OAExec.Analytic d) (seed : Point n m) (hs : seed ∈ d.domain) :
    let i := newIndex H e
    let hn' : ((H++[e]).get i).restoration = none := by dsimp only [i]; rw [get_newIndex]; exact hn
    let K := ((P.append e G).generation i).certificate hn'
    SupportedCoverage K (OAExec.family d seed (H++[e])) ((P.append e G).weight seed)
      (nonlinearSupport K d.nonlinear)
      (currentOccurrence (OAExec.eventHistory d a seed (H++[e])
        ((P.append e G).validHistory hs) i) K) := by
  dsimp only
  exact (P.append e G).event_coverage a seed hs (newIndex H e) (by rw [get_newIndex]; exact hn)



/-- Stronger cross-fiber coverage for availability follows from the same stored
row policy and the explicit global hard entailment field. -/
theorem Policy.event_global_coverage {H : List (OAExec.Event d)} (P : Policy d H)
    (a : OAExec.Analytic d) (seed : Point n m) (hs : seed ∈ d.domain)
    (i : Fin H.length) (hn : (H.get i).restoration = none) :
    let K := (P.generation i).certificate hn
    GlobalSupportedCoverage K (OAExec.family d seed H) (P.weight seed)
      (nonlinearSupport K d.nonlinear)
      (currentOccurrence (OAExec.eventHistory d a seed H (P.validHistory hs) i) K) := by
  classical
  dsimp only
  have hc := P.event_coverage a seed hs i hn
  refine ⟨hc.1,hc.2.1,hc.2.2.1,?_⟩
  intro j hj hn' q hq hy
  apply (P.generation i).hard hn j ?_ hn' q hq hy
  intro hN
  exact hj (by simp [nonlinearSupport,hN,hn'])

/-- A transported generation carries the identical certificate. -/
theorem Generation.transport_certificate {e e' : OAExec.Event d}
    (G : Generation d e) (h : e = e') (hn : e.restoration = none) :
    HEq ((G.transport h).certificate (h ▸ hn)) (G.certificate hn) := by
  cases h
  rfl

/-- Actual selected certificate identity survives chronological append. -/
theorem Policy.append_certificate_old {H : List (OAExec.Event d)} (P : Policy d H)
    (e : OAExec.Event d) (G : Generation d e) (i : Fin H.length)
    (hn : (H.get i).restoration = none) :
    HEq (((P.append e G).generation (oldIndex H e i)).certificate
      (by rw [get_oldIndex]; exact hn)) ((P.generation i).certificate hn) := by
  rw [P.append_generation_old]
  exact (P.generation i).transport_certificate (get_oldIndex H e i).symm hn

/-- Direct persistence proof for any established global coverage. It uses actual
append preservation, not a future-coverage assumption in the policy. -/
theorem Policy.global_coverage_append {H : List (OAExec.Event d)} (P : Policy d H)
    (e : OAExec.Event d) (G : Generation d e) (seed : Point n m)
    {x : RealVector n} {y : RealVector m} (K : FixedKKT d.model d.f x y)
    {S : Finset (Fin l)} {occ : S → Occurrence (OAExec.family d seed H)}
    (hc : GlobalSupportedCoverage K (OAExec.family d seed H) (P.weight seed) S occ) :
    GlobalSupportedCoverage K (OAExec.family d seed (H++[e])) ((P.append e G).weight seed)
      S (fun j => occurrenceInjection seed H e (occ j)) := by
  refine ⟨(occurrenceInjection_injective seed H e).comp hc.1,?_,?_,hc.2.2.2⟩
  · intro j q
    change _ = d.model.g (occ j).1.2
      ((OAExec.family d seed (H++[e])).origin (slotInjection H e (occ j).1.1)) +
      (OAExec.family d seed (H++[e])).derivative (slotInjection H e (occ j).1.1)
        (occ j).1.2 (q-(OAExec.family d seed (H++[e])).origin (slotInjection H e (occ j).1.1))
    rw [append_origin,append_derivative]
    exact hc.2.1 j q
  · intro j
    rw [P.append_weight]
    exact hc.2.2.1 j



/-- The stored policy supplies the coverage input to derived availability. No
future optimizer, cost comparison or bounded-master premise occurs here. -/
theorem Policy.successful_master_available {H : List (OAExec.Event d)} (P : Policy d H)
    (a : OAExec.Analytic d) (seed : Point n m) (hs : seed ∈ d.domain)
    (i : Fin H.length) (hn : (H.get i).restoration = none) :
    (historyMaster d seed H).Nonempty ∧
    BddBelow (cost (P.weight seed) '' historyMaster d seed H) ∧
    ∃ z, IsMinimizer (historyMaster d seed H) (cost (P.weight seed)) z := by
  exact covered_successful_soft_master_available d a seed H (P.validHistory hs) i hn
    ((P.generation i).certificate hn) (P.weight seed) (P.weight_nonneg seed)
    (nonlinearSupport ((P.generation i).certificate hn) d.nonlinear)
    (currentOccurrence (OAExec.eventHistory d a seed H (P.validHistory hs) i)
      ((P.generation i).certificate hn))
    (P.event_global_coverage a seed hs i hn)

end Chapter03.OASoftMaster.StoredPolicy
