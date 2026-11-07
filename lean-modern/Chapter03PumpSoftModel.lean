module

public import Chapter03PumpOAInvariant
public import Chapter03OASoftExecutionAvailability

@[expose] public section

noncomputable section
open Chapter02 Chapter03.OAKKT Chapter03.OAExec Chapter03.OASoftMaster
open Chapter03.OASoftMaster.StoredPolicy
namespace Chapter03.PumpSoft
variable {n m l r : ℕ}

def prefixCount (d : OAExec.Data n m l r) (delta : ℝ) (P : FP.State n m) : ℕ :=
  (FP.anchors (PumpOA.asFPDelta d delta) P).length

def prefixFamily (d : OAExec.Data n m l r) (delta : ℝ) (P : FP.State n m) :=
  FP.family (PumpOA.asFPDelta d delta) P

theorem prefixCount_pos (d : OAExec.Data n m l r) (delta : ℝ) (P : FP.State n m) :
    0 < prefixCount d delta P := by simp [prefixCount,FP.anchors]

def seedIndex (d : OAExec.Data n m l r) (delta : ℝ) (P : FP.State n m) :
    Fin (prefixCount d delta P) := ⟨0,prefixCount_pos d delta P⟩

def family (d : OAExec.Data n m l r) (delta : ℝ) (P : FP.State n m)
    (H : List (OAExec.Event d)) : TangentFamily n m l (prefixCount d delta P+H.length) where
  origin := Fin.addCases (prefixFamily d delta P).origin (fun i => (H.get i).anchor)
  selected := Fin.addCases (prefixFamily d delta P).selected (fun i => d.selected (H.get i).anchor)
  derivative i := d.Dg (Fin.addCases (prefixFamily d delta P).origin (fun i => (H.get i).anchor) i)

def familyDf (d : OAExec.Data n m l r) (delta : ℝ) (P : FP.State n m)
    (H : List (OAExec.Event d)) (i : Fin (prefixCount d delta P+H.length)) :=
  d.Df ((family d delta P H).origin i)

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
@[simp] theorem family_prefix_origin (d : OAExec.Data n m l r) (delta : ℝ) (P : FP.State n m)
    (H : List (OAExec.Event d)) (i : Fin (prefixCount d delta P)) :
    (family d delta P H).origin (Fin.castAdd H.length i)=(prefixFamily d delta P).origin i := by
  dsimp only [family,prefixCount,prefixFamily] at *
  exact Fin.addCases_left i
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
@[simp] theorem family_suffix_origin (d : OAExec.Data n m l r) (delta : ℝ) (P : FP.State n m)
    (H : List (OAExec.Event d)) (i : Fin H.length) :
    (family d delta P H).origin (Fin.natAdd (prefixCount d delta P) i)=(H.get i).anchor := by
  dsimp only [family,prefixCount,prefixFamily] at *
  exact Fin.addCases_right i
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
@[simp] theorem family_prefix_selected (d : OAExec.Data n m l r) (delta : ℝ) (P : FP.State n m)
    (H : List (OAExec.Event d)) (i : Fin (prefixCount d delta P)) :
    (family d delta P H).selected (Fin.castAdd H.length i)=(prefixFamily d delta P).selected i := by
  dsimp only [family,prefixCount,prefixFamily] at *
  exact Fin.addCases_left i
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
@[simp] theorem family_suffix_selected (d : OAExec.Data n m l r) (delta : ℝ) (P : FP.State n m)
    (H : List (OAExec.Event d)) (i : Fin H.length) :
    (family d delta P H).selected (Fin.natAdd (prefixCount d delta P) i)=d.selected (H.get i).anchor := by
  dsimp only [family,prefixCount,prefixFamily] at *
  exact Fin.addCases_right i

@[simp] theorem prefix_seed_origin (d : OAExec.Data n m l r) (delta : ℝ) (P : FP.State n m) :
    (prefixFamily d delta P).origin (seedIndex d delta P)=P.seed := rfl
@[simp] theorem prefix_seed_selected (d : OAExec.Data n m l r) (delta : ℝ) (P : FP.State n m) :
    (prefixFamily d delta P).selected (seedIndex d delta P)=Set.univ := rfl

def seedOccurrence (d : OAExec.Data n m l r) (delta : ℝ) (P : FP.State n m) (j : Fin l) :
    Occurrence (prefixFamily d delta P) := ⟨(seedIndex d delta P,j),by simp⟩

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
def prefixOccurrence (d : OAExec.Data n m l r) (delta : ℝ) (P : FP.State n m)
    (H : List (OAExec.Event d)) (o : Occurrence (prefixFamily d delta P)) :
    Occurrence (family d delta P H) := ⟨(Fin.castAdd H.length o.1.1,o.1.2),by
      change o.1.2 ∈ (family d delta P H).selected (Fin.castAdd H.length o.1.1)
      rw [family_prefix_selected]
      exact o.2⟩

def suffixIndex (d : OAExec.Data n m l r) (delta : ℝ) (P : FP.State n m)
    (H : List (OAExec.Event d)) : Fin (H.length+1) → Fin (prefixCount d delta P+H.length) :=
  Fin.cases (Fin.castAdd H.length (seedIndex d delta P)) (Fin.natAdd (prefixCount d delta P))

theorem suffixIndex_injective (d : OAExec.Data n m l r) (delta : ℝ) (P : FP.State n m)
    (H : List (OAExec.Event d)) : Function.Injective (suffixIndex d delta P H) := by
  intro i
  refine Fin.cases ?_ (fun i => ?_) i <;> intro j <;> refine Fin.cases ?_ (fun j => ?_) j <;> intro h
  · rfl
  · have hh := congrArg Fin.val h
    simp [suffixIndex,seedIndex] at hh
    have := prefixCount_pos d delta P
    omega
  · have hh := congrArg Fin.val h
    simp [suffixIndex,seedIndex] at hh
    have := prefixCount_pos d delta P
    omega
  · apply congrArg Fin.succ
    apply Fin.ext
    have hh := congrArg Fin.val h
    simp [suffixIndex] at hh
    omega

@[simp] theorem suffix_origin (d : OAExec.Data n m l r) (delta : ℝ) (P : FP.State n m)
    (H : List (OAExec.Event d)) (i : Fin (H.length+1)) :
    (family d delta P H).origin (suffixIndex d delta P H i)=(OAExec.family d P.seed H).origin i := by
  refine Fin.cases ?_ (fun i=>?_) i <;> simp [suffixIndex,OAExec.family]
@[simp] theorem suffix_selected (d : OAExec.Data n m l r) (delta : ℝ) (P : FP.State n m)
    (H : List (OAExec.Event d)) (i : Fin (H.length+1)) :
    (family d delta P H).selected (suffixIndex d delta P H i)=(OAExec.family d P.seed H).selected i := by
  refine Fin.cases ?_ (fun i=>?_) i <;> simp [suffixIndex,OAExec.family]

@[simp] theorem suffix_derivative (d : OAExec.Data n m l r) (delta : ℝ) (P : FP.State n m)
    (H : List (OAExec.Event d)) (i : Fin (H.length+1)) (j : Fin l) :
    (family d delta P H).derivative (suffixIndex d delta P H i) j=(OAExec.family d P.seed H).derivative i j := by
  change d.Dg ((family d delta P H).origin (suffixIndex d delta P H i)) j = _
  rw [suffix_origin]
  rfl

def suffixOccurrence (d : OAExec.Data n m l r) (delta : ℝ) (P : FP.State n m)
    (H : List (OAExec.Event d)) (o : Occurrence (OAExec.family d P.seed H)) :
    Occurrence (family d delta P H) := ⟨(suffixIndex d delta P H o.1.1,o.1.2),by simpa using o.2⟩

theorem suffixOccurrence_injective (d : OAExec.Data n m l r) (delta : ℝ) (P : FP.State n m)
    (H : List (OAExec.Event d)) : Function.Injective (suffixOccurrence d delta P H) := by
  intro a b h
  apply Subtype.ext
  apply Prod.ext
  · exact suffixIndex_injective d delta P H (congrArg (fun o => o.1.1) h)
  · exact congrArg (fun o => o.1.2) h

def SeedAgreement (d : OAExec.Data n m l r) (delta : ℝ) (P : FP.State n m)
    (W : Occurrence (prefixFamily d delta P) → ℝ) {H : List (OAExec.Event d)} (Q : Policy d H) : Prop :=
  ∀j,Q.seedWeight j=W (seedOccurrence d delta P j)

def initialPolicy (d : OAExec.Data n m l r) (delta : ℝ) (P : FP.State n m)
    (W : Occurrence (prefixFamily d delta P) → ℝ) (hW : ∀o,0≤W o) : Policy d [] where
  seedWeight j := W (seedOccurrence d delta P j)
  seed_nonneg _ := hW _
  generation i := Fin.elim0 i

theorem initialPolicy_agreement (d : OAExec.Data n m l r) (delta : ℝ) (P : FP.State n m)
    (W : Occurrence (prefixFamily d delta P) → ℝ) (hW : ∀o,0≤W o) :
    SeedAgreement d delta P W (initialPolicy d delta P W hW) := fun _=>rfl

theorem agreement_append (d : OAExec.Data n m l r) (delta : ℝ) (P : FP.State n m)
    (W : Occurrence (prefixFamily d delta P) → ℝ) {H : List (OAExec.Event d)} (Q : Policy d H)
    (hs : SeedAgreement d delta P W Q) (e : OAExec.Event d) (G : Generation d e) :
    SeedAgreement d delta P W (Q.append e G) := hs

def weight (d : OAExec.Data n m l r) (delta : ℝ) (P : FP.State n m)
    (W : Occurrence (prefixFamily d delta P) → ℝ) {H : List (OAExec.Event d)} (Q : Policy d H)
    (o : Occurrence (family d delta P H)) : ℝ :=
  if h : o.1.1.val < prefixCount d delta P then
    W ⟨(⟨o.1.1.val,h⟩,o.1.2),by
      have ho := o.2
      have he : o.1.1 = Fin.castAdd H.length ⟨o.1.1.val,h⟩ := by apply Fin.ext; rfl
      rw [he,family_prefix_selected] at ho
      exact ho⟩
  else (Q.generation ⟨o.1.1.val-prefixCount d delta P,by have := o.1.1.isLt; omega⟩).rowWeight o.1.2

theorem weight_nonneg (d : OAExec.Data n m l r) (delta : ℝ) (P : FP.State n m)
    (W : Occurrence (prefixFamily d delta P) → ℝ) (hW : ∀o,0≤W o)
    {H : List (OAExec.Event d)} (Q : Policy d H) (o : Occurrence (family d delta P H)) :
    0≤weight d delta P W Q o := by
  unfold weight
  split
  · exact hW _
  · exact Generation.rowWeight_nonneg _ _

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
theorem weight_suffix (d : OAExec.Data n m l r) (delta : ℝ) (P : FP.State n m)
    (W : Occurrence (prefixFamily d delta P) → ℝ) {H : List (OAExec.Event d)} (Q : Policy d H)
    (hs : SeedAgreement d delta P W Q) (o : Occurrence (OAExec.family d P.seed H)) :
    weight d delta P W Q (suffixOccurrence d delta P H o)=Q.weight P.seed o := by
  rcases o with ⟨⟨i,j⟩,ho⟩
  revert ho
  refine Fin.cases ?_ (fun i=>?_) i <;> intro ho
  · simpa [weight,suffixOccurrence,suffixIndex,seedIndex,prefixCount_pos,
      Policy.weight,Policy.slotWeight,seedOccurrence] using (hs j).symm
  · simp [weight,suffixOccurrence,suffixIndex,Policy.weight,Policy.slotWeight]
    congr 2 <;> first | omega | (apply Fin.ext; simp only [Fin.val_mk]; omega)

def keep (P : FP.State n m) {d : OAExec.Data n m l r} (H : List (OAExec.Event d))
    (p : Point n m) : Prop := FP.handoffNormals P p ∧ FP.noGoods P p ∧ OAExec.noGoods H p

theorem keep_same_y (P : FP.State n m) {d : OAExec.Data n m l r} (H : List (OAExec.Event d))
    (p q : Point n m) (hy : p.2=q.2) : keep P H p ↔ keep P H q := by
  simp [keep,FP.handoffNormals,FP.noGoods,OAExec.noGoods,FP.Event.normal,yMap,hy]

def warmMaster (d : OAExec.Data n m l r) (delta : ℝ) (P : FP.State n m)
    (H : List (OAExec.Event d)) :=
  OASoftMaster.master d.model d.f (family d delta P H) (familyDf d delta P H) (keep P H)

end Chapter03.PumpSoft
