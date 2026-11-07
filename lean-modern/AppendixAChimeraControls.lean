module

public import AppendixAChimeraBridge

@[expose] public section

/-! Actual sampled inputs and kernel-checked finite controls. Coordinates below
are typed shores/indices, not asserted values of the arbitrary physEquiv. The
universal construction uses choice; hand-selected branches are separate controls. -/
noncomputable section
namespace AppendixAChimeraControls
open AppendixAChimera
attribute [local instance] Classical.propDecidable

def a (i : Fin 4) : Cell := (false,i)
def b (i : Fin 4) : Cell := (true,i)

def fullH : Finset (Phys × Phys) := Finset.univ.filter (fun e => Hardware e.1 e.2)

theorem all_active (p : Phys) : Active (Finset.univ : Finset Cell) p := by
  cases p <;> simp [Active]

def fullSample (F : Finset (Cell × Cell))
    (hF : ∀ e ∈ F, e.1.1 ≠ e.2.1) : Sample where
  U := Finset.univ
  H := fullH
  F := F
  sampled_hardware := by intro e he; exact (Finset.mem_filter.mp he).2
  sampled_active := by intro e _; exact ⟨all_active e.1,all_active e.2⟩
  selected_sampled := by
    intro e he
    exact Or.inl (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hF e he⟩)
  selected_active := by intro e _; simp

def noContractions : Sample := fullSample ∅ (by simp)
def oneEdgeF : Finset (Cell × Cell) := {(a 0,b 0)}
def aStarF : Finset (Cell × Cell) := {(a 0,b 0),(a 0,b 1),(a 0,b 2)}
def bStarF : Finset (Cell × Cell) := {(a 0,b 0),(a 1,b 0),(a 2,b 0)}
def pathF : Finset (Cell × Cell) := {(a 0,b 0),(a 1,b 0),(a 1,b 1)}

theorem oneEdge_cross : ∀ e ∈ oneEdgeF, e.1.1 ≠ e.2.1 := by
  intro e he
  have heq : e = (a 0,b 0) := Finset.mem_singleton.mp he
  subst e
  simp [a,b]

theorem aStar_cross : ∀ e ∈ aStarF, e.1.1 ≠ e.2.1 := by
  intro e he
  simp only [aStarF, Finset.mem_insert, Finset.mem_singleton] at he
  rcases he with rfl | rfl | rfl <;> simp [a,b]

theorem bStar_cross : ∀ e ∈ bStarF, e.1.1 ≠ e.2.1 := by
  intro e he
  simp only [bStarF, Finset.mem_insert, Finset.mem_singleton] at he
  rcases he with rfl | rfl | rfl <;> simp [a,b]

theorem path_cross : ∀ e ∈ pathF, e.1.1 ≠ e.2.1 := by
  intro e he
  simp only [pathF, Finset.mem_insert, Finset.mem_singleton] at he
  rcases he with rfl | rfl | rfl <;> simp [a,b]

def oneEdge : Sample := fullSample oneEdgeF oneEdge_cross
def aStar : Sample := fullSample aStarF aStar_cross
def bStar : Sample := fullSample bStarF bStar_cross
def path : Sample := fullSample pathF path_cross

def denseF : Finset (Cell × Cell) :=
  (Finset.univ : Finset (Fin 4 × Fin 4)).image (fun ij => (a ij.1,b ij.2))

theorem denseF_mem (i j : Fin 4) : (a i,b j) ∈ denseF :=
  Finset.mem_image.mpr ⟨(i,j),Finset.mem_univ _,rfl⟩

theorem denseF_cross : ∀ e ∈ denseF, e.1.1 ≠ e.2.1 := by
  intro e he
  rcases Finset.mem_image.mp he with ⟨ij,_,rfl⟩
  simp [a,b]

def dense : Sample := fullSample denseF denseF_cross

theorem denseF_card : denseF.card = 16 := by
  have hinj : Function.Injective (fun ij : Fin 4 × Fin 4 => (a ij.1,b ij.2)) := by
    intro x y h
    simpa [a,b,Prod.ext_iff] using h
  rw [denseF, Finset.card_image_of_injective _ hinj]
  simp

def emptyFirstH : Finset (Phys × Phys) :=
  Finset.univ.filter (fun e => Hardware e.1 e.2 ∧ Active ∅ e.1 ∧ Active ∅ e.2)

def emptyFirst : Sample where
  U := ∅
  H := emptyFirstH
  F := ∅
  sampled_hardware := by intro e he; exact (Finset.mem_filter.mp he).2.1
  sampled_active := by intro e he; exact (Finset.mem_filter.mp he).2.2
  selected_sampled := by simp
  selected_active := by simp

def attachmentMask : Phys → Phys → Prop
  | .inl x, .inr _ => x = b 1
  | .inr _, .inl y => y = b 1
  | _, _ => True

def sparseH : Finset (Phys × Phys) :=
  fullH.filter (fun e => attachmentMask e.1 e.2)

def missingAttachments : Sample where
  U := Finset.univ
  H := sparseH
  F := aStarF
  sampled_hardware := by intro e he; exact (Finset.mem_filter.mp (Finset.mem_filter.mp he).1).2
  sampled_active := by intro e _; exact ⟨all_active e.1,all_active e.2⟩
  selected_sampled := by
    intro e he
    exact Or.inl (Finset.mem_filter.mpr
      ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, aStar_cross e he⟩, trivial⟩)
  selected_active := by intro e _; simp

theorem noContractions_embedding :
    ∃ A, AppendixATheory.fiber A = finiteBranches noContractions ∧
      AppendixATheory.Embedding targetEdges (logicalEdges noContractions) 2 A :=
  exists_twoCell_embedding noContractions

theorem oneEdge_embedding :
    ∃ A, AppendixATheory.fiber A = finiteBranches oneEdge ∧
      AppendixATheory.Embedding targetEdges (logicalEdges oneEdge) 2 A :=
  exists_twoCell_embedding oneEdge

theorem aStar_embedding :
    ∃ A, AppendixATheory.fiber A = finiteBranches aStar ∧
      AppendixATheory.Embedding targetEdges (logicalEdges aStar) 2 A :=
  exists_twoCell_embedding aStar

theorem bStar_embedding :
    ∃ A, AppendixATheory.fiber A = finiteBranches bStar ∧
      AppendixATheory.Embedding targetEdges (logicalEdges bStar) 2 A :=
  exists_twoCell_embedding bStar

theorem path_embedding :
    ∃ A, AppendixATheory.fiber A = finiteBranches path ∧
      AppendixATheory.Embedding targetEdges (logicalEdges path) 2 A :=
  exists_twoCell_embedding path

theorem emptyFirst_embedding :
    ∃ A, AppendixATheory.fiber A = finiteBranches emptyFirst ∧
      AppendixATheory.Embedding targetEdges (logicalEdges emptyFirst) 2 A :=
  exists_twoCell_embedding emptyFirst

theorem missingAttachments_embedding :
    ∃ A, AppendixATheory.fiber A = finiteBranches missingAttachments ∧
      AppendixATheory.Embedding targetEdges (logicalEdges missingAttachments) 2 A :=
  exists_twoCell_embedding missingAttachments

theorem dense_embedding :
    ∃ A, AppendixATheory.fiber A = finiteBranches dense ∧
      AppendixATheory.Embedding targetEdges (logicalEdges dense) 2 A :=
  exists_twoCell_embedding dense

def aStarSupport : Finset Cell := {a 0,b 0,b 1,b 2}

theorem aStar_step_end {x y : Cell} (h : Adj aStar.F x y) : y ∈ aStarSupport := by
  rcases h with h | h
  · simp only [aStar,fullSample,aStarF,Finset.mem_insert,Finset.mem_singleton,Prod.mk.injEq] at h
    rcases h with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ <;> simp [aStarSupport]
  · simp only [aStar,fullSample,aStarF,Finset.mem_insert,Finset.mem_singleton,Prod.mk.injEq] at h
    rcases h with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ <;> simp [aStarSupport]

theorem aStar_component : component aStar (a 0) = aStarSupport := by
  apply Finset.Subset.antisymm
  · intro y hy
    have hr := (Finset.mem_filter.mp hy).2
    induction hr with
    | refl => simp [aStarSupport]
    | tail hxy hyz ih => exact aStar_step_end hyz
  · intro y hy
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _, ?_⟩
    simp only [aStarSupport,Finset.mem_insert,Finset.mem_singleton] at hy
    rcases hy with rfl | rfl | rfl | rfl
    · exact Relation.ReflTransGen.refl
    all_goals apply Relation.ReflTransGen.single; left; simp [aStar,fullSample,aStarF]

theorem aStar_component_card : (component aStar (a 0)).card = 4 := by
  rw [aStar_component]
  simp [aStarSupport,a,b]

set_option backward.isDefEq.respectTransparency false in
theorem dense_component : component dense (a 0) = Finset.univ := by
  ext x
  simp only [component,dense,fullSample,Finset.mem_filter,Finset.mem_univ,true_and,iff_true]
  rcases x with ⟨s,i⟩
  cases s
  · have hab : Adj denseF (a 0) (b 0) := Or.inl (denseF_mem 0 0)
    exact (Relation.ReflTransGen.single hab).tail (Or.inr (denseF_mem i 0))
  · exact Relation.ReflTransGen.single (Or.inl (denseF_mem 0 i))

theorem dense_component_card : (component dense (a 0)).card = 8 := by
  rw [dense_component]
  simp [Cell,Fintype.card_prod]

theorem emptyFirst_no_component : IsEmpty (Component emptyFirst) := by
  refine ⟨?_⟩
  intro C
  rcases C.property with ⟨x,hx,_⟩
  simp [emptyFirst] at hx

theorem emptyFirst_count : logicalCount emptyFirst = 8 := by
  letI := emptyFirst_no_component
  simp [logicalCount,Label,Cell,Fintype.card_sum,Fintype.card_prod]

set_option backward.isDefEq.respectTransparency false in
theorem missing_coupler_absent :
    ¬ Adj missingAttachments.H (first (b 2)) (second (b 2)) := by
  simp [Adj,missingAttachments,sparseH,fullH,attachmentMask,b]

theorem missing_coupler_hardware : Hardware (first (b 2)) (second (b 2)) := by
  simp [Hardware,b]

set_option backward.isDefEq.respectTransparency false in
theorem sampled_coupler_present :
    Adj missingAttachments.H (first (b 1)) (second (b 1)) := by
  simp [Adj,missingAttachments,sparseH,fullH,attachmentMask,Hardware,b]

theorem noContractions_component (x : Cell) : component noContractions x = {x} := by
  ext y
  constructor
  · intro hy
    have hr := (Finset.mem_filter.mp hy).2
    induction hr with
    | refl => simp
    | tail hxy hyz ih => simp [Adj,noContractions,fullSample] at hyz
  · intro hy
    have hxy : y = x := Finset.mem_singleton.mp hy
    subst y
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,Relation.ReflTransGen.refl⟩

def pathSupport : Finset Cell := {a 0,a 1,b 0,b 1}

theorem path_step_end {x y : Cell} (h : Adj path.F x y) : y ∈ pathSupport := by
  rcases h with h | h
  · simp only [path,fullSample,pathF,Finset.mem_insert,Finset.mem_singleton,Prod.mk.injEq] at h
    rcases h with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ <;> simp [pathSupport]
  · simp only [path,fullSample,pathF,Finset.mem_insert,Finset.mem_singleton,Prod.mk.injEq] at h
    rcases h with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ <;> simp [pathSupport]

theorem path_component : component path (a 0) = pathSupport := by
  have h₀ : Adj path.F (a 0) (b 0) := by left; simp [path,fullSample,pathF]
  have h₁ : Adj path.F (b 0) (a 1) := by right; simp [path,fullSample,pathF]
  have h₂ : Adj path.F (a 1) (b 1) := by left; simp [path,fullSample,pathF]
  apply Finset.Subset.antisymm
  · intro y hy
    have hr := (Finset.mem_filter.mp hy).2
    induction hr with
    | refl => simp [pathSupport]
    | tail hxy hyz ih => exact path_step_end hyz
  · intro y hy
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _,?_⟩
    simp only [pathSupport,Finset.mem_insert,Finset.mem_singleton] at hy
    rcases hy with rfl | rfl | rfl | rfl
    · exact Relation.ReflTransGen.refl
    · exact (Relation.ReflTransGen.single h₀).tail h₁
    · exact Relation.ReflTransGen.single h₀
    · exact ((Relation.ReflTransGen.single h₀).tail h₁).tail h₂

theorem path_component_card : (component path (a 0)).card = 4 := by
  rw [path_component]
  simp [pathSupport,a,b]

theorem missing_coupler_connected : AppendixA.connected targetEdges
    {physEquiv (first (b 2)),physEquiv (second (b 2))} :=
  connected_pair_bridge _ _ _ (Or.inr ((hardware_transport _ _).mpr missing_coupler_hardware))

def aStarLabel : Label aStar := .inl (componentLabel aStar (a 0) (by simp [aStar,fullSample]))

theorem aStar_originalFiber_card : (originalFiber aStar aStarLabel).card = 4 := by
  change ((component aStar (a 0)).image first).card = 4
  rw [Finset.card_image_of_injective _ Sum.inl_injective]
  exact aStar_component_card

set_option backward.isDefEq.respectTransparency false in
theorem aStar_attachment_edge : QuotientAdj aStar aStarLabel (.inr (b 1)) := by
  constructor
  · simp [aStarLabel]
  · refine ⟨first (b 1),?_,second (b 1),by simp [originalFiber],?_⟩
    · change first (b 1) ∈ (component aStar (a 0)).image first
      rw [aStar_component]
      exact Finset.mem_image.mpr ⟨b 1,by simp [aStarSupport],rfl⟩
    · left
      simp [aStar,fullSample,fullH,Hardware,b]

def shortStarPair : Finset (Fin 16) := {physEquiv (first (a 0)),physEquiv (first (b 0))}

theorem shortStarPair_misses_attachment :
    ¬ ∃u ∈ shortStarPair, ∃v ∈ ({physEquiv (second (b 1))} : Finset (Fin 16)),
      AppendixA.adjacent targetEdges u v := by
  rintro ⟨u,hu,v,hv,he⟩
  have hv' : v = physEquiv (second (b 1)) := Finset.mem_singleton.mp hv
  subst v
  simp only [shortStarPair,Finset.mem_insert,Finset.mem_singleton] at hu
  rcases hu with rfl | rfl
  all_goals have hh := (hardware_transport _ _).mp he
  all_goals simp [Hardware,a,b] at hh

/- This mutation deliberately shrinks the star component and leaves its sampled
attachment singleton. It does not assert which representatives choice selected. -/
def lostTransferBranches (j : Fin (logicalCount aStar)) : Finset (Fin 16) :=
  if (labelEquiv aStar).symm j = aStarLabel then shortStarPair
  else (originalFiber aStar ((labelEquiv aStar).symm j)).image physEquiv

theorem lostTransfer_not_branchModel :
    ¬ AppendixATheory.BranchModel targetEdges (logicalEdges aStar) 2 lostTransferBranches := by
  intro h
  have he := (logical_transport aStar aStarLabel (.inr (b 1))).mpr aStar_attachment_edge
  have hc := h.2.2 _ _ he
  apply shortStarPair_misses_attachment
  simpa [lostTransferBranches,originalFiber,aStarLabel] using hc

/- A second-shore twin label is assigned a duplicate singleton. This targets the
actual disjointness field, independently of the missing-transfer mutation. -/
def duplicateBranches (j : Fin (logicalCount noContractions)) : Finset (Fin 16) :=
  if (labelEquiv noContractions).symm j = (.inr (a 1) : Label noContractions) ∨
      (labelEquiv noContractions).symm j = (.inr (a 2) : Label noContractions)
  then {physEquiv (second (a 1))} else finiteBranches noContractions j

theorem duplicate_not_branchModel :
    ¬ AppendixATheory.BranchModel targetEdges (logicalEdges noContractions) 2 duplicateBranches := by
  intro h
  have hne : (labelEquiv noContractions) (.inr (a 1)) ≠
      (labelEquiv noContractions) (.inr (a 2)) := by
    intro he
    have he' := (labelEquiv noContractions).injective he
    simp [a] at he'
  have hd := h.2.1 _ _ hne
  simp [duplicateBranches] at hd

end AppendixAChimeraControls

#print axioms AppendixAChimeraControls.a
#print axioms AppendixAChimeraControls.b
#print axioms AppendixAChimeraControls.fullH
#print axioms AppendixAChimeraControls.all_active
#print axioms AppendixAChimeraControls.fullSample
#print axioms AppendixAChimeraControls.noContractions
#print axioms AppendixAChimeraControls.oneEdgeF
#print axioms AppendixAChimeraControls.aStarF
#print axioms AppendixAChimeraControls.bStarF
#print axioms AppendixAChimeraControls.pathF
#print axioms AppendixAChimeraControls.oneEdge_cross
#print axioms AppendixAChimeraControls.aStar_cross
#print axioms AppendixAChimeraControls.bStar_cross
#print axioms AppendixAChimeraControls.path_cross
#print axioms AppendixAChimeraControls.oneEdge
#print axioms AppendixAChimeraControls.aStar
#print axioms AppendixAChimeraControls.bStar
#print axioms AppendixAChimeraControls.path
#print axioms AppendixAChimeraControls.denseF
#print axioms AppendixAChimeraControls.denseF_mem
#print axioms AppendixAChimeraControls.denseF_cross
#print axioms AppendixAChimeraControls.dense
#print axioms AppendixAChimeraControls.denseF_card
#print axioms AppendixAChimeraControls.emptyFirstH
#print axioms AppendixAChimeraControls.emptyFirst
#print axioms AppendixAChimeraControls.attachmentMask
#print axioms AppendixAChimeraControls.sparseH
#print axioms AppendixAChimeraControls.missingAttachments
#print axioms AppendixAChimeraControls.noContractions_embedding
#print axioms AppendixAChimeraControls.oneEdge_embedding
#print axioms AppendixAChimeraControls.aStar_embedding
#print axioms AppendixAChimeraControls.bStar_embedding
#print axioms AppendixAChimeraControls.path_embedding
#print axioms AppendixAChimeraControls.emptyFirst_embedding
#print axioms AppendixAChimeraControls.missingAttachments_embedding
#print axioms AppendixAChimeraControls.dense_embedding
#print axioms AppendixAChimeraControls.aStarSupport
#print axioms AppendixAChimeraControls.aStar_step_end
#print axioms AppendixAChimeraControls.aStar_component
#print axioms AppendixAChimeraControls.aStar_component_card
#print axioms AppendixAChimeraControls.dense_component
#print axioms AppendixAChimeraControls.dense_component_card
#print axioms AppendixAChimeraControls.emptyFirst_no_component
#print axioms AppendixAChimeraControls.emptyFirst_count
#print axioms AppendixAChimeraControls.missing_coupler_absent
#print axioms AppendixAChimeraControls.missing_coupler_hardware
#print axioms AppendixAChimeraControls.sampled_coupler_present
#print axioms AppendixAChimeraControls.noContractions_component
#print axioms AppendixAChimeraControls.pathSupport
#print axioms AppendixAChimeraControls.path_step_end
#print axioms AppendixAChimeraControls.path_component
#print axioms AppendixAChimeraControls.path_component_card
#print axioms AppendixAChimeraControls.missing_coupler_connected
#print axioms AppendixAChimeraControls.aStarLabel
#print axioms AppendixAChimeraControls.aStar_originalFiber_card
#print axioms AppendixAChimeraControls.aStar_attachment_edge
#print axioms AppendixAChimeraControls.shortStarPair
#print axioms AppendixAChimeraControls.shortStarPair_misses_attachment
#print axioms AppendixAChimeraControls.lostTransferBranches
#print axioms AppendixAChimeraControls.lostTransfer_not_branchModel
#print axioms AppendixAChimeraControls.duplicateBranches
#print axioms AppendixAChimeraControls.duplicate_not_branchModel
