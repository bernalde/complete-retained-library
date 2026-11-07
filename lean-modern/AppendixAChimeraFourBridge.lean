module

public import AppendixAChimeraFourBranches
public import AppendixAChimeraFourCoverage

@[expose] public section

/-! Coherent finite transport of the explicit aligned four-cell construction.
Arbitrary physical and logical bijections transport both graphs and branches.
The existence theorem uses the proved repairPlan, with no embedding premise. -/
noncomputable section
namespace AppendixAChimeraFour
open AppendixAChimera
attribute [local instance] Classical.propDecidable

def targetEdgesVia4 {n : ℕ} (e : Phys4 ≃ Fin n) : Finset (Fin n × Fin n) :=
  Finset.univ.filter (fun p => Hardware4 (e.symm p.1) (e.symm p.2))

def logicalEdgesVia4 {m : ℕ} (D : Sample4) (g : Label4 D ≃ Fin m) :
    Finset (Fin m × Fin m) :=
  Finset.univ.filter (fun p => QuotientAdj4 D (g.symm p.1) (g.symm p.2))

def finiteBranchesVia4 {n m : ℕ} (D : Sample4) (P : RepairPlan D)
    (e : Phys4 ≃ Fin n) (g : Label4 D ≃ Fin m) (j : Fin m) : Finset (Fin n) :=
  (finalBranch D P (g.symm j)).image e

theorem targetVia4_adjacent_iff {n : ℕ} (e : Phys4 ≃ Fin n) (a b : Fin n) :
    AppendixA.adjacent (targetEdgesVia4 e) a b ↔ Hardware4 (e.symm a) (e.symm b) := by
  simp only [AppendixA.adjacent,targetEdgesVia4,Finset.mem_filter,Finset.mem_univ,true_and]
  exact ⟨fun h => h.elim id (fun h => hardware4_symmetric h),Or.inl⟩

theorem hardwareVia4_transport {n : ℕ} (e : Phys4 ≃ Fin n) (u v : Phys4) :
    AppendixA.adjacent (targetEdgesVia4 e) (e u) (e v) ↔ Hardware4 u v := by
  simpa using targetVia4_adjacent_iff e (e u) (e v)

theorem logicalVia4_adjacent_iff {m : ℕ} (D : Sample4) (g : Label4 D ≃ Fin m)
    (j l : Fin m) : AppendixA.adjacent (logicalEdgesVia4 D g) j l ↔
      QuotientAdj4 D (g.symm j) (g.symm l) := by
  simp only [AppendixA.adjacent,logicalEdgesVia4,Finset.mem_filter,Finset.mem_univ,true_and]
  exact ⟨fun h => h.elim id (fun h => quotientAdj4_symmetric D h),Or.inl⟩

theorem logicalVia4_transport {m : ℕ} (D : Sample4) (g : Label4 D ≃ Fin m)
    (j l : Label4 D) : AppendixA.adjacent (logicalEdgesVia4 D g) (g j) (g l) ↔
      QuotientAdj4 D j l := by
  simpa using logicalVia4_adjacent_iff D g (g j) (g l)

theorem finiteBranchesVia4_mem {n m : ℕ} (D : Sample4) (P : RepairPlan D)
    (e : Phys4 ≃ Fin n) (g : Label4 D ≃ Fin m) (j : Fin m) (u : Phys4) :
    e u ∈ finiteBranchesVia4 D P e g j ↔ u ∈ finalBranch D P (g.symm j) := by
  simp [finiteBranchesVia4]

theorem finiteBranchesVia4_label_transport {n m : ℕ} (D : Sample4) (P : RepairPlan D)
    (e : Phys4 ≃ Fin n) (g : Label4 D ≃ Fin m) (j : Label4 D) (u : Phys4) :
    e u ∈ finiteBranchesVia4 D P e g (g j) ↔ u ∈ finalBranch D P j := by
  simpa using finiteBranchesVia4_mem D P e g (g j) u

theorem finiteBranchesVia4_connected {n m : ℕ} (D : Sample4) (P : RepairPlan D)
    (e : Phys4 ≃ Fin n) (g : Label4 D ≃ Fin m) (j : Fin m) :
    AppendixA.connected (targetEdgesVia4 e) (finiteBranchesVia4 D P e g j) := by
  intro a ha b hb
  rcases Finset.mem_image.mp ha with ⟨u,hu,rfl⟩
  rcases Finset.mem_image.mp hb with ⟨v,hv,rfl⟩
  apply Relation.ReflTransGen.lift e ?_ u v (finalBranch_connected D P (g.symm j) u hu v hv)
  intro x y hxy
  exact ⟨Finset.mem_image.mpr ⟨x,hxy.1,rfl⟩,
    Finset.mem_image.mpr ⟨y,hxy.2.1,rfl⟩,(hardwareVia4_transport e x y).mpr hxy.2.2⟩

theorem finiteBranchesVia4_branchModel {n m : ℕ} (D : Sample4) (P : RepairPlan D)
    (e : Phys4 ≃ Fin n) (g : Label4 D ≃ Fin m) :
    AppendixATheory.BranchModel (targetEdgesVia4 e) (logicalEdgesVia4 D g) 3
      (finiteBranchesVia4 D P e g) := by
  refine ⟨?_,?_,?_⟩
  · intro j
    exact ⟨(finalBranch_nonempty D P _).image e,
      Finset.card_image_le.trans (finalBranch_card_le_three D P _),
      finiteBranchesVia4_connected D P e g j⟩
  · intro j l hne
    apply Finset.disjoint_left.mpr
    intro p hp hq
    rcases Finset.mem_image.mp hp with ⟨u,hu,hu'⟩
    rcases Finset.mem_image.mp hq with ⟨v,hv,hv'⟩
    have huv : u = v := e.injective (hu'.trans hv'.symm)
    subst v
    exact Finset.disjoint_left.mp (finalBranch_disjoint D P _ _
      (fun heq => hne (g.symm.injective heq))) hu hv
  · intro j l h
    rcases final_quotient_covered D P ((logicalVia4_adjacent_iff D g j l).mp h) with
      ⟨u,hu,v,hv,he⟩
    exact ⟨e u,Finset.mem_image.mpr ⟨u,hu,rfl⟩,
      e v,Finset.mem_image.mpr ⟨v,hv,rfl⟩,(hardwareVia4_transport e u v).mpr he⟩

theorem finiteBranchesVia4_embedding {n m : ℕ} (D : Sample4) (P : RepairPlan D)
    (e : Phys4 ≃ Fin n) (g : Label4 D ≃ Fin m) :
    AppendixATheory.Embedding (targetEdgesVia4 e) (logicalEdgesVia4 D g) 3
      (AppendixATheory.alphaOfFibers (finiteBranchesVia4 D P e g)) := by
  apply (AppendixATheory.embedding_iff_branchModel _ _ _ _).mpr
  simpa using finiteBranchesVia4_branchModel D P e g

theorem exists_fourCell_embeddingVia {n m : ℕ} (D : Sample4)
    (e : Phys4 ≃ Fin n) (g : Label4 D ≃ Fin m) :
    ∃ A : AppendixATheory.Alpha n m,
      AppendixATheory.fiber A = finiteBranchesVia4 D (repairPlan D) e g ∧
      AppendixATheory.Embedding (targetEdgesVia4 e) (logicalEdgesVia4 D g) 3 A :=
  (AppendixATheory.branchModel_alpha_projection _ _ _ _).mpr
    (finiteBranchesVia4_branchModel D (repairPlan D) e g)

/-- The exact finite numbering and graphs already fixed by Data4. -/
def finiteBranches4 (D : Sample4) (P : RepairPlan D) :
    Fin (logicalCount4 D) → Finset (Fin 32) :=
  finiteBranchesVia4 D P physEquiv4 (labelEquiv4 D)

theorem finiteBranches4_mem (D : Sample4) (P : RepairPlan D)
    (j : Fin (logicalCount4 D)) (u : Phys4) :
    physEquiv4 u ∈ finiteBranches4 D P j ↔
      u ∈ finalBranch D P ((labelEquiv4 D).symm j) :=
  finiteBranchesVia4_mem D P physEquiv4 (labelEquiv4 D) j u

theorem finiteBranches4_branchModel (D : Sample4) (P : RepairPlan D) :
    AppendixATheory.BranchModel targetEdges4 (logicalEdges4 D) 3 (finiteBranches4 D P) :=
  finiteBranchesVia4_branchModel D P physEquiv4 (labelEquiv4 D)

theorem finiteBranches4_embedding (D : Sample4) (P : RepairPlan D) :
    AppendixATheory.Embedding targetEdges4 (logicalEdges4 D) 3
      (AppendixATheory.alphaOfFibers (finiteBranches4 D P)) :=
  finiteBranchesVia4_embedding D P physEquiv4 (labelEquiv4 D)

theorem exists_fourCell_embedding (D : Sample4) :
    ∃ A : AppendixATheory.Alpha 32 (logicalCount4 D),
      AppendixATheory.fiber A = finiteBranches4 D (repairPlan D) ∧
      AppendixATheory.Embedding targetEdges4 (logicalEdges4 D) 3 A :=
  exists_fourCell_embeddingVia D physEquiv4 (labelEquiv4 D)

end AppendixAChimeraFour

-- Explicit types and bounded transitive-axiom diagnostics.
set_option pp.all true
set_option pp.deepTerms true
#check AppendixAChimeraFour.targetEdgesVia4
#print axioms AppendixAChimeraFour.targetEdgesVia4
#check AppendixAChimeraFour.logicalEdgesVia4
#print axioms AppendixAChimeraFour.logicalEdgesVia4
#check AppendixAChimeraFour.finiteBranchesVia4
#print axioms AppendixAChimeraFour.finiteBranchesVia4
#check AppendixAChimeraFour.targetVia4_adjacent_iff
#print axioms AppendixAChimeraFour.targetVia4_adjacent_iff
#check AppendixAChimeraFour.hardwareVia4_transport
#print axioms AppendixAChimeraFour.hardwareVia4_transport
#check AppendixAChimeraFour.logicalVia4_adjacent_iff
#print axioms AppendixAChimeraFour.logicalVia4_adjacent_iff
#check AppendixAChimeraFour.logicalVia4_transport
#print axioms AppendixAChimeraFour.logicalVia4_transport
#check AppendixAChimeraFour.finiteBranchesVia4_mem
#print axioms AppendixAChimeraFour.finiteBranchesVia4_mem
#check AppendixAChimeraFour.finiteBranchesVia4_label_transport
#print axioms AppendixAChimeraFour.finiteBranchesVia4_label_transport
#check AppendixAChimeraFour.finiteBranchesVia4_connected
#print axioms AppendixAChimeraFour.finiteBranchesVia4_connected
#check AppendixAChimeraFour.finiteBranchesVia4_branchModel
#print axioms AppendixAChimeraFour.finiteBranchesVia4_branchModel
#check AppendixAChimeraFour.finiteBranchesVia4_embedding
#print axioms AppendixAChimeraFour.finiteBranchesVia4_embedding
#check AppendixAChimeraFour.exists_fourCell_embeddingVia
#print axioms AppendixAChimeraFour.exists_fourCell_embeddingVia
#check AppendixAChimeraFour.finiteBranches4
#print axioms AppendixAChimeraFour.finiteBranches4
#check AppendixAChimeraFour.finiteBranches4_mem
#print axioms AppendixAChimeraFour.finiteBranches4_mem
#check AppendixAChimeraFour.finiteBranches4_branchModel
#print axioms AppendixAChimeraFour.finiteBranches4_branchModel
#check AppendixAChimeraFour.finiteBranches4_embedding
#print axioms AppendixAChimeraFour.finiteBranches4_embedding
#check AppendixAChimeraFour.exists_fourCell_embedding
#print axioms AppendixAChimeraFour.exists_fourCell_embedding
