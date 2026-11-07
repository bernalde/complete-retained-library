module

public import AppendixAChimeraTwoCell

@[expose] public section

/-! Transport the typed two-cell construction into the accepted finite graph
embedding interface. The Fintype equivalences are arbitrary bijections; no
identification with the displayed hand numbering is used. -/
noncomputable section
namespace AppendixAChimera
attribute [local instance] Classical.propDecidable

theorem target_adjacent_iff (a b : Fin 16) :
    AppendixA.adjacent targetEdges a b ↔ Hardware (physEquiv.symm a) (physEquiv.symm b) := by
  simp only [AppendixA.adjacent, targetEdges, Finset.mem_filter, Finset.mem_univ, true_and]
  exact ⟨fun h => h.elim id (fun hr => hardware_symmetric hr), Or.inl⟩

theorem hardware_transport (u v : Phys) :
    AppendixA.adjacent targetEdges (physEquiv u) (physEquiv v) ↔ Hardware u v := by
  simpa using target_adjacent_iff (physEquiv u) (physEquiv v)

theorem quotient_symmetric_bridge (D : Sample) : Symmetric (QuotientAdj D) := by
  rintro j l ⟨hne,u,hu,v,hv,he⟩
  exact ⟨hne.symm,v,hv,u,hu,he.symm⟩

theorem logical_adjacent_iff (D : Sample) (j l : Fin (logicalCount D)) :
    AppendixA.adjacent (logicalEdges D) j l ↔
      QuotientAdj D ((labelEquiv D).symm j) ((labelEquiv D).symm l) := by
  simp only [AppendixA.adjacent, logicalEdges, Finset.mem_filter, Finset.mem_univ, true_and]
  exact ⟨fun h => h.elim id (fun hr => quotient_symmetric_bridge D hr), Or.inl⟩

theorem logical_transport (D : Sample) (j l : Label D) :
    AppendixA.adjacent (logicalEdges D) (labelEquiv D j) (labelEquiv D l) ↔
      QuotientAdj D j l := by
  simpa using logical_adjacent_iff D (labelEquiv D j) (labelEquiv D l)

theorem finiteBranches_mem (D : Sample) (j : Fin (logicalCount D)) (u : Phys) :
    physEquiv u ∈ finiteBranches D j ↔ u ∈ branch D ((labelEquiv D).symm j) := by
  simp [finiteBranches]

theorem connected_pair_bridge {n : ℕ} (E : Finset (Fin n × Fin n)) (u v : Fin n)
    (h : u = v ∨ AppendixA.adjacent E u v) : AppendixA.connected E {u,v} := by
  intro a ha b hb
  rcases h with rfl | h
  · simp only [Finset.insert_eq_of_mem (Finset.mem_singleton_self u), Finset.mem_singleton] at ha hb
    subst a
    subst b
    exact Relation.ReflTransGen.refl
  · simp only [Finset.mem_insert, Finset.mem_singleton] at ha hb
    rcases ha with rfl | rfl <;> rcases hb with rfl | rfl
    · exact Relation.ReflTransGen.refl
    · exact Relation.ReflTransGen.single ⟨by simp, by simp, h⟩
    · exact Relation.ReflTransGen.single ⟨by simp, by simp, AppendixA.adjacent_symmetric E h⟩
    · exact Relation.ReflTransGen.refl

theorem finiteBranches_connected (D : Sample) (j : Fin (logicalCount D)) :
    AppendixA.connected targetEdges (finiteBranches D j) := by
  rcases branch_pair D ((labelEquiv D).symm j) with ⟨u,v,hpair,h⟩
  simp only [finiteBranches, hpair, Finset.image_insert, Finset.image_singleton]
  apply connected_pair_bridge
  exact h.imp (congrArg physEquiv) ((hardware_transport u v).mpr)

theorem finiteBranches_branchModel (D : Sample) :
    AppendixATheory.BranchModel targetEdges (logicalEdges D) 2 (finiteBranches D) := by
  refine ⟨?_, ?_, ?_⟩
  · intro j
    refine ⟨(branch_nonempty D _).image physEquiv, ?_, finiteBranches_connected D j⟩
    exact Finset.card_image_le.trans (branch_card D _)
  · intro j l hne
    apply Finset.disjoint_left.mpr
    intro p hp hq
    rcases Finset.mem_image.mp hp with ⟨u,hu,hu'⟩
    rcases Finset.mem_image.mp hq with ⟨v,hv,hv'⟩
    have huv : u = v := physEquiv.injective (hu'.trans hv'.symm)
    subst v
    exact Finset.disjoint_left.mp (branch_disjoint D _ _
      (fun heq => hne ((labelEquiv D).symm.injective heq))) hu hv
  · intro j l h
    rcases quotient_covered D ((logical_adjacent_iff D j l).mp h) with ⟨u,hu,v,hv,he⟩
    exact ⟨physEquiv u, Finset.mem_image.mpr ⟨u,hu,rfl⟩,
      physEquiv v, Finset.mem_image.mpr ⟨v,hv,rfl⟩, (hardware_transport u v).mpr he⟩

theorem finiteBranches_embedding (D : Sample) :
    AppendixATheory.Embedding targetEdges (logicalEdges D) 2
      (AppendixATheory.alphaOfFibers (finiteBranches D)) := by
  apply (AppendixATheory.embedding_iff_branchModel _ _ _ _).mpr
  simpa using finiteBranches_branchModel D

theorem exists_twoCell_embedding (D : Sample) :
    ∃ A : AppendixATheory.Alpha 16 (logicalCount D),
      AppendixATheory.fiber A = finiteBranches D ∧
      AppendixATheory.Embedding targetEdges (logicalEdges D) 2 A :=
  (AppendixATheory.branchModel_alpha_projection _ _ _ _).mpr (finiteBranches_branchModel D)

theorem logicalEdges_loopFree (D : Sample) : AppendixATheory.LoopFree (logicalEdges D) := by
  intro j h
  exact ((logical_adjacent_iff D j j).mp h).1 rfl

end AppendixAChimera

#print axioms AppendixAChimera.target_adjacent_iff
#print axioms AppendixAChimera.hardware_transport
#print axioms AppendixAChimera.quotient_symmetric_bridge
#print axioms AppendixAChimera.logical_adjacent_iff
#print axioms AppendixAChimera.logical_transport
#print axioms AppendixAChimera.finiteBranches_mem
#print axioms AppendixAChimera.connected_pair_bridge
#print axioms AppendixAChimera.finiteBranches_connected
#print axioms AppendixAChimera.finiteBranches_branchModel
#print axioms AppendixAChimera.finiteBranches_embedding
#print axioms AppendixAChimera.exists_twoCell_embedding
#print axioms AppendixAChimera.logicalEdges_loopFree
