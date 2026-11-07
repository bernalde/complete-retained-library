module

public import AppendixAChimeraBridge

@[expose] public section

/-! Candidate only. A sampled pendant edge with all four couplers.
The accepted Sample, original fibers, quotient and finite target are unchanged.
The optional first A vertices affect only the retained logical isolates.
No assertion identifies this family with the historical random generator. -/
noncomputable section
open scoped BigOperators
namespace AppendixAChimeraMinimum
open AppendixAChimera AppendixATheory
attribute [local instance] Classical.propDecidable

def a (i : Fin 4) : Cell := (false, i)
def b (i : Fin 4) : Cell := (true, i)

structure Domain where
  U : Finset Cell
  hasA : a 0 ∈ U
  hasB : ∀ i, b i ∈ U

def Sampled : Phys → Phys → Prop
  | .inl x, .inl y => (x = a 0 ∧ y = b 0) ∨ (x = b 0 ∧ y = a 0)
  | .inl x, .inr y => x.1 = true ∧ x = y
  | .inr x, .inl y => y.1 = true ∧ y = x
  | .inr x, .inr y => x.1 ≠ y.1

def sampledEdges : Finset (Phys × Phys) :=
  Finset.univ.filter (fun e => Sampled e.1 e.2)

def selectedEdges : Finset (Cell × Cell) := {(a 0, b 0)}

theorem selectedEdges_card : selectedEdges.card = 1 := by simp [selectedEdges]

theorem sampled_symmetric : Symmetric Sampled := by
  intro u v h
  cases u <;> cases v
  · rcases h with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ <;> simp [Sampled]
  · exact h
  · exact h
  · exact Ne.symm h

theorem sampled_hardware {u v : Phys} (h : Sampled u v) : Hardware u v := by
  cases u <;> cases v
  · rcases h with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ <;> simp [Hardware,a,b]
  · exact h
  · exact h
  · exact h

theorem sampled_adj_iff (u v : Phys) : Adj sampledEdges u v ↔ Sampled u v := by
  simp only [Adj,sampledEdges,Finset.mem_filter,Finset.mem_univ,true_and]
  exact ⟨fun h => h.elim id (fun hr => sampled_symmetric hr), Or.inl⟩

theorem b_mem (D : Domain) {x : Cell} (hx : x.1 = true) : x ∈ D.U := by
  rcases x with ⟨s,i⟩
  have hs : s = true := hx
  subst s
  exact D.hasB i

theorem sampled_active (D : Domain) {u v : Phys} (h : Sampled u v) :
    Active D.U u ∧ Active D.U v := by
  cases u with
  | inl x =>
    cases v with
    | inl y =>
      rcases h with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
      · exact ⟨D.hasA,D.hasB 0⟩
      · exact ⟨D.hasB 0,D.hasA⟩
    | inr y => exact ⟨b_mem D h.1,trivial⟩
  | inr x =>
    cases v with
    | inl y => exact ⟨trivial,b_mem D h.1⟩
    | inr y => exact ⟨trivial,trivial⟩

def sample (D : Domain) : Sample where
  U := D.U
  H := sampledEdges
  F := selectedEdges
  sampled_hardware := by
    intro e he
    exact sampled_hardware (Finset.mem_filter.mp he).2
  sampled_active := by
    intro e he
    exact sampled_active D (Finset.mem_filter.mp he).2
  selected_sampled := by
    intro e he
    have heq : e = (a 0,b 0) := Finset.mem_singleton.mp he
    subst e
    exact (sampled_adj_iff _ _).mpr (Or.inl ⟨rfl,rfl⟩)
  selected_active := by
    intro e he
    have heq : e = (a 0,b 0) := Finset.mem_singleton.mp he
    subst e
    exact ⟨D.hasA,D.hasB 0⟩

def collapse (x : Cell) : Cell := if x = a 0 then b 0 else x

@[simp] theorem collapse_b (i : Fin 4) : collapse (b i) = b i := by
  simp [collapse,a,b]

@[simp] theorem collapse_a0 : collapse (a 0) = b 0 := by simp [collapse]

theorem collapse_ne_a0 (x : Cell) : collapse x ≠ a 0 := by
  by_cases h : x = a 0
  · rw [collapse,if_pos h]
    simp [a,b]
  · rw [collapse,if_neg h]
    exact h

@[simp] theorem collapse_idem (x : Cell) : collapse (collapse x) = collapse x := by
  rw [collapse,if_neg (collapse_ne_a0 x)]

theorem collapse_mem (D : Domain) {x : Cell} (hx : x ∈ D.U) : collapse x ∈ D.U := by
  by_cases h : x = a 0
  · simpa [collapse,h] using D.hasB 0
  · simpa [collapse,h] using hx

theorem collapse_eq_iff (x y : Cell) :
    collapse x = collapse y ↔
      x = y ∨ (x = a 0 ∧ y = b 0) ∨ (x = b 0 ∧ y = a 0) := by
  by_cases hx : x = a 0 <;> by_cases hy : y = a 0 <;>
    simp_all [collapse,a,b,eq_comm]

theorem selected_collapse {x y : Cell} (h : Adj selectedEdges x y) :
    collapse x = collapse y := by
  simp only [Adj,selectedEdges,Finset.mem_singleton,Prod.mk.injEq] at h
  rcases h with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ <;> simp

theorem reach_collapse {x y : Cell}
    (h : Relation.ReflTransGen (Adj selectedEdges) x y) : collapse x = collapse y := by
  induction h with
  | refl => rfl
  | tail hxy hyz ih => exact ih.trans (selected_collapse hyz)

theorem collapse_reach {x y : Cell} (h : collapse x = collapse y) :
    Relation.ReflTransGen (Adj selectedEdges) x y := by
  rcases (collapse_eq_iff x y).mp h with rfl | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
  · exact .refl
  · exact .single (Or.inl (by simp [selectedEdges]))
  · exact .single (Or.inr (by simp [selectedEdges]))

set_option backward.isDefEq.respectTransparency false in
theorem mem_component_iff (D : Domain) (x y : Cell) :
    y ∈ component (sample D) x ↔ y ∈ D.U ∧ collapse x = collapse y := by
  simp only [component,sample,Finset.mem_filter]
  exact and_congr_right (fun _ => ⟨reach_collapse,collapse_reach⟩)

theorem component_pair (D : Domain) :
    component (sample D) (a 0) = {a 0,b 0} := by
  ext x
  rw [mem_component_iff,collapse_eq_iff]
  simp only [Finset.mem_insert,Finset.mem_singleton]
  constructor
  · rintro ⟨_,h | ⟨_,h⟩ | ⟨h,_⟩⟩
    · exact Or.inl h.symm
    · exact Or.inr h
    · simp [a,b] at h
  · rintro (rfl | rfl)
    · exact ⟨D.hasA,Or.inl rfl⟩
    · exact ⟨D.hasB 0,Or.inr (Or.inl ⟨trivial,rfl⟩)⟩

theorem component_singleton (D : Domain) (x : Cell) (hx : x ∈ D.U)
    (ha : x ≠ a 0) (hb : x ≠ b 0) : component (sample D) x = {x} := by
  ext y
  rw [mem_component_iff,collapse_eq_iff]
  constructor
  · rintro ⟨_,h | ⟨h,_⟩ | ⟨h,_⟩⟩
    · exact Finset.mem_singleton.mpr h.symm
    · exact (ha h).elim
    · exact (hb h).elim
  · intro hy
    have hyx := Finset.mem_singleton.mp hy
    subst y
    exact ⟨hx,Or.inl rfl⟩

def representativeCell (D : Domain) (C : Component (sample D)) : Cell :=
  collapse (Classical.choose (component_nonempty (sample D) C))

theorem representativeCell_eq (D : Domain) (C : Component (sample D))
    {x : Cell} (hx : x ∈ C.val) : representativeCell D C = collapse x := by
  exact reach_collapse (component_reachable (sample D) C
    (Classical.choose_spec (component_nonempty (sample D) C)) hx)

theorem representativeCell_mem (D : Domain) (C : Component (sample D)) :
    representativeCell D C ∈ C.val := by
  let x := Classical.choose (component_nonempty (sample D) C)
  have hx : x ∈ C.val := Classical.choose_spec (component_nonempty (sample D) C)
  rw [component_eq_at (sample D) C hx,mem_component_iff]
  refine ⟨collapse_mem D (component_mem_active (sample D) C hx), ?_⟩
  exact (collapse_idem x).symm

theorem representativeCell_injective (D : Domain) :
    Function.Injective (representativeCell D) := by
  intro C K h
  exact component_eq_of_shared (sample D) C K (representativeCell_mem D C)
    (by simpa only [h] using representativeCell_mem D K)

def representative (D : Domain) : Label (sample D) → Phys
  | .inl C => first (representativeCell D C)
  | .inr x => second x

def collapsePhys : Phys → Phys
  | .inl x => first (collapse x)
  | .inr x => second x

theorem representative_mem (D : Domain) (j : Label (sample D)) :
    representative D j ∈ originalFiber (sample D) j := by
  cases j with
  | inl C => exact Finset.mem_image.mpr ⟨_,representativeCell_mem D C,rfl⟩
  | inr x => exact Finset.mem_singleton_self _

theorem collapse_of_fiber (D : Domain) {j : Label (sample D)} {p : Phys}
    (hp : p ∈ originalFiber (sample D) j) : collapsePhys p = representative D j := by
  cases j with
  | inl C =>
    rcases Finset.mem_image.mp hp with ⟨x,hx,rfl⟩
    exact congrArg first (representativeCell_eq D C hx).symm
  | inr x =>
    have heq := Finset.mem_singleton.mp hp
    subst p
    rfl

theorem representative_injective (D : Domain) : Function.Injective (representative D) := by
  intro j l h
  exact originalFiber_unique (sample D) (representative_mem D j)
    (by simpa only [h] using representative_mem D l)

theorem representative_ne_drop (D : Domain) (j : Label (sample D)) :
    representative D j ≠ first (a 0) := by
  cases j with
  | inl C => exact fun h => collapse_ne_a0 _ (Sum.inl.inj h)
  | inr x => simp [representative,first,second]

theorem sampled_collapse {u v : Phys} (h : Sampled u v) :
    collapsePhys u = collapsePhys v ∨ Sampled (collapsePhys u) (collapsePhys v) := by
  cases u with
  | inl x =>
    cases v with
    | inl y =>
      rcases h with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ <;> left <;> simp [collapsePhys]
    | inr y =>
      right
      have hx : x ≠ a 0 := by intro he; subst x; simp [Sampled,a] at h
      simpa [collapsePhys,collapse,hx,Sampled] using h
  | inr x =>
    cases v with
    | inl y =>
      right
      have hy : y ≠ a 0 := by intro he; subst y; simp [Sampled,a] at h
      simpa [collapsePhys,collapse,hy,Sampled] using h
    | inr y => exact Or.inr h

theorem quotient_exact (D : Domain) (j l : Label (sample D)) :
    QuotientAdj (sample D) j l ↔
      j ≠ l ∧ Adj sampledEdges (representative D j) (representative D l) := by
  constructor
  · rintro ⟨hne,u,hu,v,hv,he⟩
    refine ⟨hne,?_⟩
    rcases sampled_collapse ((sampled_adj_iff u v).mp he) with h | h
    · rw [collapse_of_fiber D hu,collapse_of_fiber D hv] at h
      exact (hne (representative_injective D h)).elim
    · rw [collapse_of_fiber D hu,collapse_of_fiber D hv] at h
      exact (sampled_adj_iff _ _).mpr h
  · rintro ⟨hne,he⟩
    exact ⟨hne,_,representative_mem D j,_,representative_mem D l,he⟩

def singletonBranches (D : Domain) (j : Fin (logicalCount (sample D))) :
    Finset (Fin 16) := {physEquiv (representative D ((labelEquiv (sample D)).symm j))}

def assignment (D : Domain) : Alpha 16 (logicalCount (sample D)) :=
  alphaOfFibers (singletonBranches D)

theorem singleton_branchModel (D : Domain) (k : ℕ) (hk : 1 ≤ k) :
    BranchModel targetEdges (logicalEdges (sample D)) k (singletonBranches D) := by
  refine ⟨?_,?_,?_⟩
  · intro j
    refine ⟨Finset.singleton_nonempty _,by simpa [singletonBranches] using hk,?_⟩
    simpa [singletonBranches] using connected_pair_bridge targetEdges
      (physEquiv (representative D ((labelEquiv (sample D)).symm j)))
      (physEquiv (representative D ((labelEquiv (sample D)).symm j))) (Or.inl rfl)
  · intro j l hne
    apply Finset.disjoint_left.mpr
    intro p hp hq
    have he := (Finset.mem_singleton.mp hp).symm.trans (Finset.mem_singleton.mp hq)
    exact hne ((labelEquiv (sample D)).symm.injective
      (representative_injective D (physEquiv.injective he)))
  · intro j l h
    have hq := (logical_adjacent_iff (sample D) j l).mp h
    have hs := (sampled_adj_iff _ _).mp ((quotient_exact D _ _).mp hq).2
    exact ⟨_,Finset.mem_singleton_self _,_,Finset.mem_singleton_self _,
      (hardware_transport _ _).mpr (sampled_hardware hs)⟩

theorem assignment_embedding (D : Domain) (k : ℕ) (hk : 1 ≤ k) :
    Embedding targetEdges (logicalEdges (sample D)) k (assignment D) := by
  apply (embedding_iff_branchModel _ _ _ _).mpr
  simpa [assignment] using singleton_branchModel D k hk

theorem assignment_footprint_eq_logical (D : Domain) :
    footprint (assignment D) = logicalCount (sample D) := by
  have he := assignment_embedding D 1 (le_refl _)
  rw [← sum_fiber_card_eq_footprint (assignment D) ((row_card_iff_exclusive _).mp he.1.1)]
  simp [assignment,singletonBranches]

def activeSupport (D : Domain) : Finset Phys :=
  D.U.image first ∪ (Finset.univ : Finset Cell).image second

def usedSupport (D : Domain) : Finset Phys := (activeSupport D).erase (first (a 0))

theorem mem_activeSupport (D : Domain) (p : Phys) :
    p ∈ activeSupport D ↔ Active D.U p := by
  cases p <;> simp [activeSupport,Active,first,second]

theorem original_support_exact (D : Domain) (p : Phys) :
    (∃ j, p ∈ originalFiber (sample D) j) ↔ p ∈ activeSupport D := by
  rw [mem_activeSupport]
  exact ⟨fun ⟨j,hj⟩ => originalFiber_active (sample D) hj,
    fun hp => ⟨originalLabel (sample D) p hp,originalLabel_mem (sample D) p hp⟩⟩

theorem representative_range (D : Domain) (p : Phys) :
    (∃ j, representative D j = p) ↔ p ∈ usedSupport D := by
  constructor
  · rintro ⟨j,rfl⟩
    exact Finset.mem_erase.mpr ⟨representative_ne_drop D j,
      (original_support_exact D _).mp ⟨j,representative_mem D j⟩⟩
  · intro hp
    rcases Finset.mem_erase.mp hp with ⟨hne,ha⟩
    have hactive := (mem_activeSupport D p).mp ha
    refine ⟨originalLabel (sample D) p hactive,?_⟩
    rw [← collapse_of_fiber D (originalLabel_mem (sample D) p hactive)]
    cases p with
    | inl x =>
      have hx : x ≠ a 0 := fun he => hne (congrArg first he)
      simp [collapsePhys,collapse,hx]
    | inr x => rfl

theorem assignment_used_iff (D : Domain) (p : Phys) :
    (∃ j, assignment D (physEquiv p) j = true) ↔ p ∈ usedSupport D := by
  rw [← representative_range]
  constructor
  · rintro ⟨j,hj⟩
    have he : p = representative D ((labelEquiv (sample D)).symm j) := by
      simpa [assignment,alphaOfFibers,singletonBranches] using hj
    exact ⟨_,he.symm⟩
  · rintro ⟨j,rfl⟩
    exact ⟨labelEquiv (sample D) j,by simp [assignment,alphaOfFibers,singletonBranches]⟩

theorem assignment_footprint_eq_used (D : Domain) :
    footprint (assignment D) = (usedSupport D).card := by
  have hset : (Finset.univ.filter (fun i => ∃ j, assignment D i j = true)) =
      (usedSupport D).image physEquiv := by
    ext i
    obtain ⟨p,rfl⟩ := physEquiv.surjective i
    simp [assignment_used_iff]
  rw [footprint,hset,Finset.card_image_of_injective _ physEquiv.injective]

theorem activeSupport_card (D : Domain) : (activeSupport D).card = D.U.card + 8 := by
  have hd : Disjoint (D.U.image first) ((Finset.univ : Finset Cell).image second) := by
    apply Finset.disjoint_left.mpr
    intro p hp hq
    rcases Finset.mem_image.mp hp with ⟨x,_,rfl⟩
    rcases Finset.mem_image.mp hq with ⟨y,_,hbad⟩
    cases hbad
  rw [activeSupport,Finset.card_union_of_disjoint hd]
  rw [Finset.card_image_of_injective _ Sum.inl_injective,
    Finset.card_image_of_injective _ Sum.inr_injective]
  simp [Cell,Fintype.card_prod]

theorem usedSupport_card (D : Domain) : (usedSupport D).card = D.U.card + 7 := by
  have ha : first (a 0) ∈ activeSupport D := (mem_activeSupport D _).mpr D.hasA
  rw [usedSupport,Finset.card_erase_of_mem ha,activeSupport_card]
  omega

theorem logical_count (D : Domain) : logicalCount (sample D) = D.U.card + 7 := by
  rw [← assignment_footprint_eq_logical,assignment_footprint_eq_used,usedSupport_card]

theorem minimum_below_original_support (D : Domain) (k : ℕ) (hk : 1 ≤ k) :
    Embedding targetEdges (logicalEdges (sample D)) k (assignment D) ∧
    footprint (assignment D) = logicalCount (sample D) ∧
    footprint (assignment D) + 1 = (activeSupport D).card ∧
    ∀ B, Embedding targetEdges (logicalEdges (sample D)) k B →
      footprint (assignment D) ≤ footprint B := by
  refine ⟨assignment_embedding D k hk,assignment_footprint_eq_logical D,?_,?_⟩
  · rw [assignment_footprint_eq_used,usedSupport_card,activeSupport_card]
  · intro B hB
    rw [assignment_footprint_eq_logical]
    exact (rowBounds_size_bounds k B hB.1).1

def fullDomain : Domain where
  U := Finset.univ
  hasA := Finset.mem_univ _
  hasB := fun _ => Finset.mem_univ _

def prunedDomain : Domain where
  U := insert (a 0) ((Finset.univ : Finset (Fin 4)).image b)
  hasA := Finset.mem_insert_self _ _
  hasB := fun i => Finset.mem_insert_of_mem (Finset.mem_image.mpr ⟨i,Finset.mem_univ _,rfl⟩)

theorem fullDomain_card : fullDomain.U.card = 8 := by
  simp [fullDomain,Cell,Fintype.card_prod]

theorem prunedDomain_card : prunedDomain.U.card = 5 := by
  have hinj : Function.Injective b := by intro i j h; exact congrArg Prod.snd h
  have ha : a 0 ∉ (Finset.univ : Finset (Fin 4)).image b := by simp [a,b]
  rw [prunedDomain,Finset.card_insert_of_notMem ha,
    Finset.card_image_of_injective _ hinj]
  simp

theorem full_counts : logicalCount (sample fullDomain) = 15 ∧
    (activeSupport fullDomain).card = 16 ∧ footprint (assignment fullDomain) = 15 := by
  refine ⟨?_,?_,?_⟩
  · rw [logical_count,fullDomain_card]
  · rw [activeSupport_card,fullDomain_card]
  · rw [assignment_footprint_eq_used,usedSupport_card,fullDomain_card]

theorem pruned_counts : logicalCount (sample prunedDomain) = 12 ∧
    (activeSupport prunedDomain).card = 13 ∧ footprint (assignment prunedDomain) = 12 := by
  refine ⟨?_,?_,?_⟩
  · rw [logical_count,prunedDomain_card]
  · rw [activeSupport_card,prunedDomain_card]
  · rw [assignment_footprint_eq_used,usedSupport_card,prunedDomain_card]

theorem full_minimum (k : ℕ) (hk : 1 ≤ k) :
    Embedding targetEdges (logicalEdges (sample fullDomain)) k (assignment fullDomain) ∧
    footprint (assignment fullDomain) = 15 ∧
    ∀ B, Embedding targetEdges (logicalEdges (sample fullDomain)) k B → 15 ≤ footprint B := by
  have h := minimum_below_original_support fullDomain k hk
  exact ⟨h.1,full_counts.2.2,fun B hB => full_counts.2.2 ▸ h.2.2.2 B hB⟩

theorem pruned_minimum (k : ℕ) (hk : 1 ≤ k) :
    Embedding targetEdges (logicalEdges (sample prunedDomain)) k (assignment prunedDomain) ∧
    footprint (assignment prunedDomain) = 12 ∧
    ∀ B, Embedding targetEdges (logicalEdges (sample prunedDomain)) k B → 12 ≤ footprint B := by
  have h := minimum_below_original_support prunedDomain k hk
  exact ⟨h.1,pruned_counts.2.2,fun B hB => pruned_counts.2.2 ▸ h.2.2.2 B hB⟩

end AppendixAChimeraMinimum
