module

public import AppendixASelectors

@[expose] public section

/-! Kernel-checked finite controls for the vertex cap, disconnected ambient
pairs, and selectable paths in a cycle. No graph computation is an oracle. -/
open scoped BigOperators
namespace AppendixAPaths.Controls

theorem small_cap_catalogue_empty {n : ℕ} (E : Finset (Fin n × Fin n))
    (k : ℕ) (hk : k < 2) (a b : Fin n) : catalogue E k a b = ∅ := by
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro p hp
  have hh := interior_card_add_two_le hp
  omega

theorem connected_empty {n : ℕ} (E : Finset (Fin n × Fin n)) :
    AppendixA.connected E ∅ := by
  intro a ha; simp at ha

theorem empty_fiber_full_selector {n : ℕ} (E : Finset (Fin n × Fin n)) (k : ℕ) :
    ∃ g, FullSelectorRows E ∅ k g := by
  exact (full_selector_exists_iff_connected E ∅ k (by simp)).mpr (connected_empty E)

theorem connected_singleton {n : ℕ} (E : Finset (Fin n × Fin n)) (a : Fin n) :
    AppendixA.connected E {a} := by
  intro b hb c hc
  have hb' : b = a := Finset.mem_singleton.mp hb
  have hc' : c = a := Finset.mem_singleton.mp hc
  subst b; subst c; exact .refl

theorem singleton_cap_one_full_selector {n : ℕ} (E : Finset (Fin n × Fin n))
    (a : Fin n) : ∃ g, FullSelectorRows E {a} 1 g := by
  exact (full_selector_exists_iff_connected E {a} 1 (by simp)).mpr (connected_singleton E a)

theorem empty_domain_check : connectedCheck (∅ : Finset (Fin 0 × Fin 0)) ∅ = true := by decide

theorem singleton_check : connectedCheck (∅ : Finset (Fin 1 × Fin 1)) {0} = true := by decide

def lineEdges : Finset (Fin 3 × Fin 3) := {(0,1),(1,2)}
def linePath : NodupVertices 3 := ⟨[0,1,2],by decide⟩

theorem linePath_mem : linePath ∈ catalogue lineEdges 3 0 2 := by
  apply (mem_catalogue _ _ _ _ _).mpr
  decide
theorem linePath_vertices : linePath.val.length = 3 := rfl
theorem line_two_edges : linePath.val.length - 1 = 2 := rfl
theorem line_no_direct_edge : ¬ AppendixA.adjacent lineEdges 0 2 := by
  unfold AppendixA.adjacent lineEdges
  decide

theorem two_vertex_path_is_edge {n : ℕ} {E : Finset (Fin n × Fin n)}
    {a b : Fin n} {p : NodupVertices n} (hp : p ∈ catalogue E 2 a b) :
    AppendixA.adjacent E a b := by
  obtain ⟨hne,ha,hb,hchain,hlen⟩ := (mem_catalogue E 2 a b p).mp hp
  cases hl : p.val with
  | nil => simp [hl] at ha
  | cons x xs =>
    have hx : x = a := by simpa [hl] using ha
    subst x
    cases xs with
    | nil =>
      have he : a = b := by simpa [hl] using hb
      exact False.elim (hne he)
    | cons y ys =>
      cases ys with
      | nil =>
        have hy : y = b := by simpa [hl] using hb
        subst y
        simpa [hl, List.isChain_pair] using hchain
      | cons z zs =>
        simp only [hl,List.length_cons] at hlen
        omega

theorem no_edge_two_vertex_catalogue {n : ℕ} (E : Finset (Fin n × Fin n))
    (a b : Fin n) (h : ¬ AppendixA.adjacent E a b) : catalogue E 2 a b = ∅ := by
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro p hp
  exact h (two_vertex_path_is_edge hp)

theorem line_no_two_vertex_path : catalogue lineEdges 2 0 2 = ∅ :=
  no_edge_two_vertex_catalogue lineEdges 0 2 line_no_direct_edge

theorem distance_exact_cap_excluded (g : Gamma 3) :
    ¬ StaticPairRows lineEdges {0,2} 2 g := by
  intro h
  have hp := (static_rows_selected_pair h (by decide : (0 : Fin 3) ≠ 2)
    (by decide) (by decide)).1
  rw [line_no_two_vertex_path] at hp
  exact Finset.not_nonempty_empty hp

theorem line_connected_check : connectedCheck lineEdges Finset.univ = true := by
  apply (connectedCheck_eq_true_iff _ _).mpr
  intro a ha b hb
  fin_cases a <;> fin_cases b
  all_goals solve
    | exact .refl
    | apply Relation.ReflTransGen.single
      refine ⟨Finset.mem_univ _,Finset.mem_univ _,?_⟩
      unfold AppendixA.adjacent lineEdges
      decide
    | apply Relation.ReflTransGen.trans (b := (1 : Fin 3))
      all_goals
        apply Relation.ReflTransGen.single
        refine ⟨Finset.mem_univ _,Finset.mem_univ _,?_⟩
        unfold AppendixA.adjacent lineEdges
        decide

theorem line_connected : AppendixA.connected lineEdges Finset.univ :=
  (connectedCheck_eq_true_iff lineEdges Finset.univ).mp line_connected_check

theorem line_cap_three_full_selector : ∃ g, FullSelectorRows lineEdges Finset.univ 3 g := by
  exact (full_selector_exists_iff_connected lineEdges Finset.univ 3 (by decide)).mpr line_connected

theorem disconnected_ambient_catalogue :
    catalogue (∅ : Finset (Fin 2 × Fin 2)) 2 0 1 = ∅ := by
  apply no_edge_two_vertex_catalogue
  simp [AppendixA.adjacent]

theorem disconnected_ambient_excluded (g : Gamma 2) :
    ¬ StaticPairRows ∅ Finset.univ 2 g := by
  intro h
  have hp := (static_rows_selected_pair h (by decide : (0 : Fin 2) ≠ 1)
    (Finset.mem_univ _) (Finset.mem_univ _)).1
  rw [disconnected_ambient_catalogue] at hp
  exact Finset.not_nonempty_empty hp

theorem disconnected_check :
    connectedCheck (∅ : Finset (Fin 2 × Fin 2)) Finset.univ = false := by
  cases he : connectedCheck (∅ : Finset (Fin 2 × Fin 2)) Finset.univ
  · rfl
  · have hc := (connectedCheck_eq_true_iff _ _).mp he
    have hs := (full_selector_exists_iff_connected ∅ (Finset.univ : Finset (Fin 2)) 2 (by decide)).mpr hc
    obtain ⟨g,hg⟩ := hs
    exact False.elim (disconnected_ambient_excluded g hg.1.2)

def edgePath : NodupVertices 2 := ⟨[0,1],by decide⟩
theorem edgePath_mem : edgePath ∈ catalogue {(0,1)} 2 0 1 := by
  apply (mem_catalogue _ _ _ _ _).mpr
  decide

theorem literal_lower_can_equal_zero :
    1 - ((2 : ℝ) - 1) +
      (∑ v ∈ interior (0 : Fin 2) 1 edgePath, selected Finset.univ v) = 0 := by
  norm_num [interior,edgePath]

def cycleEdges : Finset (Fin 4 × Fin 4) := {(0,1),(1,2),(2,3),(3,0)}
def cycleFirst : NodupVertices 4 := ⟨[0,1,2],by decide⟩
def cycleSecond : NodupVertices 4 := ⟨[0,3,2],by decide⟩

theorem cycle_first_mem : cycleFirst ∈ catalogue cycleEdges 4 0 2 := by
  apply (mem_catalogue _ _ _ _ _).mpr
  decide
theorem cycle_second_mem : cycleSecond ∈ catalogue cycleEdges 4 0 2 := by
  apply (mem_catalogue _ _ _ _ _).mpr
  decide
theorem cycle_paths_distinct : cycleFirst ≠ cycleSecond := by decide
theorem cycle_first_contained : Contains Finset.univ cycleFirst := by intro v hv; exact Finset.mem_univ v
theorem cycle_second_contained : Contains Finset.univ cycleSecond := by intro v hv; exact Finset.mem_univ v
theorem cycle_nonadjacent : ¬ AppendixA.adjacent cycleEdges 0 2 := by
  unfold AppendixA.adjacent cycleEdges
  decide
theorem cycle_connected_check : connectedCheck cycleEdges Finset.univ = true := by
  apply (connectedCheck_eq_true_iff _ _).mpr
  intro a ha b hb
  fin_cases a <;> fin_cases b
  all_goals solve
    | exact .refl
    | apply Relation.ReflTransGen.single
      refine ⟨Finset.mem_univ _,Finset.mem_univ _,?_⟩
      unfold AppendixA.adjacent cycleEdges
      decide
    | apply Relation.ReflTransGen.trans (b := (1 : Fin 4))
      all_goals
        apply Relation.ReflTransGen.single
        refine ⟨Finset.mem_univ _,Finset.mem_univ _,?_⟩
        unfold AppendixA.adjacent cycleEdges
        decide
    | apply Relation.ReflTransGen.trans (b := (0 : Fin 4))
      all_goals
        apply Relation.ReflTransGen.single
        refine ⟨Finset.mem_univ _,Finset.mem_univ _,?_⟩
        unfold AppendixA.adjacent cycleEdges
        decide

theorem cycle_connected : AppendixA.connected cycleEdges Finset.univ :=
  (connectedCheck_eq_true_iff cycleEdges Finset.univ).mp cycle_connected_check

theorem cycle_full_selector_extension : ∃ g, FullSelectorRows cycleEdges Finset.univ 4 g := by
  exact (full_selector_exists_iff_connected cycleEdges Finset.univ 4 (by decide)).mpr cycle_connected

theorem cycle_exactly_one (g : Gamma 4) (h : FullSelectorRows cycleEdges Finset.univ 4 g) :
    gammaMass cycleEdges 4 0 2 g = 1 :=
  nonadjacent_selected_exactly_one h.1.2 (by decide) (Finset.mem_univ _) (Finset.mem_univ _) cycle_nonadjacent

theorem cycle_cannot_activate_both (g : Gamma 4)
    (h : FullSelectorRows cycleEdges Finset.univ 4 g) :
    ¬ (g 0 2 cycleFirst = true ∧ g 0 2 cycleSecond = true) := by
  rintro ⟨hfirst,hsecond⟩
  have hl := two_active_mass cycle_first_mem cycle_second_mem cycle_paths_distinct hfirst hsecond
  have he := cycle_exactly_one g h
  linarith

/-- This tests the distinct, stronger exact-product reading; it is not used in
the selector projection. Every contained path would have to activate. -/
def AllContainedActive {n : ℕ} (E : Finset (Fin n × Fin n)) (S : Finset (Fin n))
    (k : ℕ) (g : Gamma n) : Prop :=
  ∀ a b p, p ∈ catalogue E k a b → Contains S p → g a b p = true

theorem cycle_all_contained_conflicts_uniqueness (g : Gamma 4) :
    ¬ (FullSelectorRows cycleEdges Finset.univ 4 g ∧ AllContainedActive cycleEdges Finset.univ 4 g) := by
  rintro ⟨hfull,hall⟩
  exact cycle_cannot_activate_both g hfull
    ⟨hall 0 2 cycleFirst cycle_first_mem cycle_first_contained,
      hall 0 2 cycleSecond cycle_second_mem cycle_second_contained⟩

end AppendixAPaths.Controls
