module

public import Chapter09Nonlinear

@[expose] public section

/-! Nonvacuity and boundary controls on the full graph/slot objects, not scalar surrogates. -/
noncomputable section
open scoped BigOperators
namespace Chapter09.Source.Controls
open Chapter09.Source

def emptyGraph (n : ℕ) : Graph n := ⟨∅,by simp⟩

theorem alpha_le_vertices {n : ℕ} (G : Graph n) (k : ℕ) : alpha G k ≤ n := by
  obtain ⟨S,hS,he⟩ := alpha_attained G k
  rw [← he,← feasible_vertex_card G S hS]
  have hn : (vertices S).card ≤ n := by simpa using Finset.card_le_univ (vertices S)
  exact_mod_cast hn

theorem alpha_of_total_coloring {n k : ℕ} (G : Graph n) (c : Fin n → Option (Fin k))
    (hc : Proper G c) (ht : ∀ i, ∃ r, c i = some r) : alpha G k = n := by
  have hv : vertices (encode c) = Finset.univ := by
    ext i; simp only [Finset.mem_univ,iff_true]; exact (vertices_encode c i).mpr (ht i)
  have hf := (proper_encode_iff G c).mpr hc
  apply le_antisymm (alpha_le_vertices G k)
  have hb := card_le_alpha G (encode c) hf
  rw [← feasible_vertex_card G (encode c) hf,hv] at hb
  simpa using hb

/-- No edges still has an actual nonempty optimum, for every positive color count. -/
theorem empty_graph_alpha (n k : ℕ) (hk : 0 < k) : alpha (emptyGraph n) k = n := by
  apply alpha_of_total_coloring (emptyGraph n) (fun _ => some (⟨0,hk⟩ : Fin k))
  · intro i j h; simpa [Adj,emptyGraph] using h
  · intro i; exact ⟨⟨0,hk⟩,rfl⟩

/-- Enough colors admits every vertex in an arbitrary graph. -/
theorem enough_colors_alpha {n k : ℕ} (G : Graph n) (hnk : n ≤ k) : alpha G k = n := by
  apply alpha_of_total_coloring G (fun i => some (Fin.castLE hnk i))
  · intro i j hij r h
    have he : Fin.castLE hnk i = Fin.castLE hnk j := Option.some.inj (h.1.trans h.2.symm)
    have he' : i = j := Fin.ext (by simpa using congrArg (fun x : Fin k => x.val) he)
    subst j
    exact adj_irrefl G i hij
  · intro i; exact ⟨Fin.castLE hnk i,rfl⟩

/-- Empty vertices cause no hidden nonemptiness assumption in either attained maximum. -/
theorem zero_vertices (G : Graph 0) (k : ℕ) (c1 c2 : ℝ) :
    alpha G k = 0 ∧ qNonlinear G k c1 c2 = 0 := by
  have hS : ∀ S : Finset (Slot 0 k), S = ∅ := by
    intro S; ext u; exact Fin.elim0 u.1
  have he : G.edges = ∅ := by ext e; exact Fin.elim0 e.1
  constructor
  · obtain ⟨S,_,hc⟩ := alpha_attained G k
    simpa [hS S] using hc.symm
  · obtain ⟨S,hs⟩ := qNonlinear_attained G k c1 c2
    rw [hS S] at hs
    simpa [nScore,reward,edgeProducts,orderedProducts,he] using hs.symm

def twoVertexEdge : Graph 2 :=
  ⟨{(0,1)},by
    intro e he
    have h : e = (0,1) := by simpa using he
    subst e
    decide⟩

theorem edge_one_color_alpha : alpha twoVertexEdge 1 = 1 := by
  have hcard : ∀ S : Finset (Slot 2 1), Feasible twoVertexEdge S → S.card ≤ 1 := by
    intro S hS
    have hp : ¬ ((0,0) ∈ S ∧ (1,0) ∈ S) :=
      ((feasible_iff twoVertexEdge S).mp hS).1 (0,1) (by simp [twoVertexEdge]) 0
    apply Finset.card_le_one.mpr
    rintro ⟨i,r⟩ hi ⟨j,p⟩ hj
    fin_cases i <;> fin_cases j <;> fin_cases r <;> fin_cases p
    all_goals first | rfl | exact False.elim (hp ⟨hi,hj⟩) | exact False.elim (hp ⟨hj,hi⟩)
  apply le_antisymm
  · obtain ⟨S,hS,he⟩ := alpha_attained twoVertexEdge 1
    rw [← he]; exact_mod_cast hcard S hS
  · have hf : Feasible twoVertexEdge ({(0,0)} : Finset (Slot 2 1)) := by
      rw [feasible_iff]
      constructor
      · intro e he r; have h : e = (0,1) := by simpa [twoVertexEdge] using he
        subst e; simp
      · intro i r p; exact fun _ _ => Subsingleton.elim r p
    simpa using card_le_alpha twoVertexEdge ({(0,0)} : Finset (Slot 2 1)) hf

/-- The edge endpoint at the unit penalty is a globally maximizing infeasible tie. -/
theorem unit_edge_global_tie (c2 : ℝ) :
    isNMax twoVertexEdge 1 c2 (Finset.univ : Finset (Slot 2 1)) ∧
    ¬ Feasible twoVertexEdge (Finset.univ : Finset (Slot 2 1)) := by
  constructor
  · rw [isNMax_iff,qNonlinear_one_color twoVertexEdge 1 c2 (by norm_num),edge_one_color_alpha]
    norm_num [nScore,reward,edgeProducts,orderedProducts,flag,twoVertexEdge,Fin.sum_univ_two,Fin.sum_univ_one]
  · intro h
    exact ((feasible_iff twoVertexEdge _).mp h).1 (0,1) (by simp [twoVertexEdge]) 0 (by simp)

/-- Strict coefficients have an attained feasible optimum on the same nontrivial edge. -/
theorem strict_edge_optimizer_exists (c1 c2 : ℝ) (hc1 : 1 < c1) :
    ∃ S : Finset (Slot 2 1), isNMax twoVertexEdge c1 c2 S ∧ Feasible twoVertexEdge S ∧ S.card = 1 := by
  obtain ⟨S,hS⟩ := qNonlinear_attained twoVertexEdge 1 c1 c2
  have hm := (isNMax_iff twoVertexEdge c1 c2 S).mpr hS
  obtain ⟨hf,hc⟩ := nonlinear_one_color_strict twoVertexEdge c1 c2 hc1 S hm
  refine ⟨S,hm,hf,?_⟩
  rw [edge_one_color_alpha] at hc
  exact_mod_cast hc

/-- The ordered color boundary has an actual infeasible global maximum even without edges. -/
theorem half_color_global_tie :
    isNMax (emptyGraph 1) 1 (1/2) (Finset.univ : Finset (Slot 1 2)) ∧
    ¬ Feasible (emptyGraph 1) (Finset.univ : Finset (Slot 1 2)) := by
  constructor
  · rw [isNMax_iff,qNonlinear_eq_alpha (emptyGraph 1) 2 1 (1/2) (by norm_num) (by norm_num),
      empty_graph_alpha 1 2 (by decide)]
    norm_num [nScore,reward,edgeProducts,orderedProducts,flag,emptyGraph,Fin.sum_univ_two,Fin.sum_univ_one]
  · intro h
    have he := ((feasible_iff (emptyGraph 1) _).mp h).2 0 0 1 (by simp) (by simp)
    exact (by decide : (0 : Fin 2) ≠ 1) he

end Chapter09.Source.Controls
#print axioms Chapter09.Source.Controls.zero_vertices
#print axioms Chapter09.Source.Controls.empty_graph_alpha
#print axioms Chapter09.Source.Controls.enough_colors_alpha
#print axioms Chapter09.Source.Controls.unit_edge_global_tie
#print axioms Chapter09.Source.Controls.strict_edge_optimizer_exists
#print axioms Chapter09.Source.Controls.half_color_global_tie
