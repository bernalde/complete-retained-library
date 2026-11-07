module

public import Chapter02

@[expose] public section

/-! Candidate exact monotone-composition lift. Domains and graph witnesses are
explicit; no convexity, solver, compactness or assumed projection identity. -/
noncomputable section
namespace Chapter02

def liftingOriginal {X Y : Type*} (D : Set X) (g : X → Y) (h : Y → ℝ)
    (b : ℝ) : Set X := {x | x ∈ D ∧ h (g x) ≤ b}

def liftingSet {X Y : Type*} [Preorder Y] (D : Set X) (E : Set Y)
    (g : X → Y) (h : Y → ℝ) (b : ℝ) : Set (X × Y) :=
  {p | p.1 ∈ D ∧ p.2 ∈ E ∧ g p.1 ≤ p.2 ∧ h p.2 ≤ b}

section Exact
variable {X Y : Type*} [Preorder Y]
variable (D : Set X) (E : Set Y) (g : X → Y) (h : Y → ℝ) (b : ℝ)
variable (hg : Set.MapsTo g D E) (hm : MonotoneOn h E)
include hg

theorem lifting_graph_mem {x : X} (hx : x ∈ liftingOriginal D g h b) :
    (x, g x) ∈ liftingSet D E g h b := ⟨hx.1, hg hx.1, le_rfl, hx.2⟩

include hm

theorem lifting_project_mem {p : X × Y} (hp : p ∈ liftingSet D E g h b) :
    p.1 ∈ liftingOriginal D g h b :=
  ⟨hp.1, (hm (hg hp.1) hp.2.1 hp.2.2.1).trans hp.2.2.2⟩

theorem lifting_projection :
    Prod.fst '' liftingSet D E g h b = liftingOriginal D g h b := by
  ext x
  constructor
  · rintro ⟨p, hp, rfl⟩
    exact lifting_project_mem D E g h b hg hm hp
  · intro hx
    exact ⟨(x,g x), lifting_graph_mem D E g h b hg hx, rfl⟩

theorem lifting_exists_iff (x : X) :
    (∃ y, (x,y) ∈ liftingSet D E g h b) ↔ x ∈ liftingOriginal D g h b := by
  constructor
  · rintro ⟨y,hy⟩; exact lifting_project_mem D E g h b hg hm hy
  · intro hx; exact ⟨g x, lifting_graph_mem D E g h b hg hx⟩

theorem lifting_nonempty_iff :
    (liftingSet D E g h b).Nonempty ↔ (liftingOriginal D g h b).Nonempty := by
  constructor
  · rintro ⟨p,hp⟩; exact ⟨p.1,lifting_project_mem D E g h b hg hm hp⟩
  · rintro ⟨x,hx⟩; exact ⟨(x,g x),lifting_graph_mem D E g h b hg hx⟩

theorem lifting_empty_iff :
    liftingSet D E g h b = ∅ ↔ liftingOriginal D g h b = ∅ := by
  simpa only [Set.not_nonempty_iff_eq_empty] using
    not_congr (lifting_nonempty_iff D E g h b hg hm)

theorem lifting_lowerBound_iff (f : X → ℝ) (v : ℝ) :
    IsLowerBound (liftingSet D E g h b) (fun p => f p.1) v ↔
      IsLowerBound (liftingOriginal D g h b) f v := by
  constructor
  · intro hl x hx; exact hl (x,g x) (lifting_graph_mem D E g h b hg hx)
  · intro hl p hp; exact hl p.1 (lifting_project_mem D E g h b hg hm hp)

theorem lifting_upperWitness_iff (f : X → ℝ) (v : ℝ) :
    HasUpperBoundWitness (liftingSet D E g h b) (fun p => f p.1) v ↔
      HasUpperBoundWitness (liftingOriginal D g h b) f v := by
  constructor
  · rintro ⟨p,hp,hv⟩
    exact ⟨p.1,lifting_project_mem D E g h b hg hm hp,hv⟩
  · rintro ⟨x,hx,hv⟩
    exact ⟨(x,g x),lifting_graph_mem D E g h b hg hx,hv⟩

theorem lifting_minimizer_iff (f : X → ℝ) (p : X × Y) :
    IsMinimizer (liftingSet D E g h b) (fun q => f q.1) p ↔
      p ∈ liftingSet D E g h b ∧ IsMinimizer (liftingOriginal D g h b) f p.1 := by
  constructor
  · intro hp
    refine ⟨hp.1,lifting_project_mem D E g h b hg hm hp.1,?_⟩
    intro x hx
    exact hp.2 (x,g x) (lifting_graph_mem D E g h b hg hx)
  · rintro ⟨hp,hmn⟩
    exact ⟨hp,fun q hq => hmn.2 q.1 (lifting_project_mem D E g h b hg hm hq)⟩

theorem lifting_attainment_iff (f : X → ℝ) :
    (∃ p, IsMinimizer (liftingSet D E g h b) (fun q => f q.1) p) ↔
      ∃ x, IsMinimizer (liftingOriginal D g h b) f x := by
  constructor
  · rintro ⟨p,hp⟩; exact ⟨p.1,((lifting_minimizer_iff D E g h b hg hm f p).mp hp).2⟩
  · rintro ⟨x,hx⟩
    exact ⟨(x,g x),(lifting_minimizer_iff D E g h b hg hm f _).mpr
      ⟨lifting_graph_mem D E g h b hg hx.1,hx⟩⟩

/-- Lubin's scalar composition identity, with its outer/inner naming normalized. -/
theorem lifting_epigraph_composition (p : X × ℝ) :
    p ∈ EpigraphLift D (h ∘ g) ↔
      ∃ y ∈ E, g p.1 ≤ y ∧ h y ≤ p.2 ∧ p.1 ∈ D := by
  constructor
  · rintro ⟨hx,hv⟩; exact ⟨g p.1,hg hx,le_rfl,hv,hx⟩
  · rintro ⟨y,hy,hgy,hyb,hx⟩
    exact ⟨hx,(hm (hg hx) hy hgy).trans hyb⟩

end Exact
end Chapter02

#print axioms Chapter02.lifting_graph_mem
#print axioms Chapter02.lifting_project_mem
#print axioms Chapter02.lifting_projection
#print axioms Chapter02.lifting_exists_iff
#print axioms Chapter02.lifting_nonempty_iff
#print axioms Chapter02.lifting_empty_iff
#print axioms Chapter02.lifting_lowerBound_iff
#print axioms Chapter02.lifting_upperWitness_iff
#print axioms Chapter02.lifting_minimizer_iff
#print axioms Chapter02.lifting_attainment_iff
#print axioms Chapter02.lifting_epigraph_composition
