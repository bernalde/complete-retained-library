module

public import AppendixAChimeraRestriction
public import MigrationListChain
public import AppendixAChimeraFourBridge

@[expose] public section

/-! Actual finite active quotients and their injective decoding into a full
construction. No embedding or cap hypothesis enters the sampled graph data. -/
noncomputable section
namespace AppendixAChimeraConstruction
open AppendixAChimera AppendixAChimeraFour
attribute [local instance] Classical.propDecidable

abbrev Position := Bool × Bool

def cellPoint (p : Position) (x : Cell) : Phys4 :=
  (p.1, if p.2 then second x else first x)

structure ActiveData (V : Type*) [Fintype V] (R : V → V → Prop) where
  U : Finset V
  H : Finset (V × V)
  S : Finset (V × V)
  sampled_hardware : ∀ e ∈ H, R e.1 e.2
  sampled_active : ∀ e ∈ H, e.1 ∈ U ∧ e.2 ∈ U
  selected_sampled : ∀ e ∈ S, Adj H e.1 e.2
  selected_active : ∀ e ∈ S, e.1 ∈ U ∧ e.2 ∈ U

namespace ActiveData
variable {V : Type*} [Fintype V] {R : V → V → Prop}

def component (D : ActiveData V R) (x : V) : Finset V :=
  D.U.filter (fun y => Relation.ReflTransGen (Adj D.S) x y)

def Label (D : ActiveData V R) :=
  {C : Finset V // ∃ x ∈ D.U, C = D.component x}

instance (D : ActiveData V R) : Fintype D.Label := by
  unfold Label
  infer_instance

theorem reach_symmetric (D : ActiveData V R) :
    Symmetric (Relation.ReflTransGen (Adj D.S)) := by
  letI : Std.Symm (Adj D.S) := ⟨fun _ _ h => h.symm⟩
  exact Relation.ReflTransGen.stdSymm.symm

theorem component_eq_of_reach (D : ActiveData V R) {x y : V}
    (h : Relation.ReflTransGen (Adj D.S) x y) : D.component x = D.component y := by
  ext z
  simp only [component, Finset.mem_filter]
  exact and_congr_right (fun _ => ⟨fun hz => (D.reach_symmetric h).trans hz,
    fun hz => h.trans hz⟩)

theorem component_eq_at (D : ActiveData V R) (C : D.Label) {x : V}
    (hx : x ∈ C.val) : C.val = D.component x := by
  rcases C.property with ⟨r, _, hC⟩
  rw [hC] at hx ⊢
  exact D.component_eq_of_reach (Finset.mem_filter.mp hx).2

theorem component_nonempty (D : ActiveData V R) (C : D.Label) : C.val.Nonempty := by
  rcases C.property with ⟨x,hx,hC⟩
  refine ⟨x, ?_⟩
  rw [hC]
  exact Finset.mem_filter.mpr ⟨hx, Relation.ReflTransGen.refl⟩

theorem component_reachable (D : ActiveData V R) (C : D.Label) {x y : V}
    (hx : x ∈ C.val) (hy : y ∈ C.val) : Relation.ReflTransGen (Adj D.S) x y := by
  rw [D.component_eq_at C hx] at hy
  exact (Finset.mem_filter.mp hy).2

theorem component_active (D : ActiveData V R) (C : D.Label) {x : V}
    (hx : x ∈ C.val) : x ∈ D.U := by
  rw [D.component_eq_at C hx] at hx
  exact (Finset.mem_filter.mp hx).1

theorem component_eq_of_shared (D : ActiveData V R) (C K : D.Label) {x : V}
    (hx : x ∈ C.val) (hk : x ∈ K.val) : C = K := by
  apply Subtype.ext
  exact (D.component_eq_at C hx).trans (D.component_eq_at K hk).symm

def originalLabel (D : ActiveData V R) (x : V) (hx : x ∈ D.U) : D.Label :=
  ⟨D.component x, x, hx, rfl⟩

theorem originalLabel_mem (D : ActiveData V R) (x : V) (hx : x ∈ D.U) :
    x ∈ (D.originalLabel x hx).val :=
  Finset.mem_filter.mpr ⟨hx, Relation.ReflTransGen.refl⟩

theorem originalLabel_exact (D : ActiveData V R) (C : D.Label) (x : V) :
    x ∈ C.val ↔ ∃ hx : x ∈ D.U, D.originalLabel x hx = C := by
  constructor
  · intro hx
    exact ⟨D.component_active C hx,
      D.component_eq_of_shared _ _ (D.originalLabel_mem x _) hx⟩
  · rintro ⟨hx,rfl⟩
    exact D.originalLabel_mem x hx

theorem originalLabel_surjective (D : ActiveData V R) (C : D.Label) :
    ∃ x, ∃ hx : x ∈ D.U, D.originalLabel x hx = C := by
  rcases D.component_nonempty C with ⟨x,hx⟩
  exact ⟨x,(D.originalLabel_exact C x).mp hx⟩

def QuotientAdj (D : ActiveData V R) (C K : D.Label) : Prop :=
  C ≠ K ∧ ∃ x ∈ C.val, ∃ y ∈ K.val, Adj D.H x y

theorem quotient_symmetric (D : ActiveData V R) : Symmetric D.QuotientAdj := by
  rintro C K ⟨hne,x,hx,y,hy,h⟩
  exact ⟨hne.symm,y,hy,x,hx,h.symm⟩

def count (D : ActiveData V R) : ℕ := Fintype.card D.Label
def labelEquiv (D : ActiveData V R) : D.Label ≃ Fin D.count := Fintype.equivFin _
def logicalEdges (D : ActiveData V R) : Finset (Fin D.count × Fin D.count) :=
  Finset.univ.filter (fun e => D.QuotientAdj (D.labelEquiv.symm e.1) (D.labelEquiv.symm e.2))

theorem logical_adjacent_iff (D : ActiveData V R) (i j : Fin D.count) :
    AppendixA.adjacent D.logicalEdges i j ↔
      D.QuotientAdj (D.labelEquiv.symm i) (D.labelEquiv.symm j) := by
  simp only [AppendixA.adjacent, logicalEdges, Finset.mem_filter, Finset.mem_univ, true_and]
  exact ⟨fun h => h.elim id (fun h => D.quotient_symmetric h), Or.inl⟩

def repr (D : ActiveData V R) (C : D.Label) : V := Classical.choose (D.component_nonempty C)
theorem repr_mem (D : ActiveData V R) (C : D.Label) : D.repr C ∈ C.val :=
  Classical.choose_spec (D.component_nonempty C)

def decode {J : Type*} (D : ActiveData V R) (f : V → J) (C : D.Label) : J := f (D.repr C)

theorem decode_at {J : Type*} (D : ActiveData V R) (f : V → J)
    (hf : ∀ x y, f x = f y ↔ Relation.ReflTransGen (Adj D.S) x y)
    (C : D.Label) {x : V} (hx : x ∈ C.val) : D.decode f C = f x :=
  (hf _ _).mpr (D.component_reachable C (D.repr_mem C) hx)

theorem decode_injective {J : Type*} (D : ActiveData V R) (f : V → J)
    (hf : ∀ x y, f x = f y ↔ Relation.ReflTransGen (Adj D.S) x y) :
    Function.Injective (D.decode f) := by
  intro C K h
  apply Subtype.ext
  exact (D.component_eq_at C (D.repr_mem C)).trans
    ((D.component_eq_of_reach ((hf _ _).mp h)).trans
      (D.component_eq_at K (D.repr_mem K)).symm)

/-- Exact partial-domain completion transport. Labels are mapped, while physical
branches are left intact. The caller must prove the full realization's selected
connectivity correspondence, not assume an arbitrary quotient injection. -/
theorem embedding_of_full_model {J : Type*} [Fintype J] {n k : ℕ}
    (D : ActiveData V R) (hR : Symmetric R) (e : V ≃ Fin n)
    (E : Finset (Fin n × Fin n))
    (he : ∀ x y, AppendixA.adjacent E (e x) (e y) ↔ R x y)
    (f : V → J) (hf : ∀ x y, f x = f y ↔ Relation.ReflTransGen (Adj D.S) x y)
    (B : J → Finset V)
    (hb : ∀ j, (B j).Nonempty ∧ (B j).card ≤ k ∧
      ∀ x ∈ B j, ∀ y ∈ B j,
        Relation.ReflTransGen (fun a b => a ∈ B j ∧ b ∈ B j ∧ R a b) x y)
    (hd : ∀ j l, j ≠ l → Disjoint (B j) (B l))
    (hc : ∀ x y, R x y → ∃ a ∈ B (f x), ∃ b ∈ B (f y), R a b) :
    ∃ A : AppendixATheory.Alpha n D.count,
      AppendixATheory.Embedding E D.logicalEdges k A := by
  let G : Fin D.count → Finset (Fin n) :=
    fun j => (B (D.decode f (D.labelEquiv.symm j))).image e
  have hG : AppendixATheory.BranchModel E D.logicalEdges k G := by
    refine ⟨?_,?_,?_⟩
    · intro j
      refine ⟨(hb _).1.image e, Finset.card_image_le.trans (hb _).2.1, ?_⟩
      intro a ha b hb'
      rcases Finset.mem_image.mp ha with ⟨x,hx,rfl⟩
      rcases Finset.mem_image.mp hb' with ⟨y,hy,rfl⟩
      apply MigrationListChain.reflTransGen_lift e ?_ ((hb _).2.2 x hx y hy)
      intro u v huv
      exact ⟨Finset.mem_image.mpr ⟨u,huv.1,rfl⟩,
        Finset.mem_image.mpr ⟨v,huv.2.1,rfl⟩,(he u v).mpr huv.2.2⟩
    · intro j l hne
      apply Finset.disjoint_left.mpr
      intro a ha hb'
      rcases Finset.mem_image.mp ha with ⟨x,hx,hxa⟩
      rcases Finset.mem_image.mp hb' with ⟨y,hy,hya⟩
      have hxy := e.injective (hxa.trans hya.symm)
      subst y
      exact Finset.disjoint_left.mp (hd _ _ (fun h => hne
        (D.labelEquiv.symm.injective (D.decode_injective f hf h)))) hx hy
    · intro j l hjl
      rcases (D.logical_adjacent_iff j l).mp hjl with ⟨_,x,hx,y,hy,hxy⟩
      have hr : R x y := hxy.elim (D.sampled_hardware _) (fun h => hR (D.sampled_hardware _ h))
      rcases hc x y hr with ⟨a,ha,b,hb',hab⟩
      rw [← D.decode_at f hf _ hx] at ha
      rw [← D.decode_at f hf _ hy] at hb'
      exact ⟨e a,Finset.mem_image.mpr ⟨a,ha,rfl⟩,
        e b,Finset.mem_image.mpr ⟨b,hb',rfl⟩,(he a b).mpr hab⟩
  rcases (AppendixATheory.branchModel_alpha_projection E D.logicalEdges k G).mpr hG with
    ⟨A,_,hA⟩
  exact ⟨A,hA⟩

end ActiveData

/-- Source-sized input, with arbitrary active vertices and actual sampled
hardware edges. Only two specified distinct cells may have selected edges. -/
structure PlacementSample where
  U : Finset Phys4
  H : Finset (Phys4 × Phys4)
  donor₁ : Position
  donor₂ : Position
  distinct : donor₁ ≠ donor₂
  F : Position → Finset (Fin 4 × Fin 4)
  supported : ∀ p, p ≠ donor₁ → p ≠ donor₂ → F p = ∅
  selected_card : ∀ p, (F p).card ≤ 3
  sampled_hardware : ∀ e ∈ H, Hardware4 e.1 e.2
  sampled_active : ∀ e ∈ H, e.1 ∈ U ∧ e.2 ∈ U
  selected_sampled : ∀ p e, e ∈ F p → Adj H (cellPoint p (false,e.1)) (cellPoint p (true,e.2))

def PlacementSample.selected (D : PlacementSample) : Finset (Phys4 × Phys4) :=
  Finset.univ.biUnion (fun p => (D.F p).image
    (fun e => (cellPoint p (false,e.1),cellPoint p (true,e.2))))

def PlacementSample.activeData (D : PlacementSample) : ActiveData Phys4 Hardware4 where
  U := D.U
  H := D.H
  S := D.selected
  sampled_hardware := D.sampled_hardware
  sampled_active := D.sampled_active
  selected_sampled := by
    intro e he
    rcases Finset.mem_biUnion.mp he with ⟨p,_,he⟩
    rcases Finset.mem_image.mp he with ⟨q,hq,rfl⟩
    exact D.selected_sampled p q hq
  selected_active := by
    intro e he
    rcases Finset.mem_biUnion.mp he with ⟨p,_,he⟩
    rcases Finset.mem_image.mp he with ⟨q,hq,rfl⟩
    rcases D.selected_sampled p q hq with h | h
    · exact D.sampled_active _ h
    · exact (D.sampled_active _ h).symm

end AppendixAChimeraConstruction
