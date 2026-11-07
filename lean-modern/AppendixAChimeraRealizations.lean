module

public import AppendixAChimeraDiagonal
public import MigrationListChain

@[expose] public section

/-! Uncompiled supporting fragment for author inspection and integration.
The relation uses only selected first-cell edges, not sampled hardware edges. -/
namespace AppendixAChimera

theorem originalLabel_eq_iff_selected_physical_reach (D : Sample)
    (p q : Phys) (hp : Active D.U p) (hq : Active D.U q) :
    originalLabel D p hp = originalLabel D q hq ↔
      Relation.ReflTransGen
        (fun u v => ∃ x y : Cell, Adj D.F x y ∧ u = first x ∧ v = first y)
        p q := by
  classical
  constructor
  · intro h
    cases p with
    | inl x =>
      cases q with
      | inl y =>
        have he : component D x = component D y :=
          congrArg Subtype.val (Sum.inl.inj h)
        have hy : y ∈ component D x := by
          rw [he]
          exact Finset.mem_filter.mpr ⟨hq, Relation.ReflTransGen.refl⟩
        exact MigrationListChain.reflTransGen_lift first
          (fun a b hab => ⟨a, b, hab, rfl, rfl⟩)
          (Finset.mem_filter.mp hy).2
      | inr y => cases h
    | inr x =>
      cases q with
      | inl y => cases h
      | inr y =>
        have he : x = y := Sum.inr.inj h
        subst y
        exact Relation.ReflTransGen.refl
  · intro h
    have preserves : ∀ a b : Phys,
        Relation.ReflTransGen
          (fun u v => ∃ x y : Cell, Adj D.F x y ∧ u = first x ∧ v = first y) a b →
        ∀ ha : Active D.U a, ∃ hb : Active D.U b,
          originalLabel D a ha = originalLabel D b hb := by
      intro a b hab
      induction hab with
      | refl => intro ha; exact ⟨ha,rfl⟩
      | @tail b c hab hbc ih =>
        intro ha
        rcases ih ha with ⟨hb,he⟩
        rcases hbc with ⟨x,y,hxy,rfl,rfl⟩
        have hy : Active D.U (first y) := (selected_active D hxy).2
        refine ⟨hy,he.trans ?_⟩
        apply congrArg Sum.inl
        apply Subtype.ext
        exact component_eq_of_reach D (Relation.ReflTransGen.single hxy)
    exact (preserves p q h hp).choose_spec


end AppendixAChimera

noncomputable section
namespace AppendixAChimeraConstruction
open AppendixAChimera AppendixAChimeraFour
attribute [local instance] Classical.propDecidable

/-- A full physical construction and exact selected-edge decoding. This is an
intermediate proof package, never a premise of the source-family input. -/
structure FullModel (S : Finset (Phys4 × Phys4)) (k : ℕ) where
  J : Type
  finite : Fintype J
  label : Phys4 → J
  branch : J → Finset Phys4
  exact : ∀ u v, label u = label v ↔ Relation.ReflTransGen (Adj S) u v
  nonempty : ∀ j, (branch j).Nonempty
  card : ∀ j, (branch j).card ≤ k
  connected : ∀ j, ∀ u ∈ branch j, ∀ v ∈ branch j,
    Relation.ReflTransGen (fun a b => a ∈ branch j ∧ b ∈ branch j ∧ Hardware4 a b) u v
  disjoint : ∀ j l, j ≠ l → Disjoint (branch j) (branch l)
  covered : ∀ u v, Hardware4 u v → ∃ a ∈ branch (label u), ∃ b ∈ branch (label v), Hardware4 a b

def FullModel.cap_mono {S : Finset (Phys4 × Phys4)} {k l : ℕ}
    (M : FullModel S k) (h : k ≤ l) : FullModel S l :=
  {M with card := fun j => (M.card j).trans h}

theorem FullModel.active_embedding (D : ActiveData Phys4 Hardware4) {k : ℕ}
    (M : FullModel D.S k) :
    ∃ A : AppendixATheory.Alpha 32 D.count,
      AppendixATheory.Embedding targetEdges4 D.logicalEdges k A := by
  letI := M.finite
  exact D.embedding_of_full_model hardware4_symmetric physEquiv4 targetEdges4
    hardware4_transport M.label M.exact M.branch
    (fun j => ⟨M.nonempty j,M.card j,M.connected j⟩) M.disjoint M.covered

def FullModel.pullback {S T : Finset (Phys4 × Phys4)} {k : ℕ}
    (M : FullModel T k) (e : Phys4 ≃ Phys4)
    (he : ∀ u v, Hardware4 (e u) (e v) ↔ Hardware4 u v)
    (hs : ∀ u v, Adj T (e u) (e v) ↔ Adj S u v) : FullModel S k where
  J := M.J
  finite := M.finite
  label := fun u => M.label (e u)
  branch := fun j => (M.branch j).image e.symm
  exact := by
    intro u v
    rw [M.exact]
    constructor
    · intro h
      have h' := MigrationListChain.reflTransGen_lift e.symm (fun a b hab =>
        (hs (e.symm a) (e.symm b)).mp (by simpa using hab)) h
      simpa using h'
    · intro h
      exact MigrationListChain.reflTransGen_lift e (fun a b hab => (hs a b).mpr hab) h
  nonempty := fun j => (M.nonempty j).image e.symm
  card := fun j => Finset.card_image_le.trans (M.card j)
  connected := by
    intro j u hu v hv
    rcases Finset.mem_image.mp hu with ⟨a,ha,rfl⟩
    rcases Finset.mem_image.mp hv with ⟨b,hb,rfl⟩
    apply MigrationListChain.reflTransGen_lift e.symm ?_ (M.connected j a ha b hb)
    intro x y hxy
    exact ⟨Finset.mem_image.mpr ⟨x,hxy.1,rfl⟩,
      Finset.mem_image.mpr ⟨y,hxy.2.1,rfl⟩,
      (he (e.symm x) (e.symm y)).mp (by simpa using hxy.2.2)⟩
  disjoint := by
    intro j l hne
    apply Finset.disjoint_left.mpr
    intro p hp hq
    rcases Finset.mem_image.mp hp with ⟨u,hu,hu'⟩
    rcases Finset.mem_image.mp hq with ⟨v,hv,hv'⟩
    have huv := e.symm.injective (hu'.trans hv'.symm)
    subst v
    exact Finset.disjoint_left.mp (M.disjoint j l hne) hu hv
  covered := by
    intro u v huv
    rcases M.covered (e u) (e v) ((he u v).mpr huv) with ⟨a,ha,b,hb,hab⟩
    exact ⟨e.symm a,Finset.mem_image.mpr ⟨a,ha,rfl⟩,
      e.symm b,Finset.mem_image.mpr ⟨b,hb,rfl⟩,
      (he (e.symm a) (e.symm b)).mp (by simpa using hab)⟩

def RowSelected (D : Bool → Sample) (u v : Phys4) : Prop :=
  u.1 = v.1 ∧ ∃ x y : Cell, Adj (D u.1).F x y ∧ u.2 = first x ∧ v.2 = first y

def fullRowLabel (D : Bool → Sample) (hU : ∀ r, (D r).U = Finset.univ)
    (u : Phys4) : DiagLabel D :=
  ⟨u.1,originalLabel (D u.1) u.2 (by cases u.2 <;> simp [Active,hU])⟩

theorem fullRowLabel_exact (D : Bool → Sample) (hU : ∀ r, (D r).U = Finset.univ)
    (u v : Phys4) : fullRowLabel D hU u = fullRowLabel D hU v ↔
      Relation.ReflTransGen (RowSelected D) u v := by
  constructor
  · rcases u with ⟨r,p⟩; rcases v with ⟨s,q⟩
    intro h
    have hrs : r = s := congrArg Sigma.fst h
    subst s
    have he := eq_of_heq (Sigma.mk.inj_iff.mp h).2
    have hr := (originalLabel_eq_iff_selected_physical_reach (D r) p q _ _).mp he
    exact MigrationListChain.reflTransGen_lift (fun z => (r,z))
      (fun a b hab => ⟨rfl,hab⟩) hr
  · intro h
    induction h with
    | refl => rfl
    | @tail b c hab hbc ih =>
      rcases b with ⟨r,p⟩; rcases c with ⟨s,q⟩
      rcases hbc with ⟨hrs,x,y,hxy,rfl,rfl⟩
      dsimp at hrs
      subst s
      apply ih.trans
      apply congrArg (Sigma.mk r)
      apply (originalLabel_eq_iff_selected_physical_reach (D r) _ _ _ _).mpr
      exact Relation.ReflTransGen.single ⟨x,y,hxy,rfl,rfl⟩

def rowEquiv (diagonal : Bool) : Phys4 ≃ Phys4 where
  toFun u := if diagonal then diagLift u.1 u.2 else u
  invFun u := if diagonal then diagLift u.1 u.2 else u
  left_inv := by
    rintro ⟨r,p⟩
    cases diagonal <;> simp [diagLift]
  right_inv := by
    rintro ⟨r,p⟩
    cases diagonal <;> simp [diagLift]

def canonicalStep (D : Bool → Sample) (diagonal : Bool) (u v : Phys4) : Prop :=
  RowSelected D ((rowEquiv diagonal).symm u) ((rowEquiv diagonal).symm v)

theorem canonicalLabel_exact (D : Bool → Sample) (hU : ∀ r, (D r).U = Finset.univ)
    (b : Bool) (S : Finset (Phys4 × Phys4))
    (hS : ∀ u v, Adj S u v ↔ canonicalStep D b u v) (u v : Phys4) :
    fullRowLabel D hU ((rowEquiv b).symm u) = fullRowLabel D hU ((rowEquiv b).symm v) ↔
      Relation.ReflTransGen (Adj S) u v := by
  rw [fullRowLabel_exact]
  constructor
  · intro h
    have h' := MigrationListChain.reflTransGen_lift (rowEquiv b) (fun a c hac =>
      (hS _ _).mpr (by simpa [canonicalStep] using hac)) h
    simpa using h'
  · intro h
    exact MigrationListChain.reflTransGen_lift (rowEquiv b).symm (fun a c hac => (hS a c).mp hac) h

def fullSample (F : Bool → Finset (Cell × Cell))
    (hcanonical : ∀ r e, e ∈ F r → e.1.1 = false ∧ e.2.1 = true)
    (hcard : ∀ r, (F r).card ≤ 3) : Sample4 where
  H := Finset.univ.filter (fun e => Hardware4 e.1 e.2)
  F := F
  sampled_hardware := by intro e he; exact (Finset.mem_filter.mp he).2
  selected_canonical := hcanonical
  selected_card := hcard
  selected_sampled := by
    intro r e he
    apply Or.inl
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _,?_⟩
    apply (hardware4_same_row_iff r _ _).mpr
    have hc := hcanonical r e he
    simp [Hardware,hc.1,hc.2]

def alignedModel (D : Sample4) (S : Finset (Phys4 × Phys4))
    (hS : ∀ u v, Adj S u v ↔ canonicalStep (rowSample D) false u v) : FullModel S 3 where
  J := Label4 D
  finite := inferInstance
  label := originalLabel4 D
  branch := finalBranch D (repairPlan D)
  exact := by
    intro u v
    exact canonicalLabel_exact (rowSample D) (rowSample_U D) false S hS u v
  nonempty := finalBranch_nonempty D (repairPlan D)
  card := finalBranch_card_le_three D (repairPlan D)
  connected := finalBranch_connected D (repairPlan D)
  disjoint := finalBranch_disjoint D (repairPlan D)
  covered := by
    intro u v huv
    exact final_original_hardware_covered D (repairPlan D)
      (originalLabel4_mem D u) (originalLabel4_mem D v) huv

def diagonalModel (D : Sample4) (S : Finset (Phys4 × Phys4))
    (hS : ∀ u v, Adj S u v ↔ canonicalStep (rowSample D) true u v) : FullModel S 2 where
  J := DiagLabel (rowSample D)
  finite := inferInstance
  label := fun u => fullRowLabel (rowSample D) (rowSample_U D) ((rowEquiv true).symm u)
  branch := diagBranch (rowSample D)
  exact := canonicalLabel_exact (rowSample D) (rowSample_U D) true S hS
  nonempty := diagBranch_nonempty (rowSample D)
  card := diagBranch_card (rowSample D)
  connected := diagBranch_connected (rowSample D)
  disjoint := diagBranch_disjoint (rowSample D)
  covered := by
    intro u v huv
    apply diag_original_hardware_covered (rowSample D) _ _ ?_ ?_ huv
    · refine Finset.mem_image.mpr ⟨((rowEquiv true).symm u).2,?_,?_⟩
      · exact originalLabel_mem _ _ _
      · exact (rowEquiv true).apply_symm_apply u
    · refine Finset.mem_image.mpr ⟨((rowEquiv true).symm v).2,?_,?_⟩
      · exact originalLabel_mem _ _ _
      · exact (rowEquiv true).apply_symm_apply v

def canonicalModel (D : Sample4) (b : Bool) (S : Finset (Phys4 × Phys4))
    (hS : ∀ u v, Adj S u v ↔ canonicalStep (rowSample D) b u v) : FullModel S 3 := by
  cases b
  · exact alignedModel D S hS
  · exact (diagonalModel D S hS).cap_mono (by decide)

end AppendixAChimeraConstruction
