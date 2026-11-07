module

public import AppendixAChimeraRealizations
public import MigrationListChain
public import AppendixAChimeraSymmetry

@[expose] public section

/-! Complete source-sized placement and active-domain closure. The two donor
positions are arbitrary and distinct. The logical graph is the actual selected
edge quotient of sampled active hardware, not a supplied embeddable graph. -/
noncomputable section
namespace AppendixAChimeraConstruction
open AppendixAChimera AppendixAChimeraFour
open AppendixAChimeraSymmetry (Symmetry edgeAction edgeEquiv)
attribute [local instance] Classical.propDecidable

def indexEdge (e : Fin 4 × Fin 4) : Cell × Cell := ((false,e.1),(true,e.2))

def canonicalPosition (b r : Bool) : Position := (r,if b then r else false)

theorem rowEquiv_first (b r : Bool) (x : Cell) :
    rowEquiv b (r,first x) = cellPoint (canonicalPosition b r) x := by
  cases b <;> cases r <;> rfl

theorem canonicalStep_iff (D : Bool → Sample) (b : Bool) (u v : Phys4) :
    canonicalStep D b u v ↔ ∃ r x y, Adj (D r).F x y ∧
      cellPoint (canonicalPosition b r) x = u ∧ cellPoint (canonicalPosition b r) y = v := by
  constructor
  · rintro ⟨hr,x,y,hxy,hx,hy⟩
    refine ⟨((rowEquiv b).symm u).1,x,y,hxy,?_,?_⟩
    · rw [← rowEquiv_first]
      have hu : (((rowEquiv b).symm u).1,first x) = (rowEquiv b).symm u := by
        exact Prod.ext rfl hx.symm
      rw [hu]
      exact (rowEquiv b).apply_symm_apply u
    · rw [← rowEquiv_first]
      have hv : (((rowEquiv b).symm u).1,first y) = (rowEquiv b).symm v := by
        exact Prod.ext hr hy.symm
      rw [hv]
      exact (rowEquiv b).apply_symm_apply v
  · rintro ⟨r,x,y,hxy,rfl,rfl⟩
    rw [← rowEquiv_first,← rowEquiv_first]
    simp only [canonicalStep,Equiv.symm_apply_apply]
    exact ⟨rfl,x,y,hxy,rfl,rfl⟩

def transformedF (D : PlacementSample) (s : Symmetry) (p : Position) : Finset (Cell × Cell) :=
  ((D.F (s.position.symm p)).image indexEdge).image (edgeAction s.flip)

theorem transformedF_canonical (D : PlacementSample) (s : Symmetry) (p : Position)
    (e : Cell × Cell) (he : e ∈ transformedF D s p) : e.1.1 = false ∧ e.2.1 = true := by
  rcases Finset.mem_image.mp he with ⟨a,ha,rfl⟩
  rcases Finset.mem_image.mp ha with ⟨q,_,rfl⟩
  exact AppendixAChimeraSymmetry.edgeAction_canonical s.flip (indexEdge q) ⟨rfl,rfl⟩

theorem transformedF_card (D : PlacementSample) (s : Symmetry) (p : Position) :
    (transformedF D s p).card ≤ 3 :=
  Finset.card_image_le.trans (Finset.card_image_le.trans (D.selected_card _))

def normalizedSample (D : PlacementSample) (s : Symmetry) (b : Bool) : Sample4 :=
  fullSample (fun r => transformedF D s (canonicalPosition b r))
    (fun _ => transformedF_canonical D s _) (fun _ => transformedF_card D s _)

def mappedSelected (D : PlacementSample) (s : Symmetry) : Finset (Phys4 × Phys4) :=
  D.selected.image (fun e => (s.physical e.1,s.physical e.2))

theorem mappedSelected_transport (D : PlacementSample) (s : Symmetry) (u v : Phys4) :
    Adj (mappedSelected D s) (s.physical u) (s.physical v) ↔ Adj D.selected u v := by
  simp only [Adj,mappedSelected,Finset.mem_image,Prod.mk.injEq]
  constructor
  · rintro (⟨e,he,hu,hv⟩ | ⟨e,he,hv,hu⟩)
    · have h1 := s.physical.injective hu
      have h2 := s.physical.injective hv
      exact Or.inl ((show e = (u,v) from Prod.ext h1 h2) ▸ he)
    · have h1 := s.physical.injective hv
      have h2 := s.physical.injective hu
      exact Or.inr ((show e = (v,u) from Prod.ext h1 h2) ▸ he)
  · intro h
    rcases h with h | h
    · exact Or.inl ⟨(u,v),h,rfl,rfl⟩
    · exact Or.inr ⟨(v,u),h,rfl,rfl⟩

theorem selected_mem_iff (D : PlacementSample) (u v : Phys4) :
    (u,v) ∈ D.selected ↔ ∃ p e, e ∈ D.F p ∧
      cellPoint p (false,e.1) = u ∧ cellPoint p (true,e.2) = v := by
  simp only [PlacementSample.selected,Finset.mem_biUnion,Finset.mem_univ,true_and,
    Finset.mem_image,Prod.mk.injEq]

/-- The two existing coordinate APIs have identical definition bodies. -/
private theorem symmetry_cellPoint_eq (p : Position) (x : Cell) :
    AppendixAChimeraSymmetry.cellPoint p x = AppendixAChimeraConstruction.cellPoint p x := rfl

theorem mapped_canonical_edge (D : PlacementSample) (s : Symmetry) (p : Position)
    (e : Fin 4 × Fin 4) (he : e ∈ D.F p) :
    Adj (mappedSelected D s)
      (cellPoint (s.position p) (edgeAction s.flip (indexEdge e)).1)
      (cellPoint (s.position p) (edgeAction s.flip (indexEdge e)).2) := by
  have h : Adj (mappedSelected D s)
      (s.physical (cellPoint p (false,e.1))) (s.physical (cellPoint p (true,e.2))) := by
    apply (mappedSelected_transport D s _ _).mpr
    exact Or.inl ((selected_mem_iff D _ _).mpr ⟨p,e,he,rfl,rfl⟩)
  have h1 := s.cell_action p (false,e.1)
  have h2 := s.cell_action p (true,e.2)
  change s.physical (cellPoint p (false,e.1)) = _ at h1
  change s.physical (cellPoint p (true,e.2)) = _ at h2
  rw [h1,h2] at h
  cases hf : s.flip
  · simpa [Adj,hf,edgeAction,indexEdge,symmetry_cellPoint_eq,AppendixAChimeraSymmetry.shoreAction] using h
  · simpa [Adj,hf,edgeAction,indexEdge,symmetry_cellPoint_eq,AppendixAChimeraSymmetry.shoreAction] using h.symm

theorem selected_position_normalized (D : PlacementSample) (s : Symmetry) (b : Bool)
    (hfirst : s.position D.donor₁ = canonicalPosition b false)
    (hsecond : s.position D.donor₂ = canonicalPosition b true)
    {p : Position} {e : Fin 4 × Fin 4} (he : e ∈ D.F p) :
    ∃ r, s.position p = canonicalPosition b r := by
  by_cases hp : p = D.donor₁
  · exact ⟨false,hp ▸ hfirst⟩
  · by_cases hq : p = D.donor₂
    · exact ⟨true,hq ▸ hsecond⟩
    · have := D.supported p hp hq
      simp [this] at he

theorem mappedSelected_rows (D : PlacementSample) (s : Symmetry) (b : Bool)
    (hfirst : s.position D.donor₁ = canonicalPosition b false)
    (hsecond : s.position D.donor₂ = canonicalPosition b true) (u v : Phys4) :
    Adj (mappedSelected D s) u v ↔ canonicalStep (rowSample (normalizedSample D s b)) b u v := by
  rw [canonicalStep_iff]
  constructor
  · intro h
    have hdir : ∀ u v, (u,v) ∈ mappedSelected D s →
        ∃ r x y, Adj ((rowSample (normalizedSample D s b) r).F) x y ∧
          cellPoint (canonicalPosition b r) x = u ∧ cellPoint (canonicalPosition b r) y = v := by
      intro u v huv
      rcases Finset.mem_image.mp huv with ⟨⟨a,c⟩,hac,he⟩
      have ha := congrArg Prod.fst he
      have hc := congrArg Prod.snd he
      rcases (selected_mem_iff D a c).mp hac with ⟨p,e,he',rfl,rfl⟩
      rcases selected_position_normalized D s b hfirst hsecond he' with ⟨r,hr⟩
      have hk : edgeAction s.flip (indexEdge e) ∈ transformedF D s (canonicalPosition b r) := by
        apply Finset.mem_image.mpr
        refine ⟨indexEdge e,Finset.mem_image.mpr ⟨e,?_,rfl⟩,rfl⟩
        simpa [← hr] using he'
      have hpa := s.cell_action p (false,e.1)
      have hpc := s.cell_action p (true,e.2)
      change s.physical (cellPoint p (false,e.1)) = _ at hpa
      change s.physical (cellPoint p (true,e.2)) = _ at hpc
      rw [hr] at hpa hpc
      cases hf : s.flip
      · refine ⟨r,(false,e.1),(true,e.2),Or.inl ?_,?_,?_⟩
        · simpa [normalizedSample,fullSample,transformedF,hf,edgeAction,indexEdge] using hk
        · exact (show cellPoint _ _ = s.physical _ by simpa [hf,symmetry_cellPoint_eq,AppendixAChimeraSymmetry.shoreAction] using hpa.symm).trans ha
        · exact (show cellPoint _ _ = s.physical _ by simpa [hf,symmetry_cellPoint_eq,AppendixAChimeraSymmetry.shoreAction] using hpc.symm).trans hc
      · refine ⟨r,(true,e.1),(false,e.2),Or.inr ?_,?_,?_⟩
        · simpa [normalizedSample,fullSample,hf,edgeAction,indexEdge,
            AppendixAChimeraSymmetry.swapShore] using hk
        · exact (show cellPoint _ _ = s.physical _ by simpa [hf,symmetry_cellPoint_eq,AppendixAChimeraSymmetry.shoreAction,
            AppendixAChimeraSymmetry.swapShore] using hpa.symm).trans ha
        · exact (show cellPoint _ _ = s.physical _ by simpa [hf,symmetry_cellPoint_eq,AppendixAChimeraSymmetry.shoreAction,
            AppendixAChimeraSymmetry.swapShore] using hpc.symm).trans hc
    rcases h with h | h
    · exact hdir u v h
    · rcases hdir v u h with ⟨r,x,y,hxy,hx,hy⟩
      exact ⟨r,y,x,hxy.symm,hy,hx⟩
  · rintro ⟨r,x,y,hxy,rfl,rfl⟩
    have hdir : ∀ x y, (x,y) ∈ transformedF D s (canonicalPosition b r) →
        Adj (mappedSelected D s) (cellPoint (canonicalPosition b r) x)
          (cellPoint (canonicalPosition b r) y) := by
      intro x y h
      rcases Finset.mem_image.mp h with ⟨a,ha,he⟩
      rcases Finset.mem_image.mp ha with ⟨q,hq,rfl⟩
      have h' := mapped_canonical_edge D s (s.position.symm (canonicalPosition b r)) q hq
      have h1 := congrArg Prod.fst he
      have h2 := congrArg Prod.snd he
      simpa only [Equiv.apply_symm_apply,h1,h2] using h'
    rcases hxy with h | h
    · exact hdir x y h
    · exact (hdir y x h).symm

def placementFullModel (D : PlacementSample) : FullModel D.selected 3 := by
  let s := AppendixAChimeraSymmetry.pairNormalizer D.donor₁ D.donor₂
  have hf := AppendixAChimeraSymmetry.pairNormalizer_first D.donor₁ D.donor₂
  by_cases ha : s.position D.donor₂ = (true,false)
  · have hfirst : s.position D.donor₁ = canonicalPosition false false := hf
    have hsecond : s.position D.donor₂ = canonicalPosition false true := ha
    exact (canonicalModel (normalizedSample D s false) false (mappedSelected D s)
      (mappedSelected_rows D s false hfirst hsecond)).pullback s.physical s.hardware
        (mappedSelected_transport D s)
  · have hd : s.position D.donor₂ = (true,true) :=
      (AppendixAChimeraSymmetry.pairNormalizer_second D.donor₁ D.donor₂ D.distinct).resolve_left ha
    have hfirst : s.position D.donor₁ = canonicalPosition true false := hf
    have hsecond : s.position D.donor₂ = canonicalPosition true true := hd
    exact (canonicalModel (normalizedSample D s true) true (mappedSelected D s)
      (mappedSelected_rows D s true hfirst hsecond)).pullback s.physical s.hardware
        (mappedSelected_transport D s)

/-- Every actual active quotient in every source-sized four-cell placement has
a cap-three embedding in the unchanged full 32-vertex hardware. -/
theorem exists_anyPlacement_active_embedding (D : PlacementSample) :
    ∃ A : AppendixATheory.Alpha 32 D.activeData.count,
      AppendixATheory.Embedding targetEdges4 D.activeData.logicalEdges 3 A :=
  (placementFullModel D).active_embedding D.activeData

theorem anyPlacement_logical_restriction (D : PlacementSample) {m : ℕ}
    (L : Finset (Fin m × Fin m)) (f : Fin m → Fin D.activeData.count)
    (hf : Function.Injective f)
    (hL : ∀ j l, AppendixA.adjacent L j l → AppendixA.adjacent D.activeData.logicalEdges (f j) (f l)) :
    ∃ A : AppendixATheory.Alpha 32 m, AppendixATheory.Embedding targetEdges4 L 3 A := by
  rcases exists_anyPlacement_active_embedding D with ⟨A,hA⟩
  rcases hA.exists_restricted f hf hL with ⟨B,_,hB⟩
  exact ⟨B,hB⟩

structure TwoCellSample where
  U : Finset Phys
  H : Finset (Phys × Phys)
  donor : Bool
  F : Finset (Fin 4 × Fin 4)
  selected_card : F.card ≤ 3
  sampled_hardware : ∀ e ∈ H, Hardware e.1 e.2
  sampled_active : ∀ e ∈ H, e.1 ∈ U ∧ e.2 ∈ U
  selected_sampled : ∀ e ∈ F,
    Adj H (orient donor (first (false,e.1))) (orient donor (first (true,e.2)))

def TwoCellSample.selected (D : TwoCellSample) : Finset (Phys × Phys) :=
  D.F.image (fun e => (orient D.donor (first (false,e.1)),orient D.donor (first (true,e.2))))

def TwoCellSample.activeData (D : TwoCellSample) : ActiveData Phys Hardware where
  U := D.U
  H := D.H
  S := D.selected
  sampled_hardware := D.sampled_hardware
  sampled_active := D.sampled_active
  selected_sampled := by
    intro e he
    rcases Finset.mem_image.mp he with ⟨q,hq,rfl⟩
    exact D.selected_sampled q hq
  selected_active := by
    intro e he
    rcases Finset.mem_image.mp he with ⟨q,hq,rfl⟩
    rcases D.selected_sampled q hq with h | h
    · exact D.sampled_active _ h
    · exact (D.sampled_active _ h).symm

def TwoCellSample.full (D : TwoCellSample) : Sample where
  U := Finset.univ
  H := Finset.univ.filter (fun e => Hardware e.1 e.2)
  F := D.F.image indexEdge
  sampled_hardware := by intro e he; exact (Finset.mem_filter.mp he).2
  sampled_active := by rintro ⟨p,q⟩ _; cases p <;> cases q <;> simp [Active]
  selected_sampled := by
    intro e he
    rcases Finset.mem_image.mp he with ⟨q,_,rfl⟩
    apply Or.inl
    apply Finset.mem_filter.mpr
    exact ⟨Finset.mem_univ _, by simp [indexEdge,Hardware]⟩
  selected_active := by simp

theorem TwoCellSample.selected_iff (D : TwoCellSample) (p q : Phys) :
    Adj D.selected p q ↔ ∃ x y : Cell, Adj D.full.F x y ∧
      orient D.donor p = first x ∧ orient D.donor q = first y := by
  constructor
  · intro h
    rcases h with h | h
    · rcases Finset.mem_image.mp h with ⟨e,he,hpq⟩
      have hp := congrArg Prod.fst hpq
      have hq := congrArg Prod.snd hpq
      dsimp only at hp hq
      refine ⟨(false,e.1),(true,e.2),Or.inl (Finset.mem_image.mpr ⟨e,he,rfl⟩),?_,?_⟩
      · rw [← hp,orient_twice]
      · rw [← hq,orient_twice]
    · rcases Finset.mem_image.mp h with ⟨e,he,hpq⟩
      have hq := congrArg Prod.fst hpq
      have hp := congrArg Prod.snd hpq
      dsimp only at hp hq
      refine ⟨(true,e.2),(false,e.1),Or.inr (Finset.mem_image.mpr ⟨e,he,rfl⟩),?_,?_⟩
      · rw [← hp,orient_twice]
      · rw [← hq,orient_twice]
  · rintro ⟨x,y,hxy,hp,hq⟩
    have hp' : p = orient D.donor (first x) := by rw [← hp,orient_twice]
    have hq' : q = orient D.donor (first y) := by rw [← hq,orient_twice]
    rcases hxy with h | h
    · rcases Finset.mem_image.mp h with ⟨e,he,hxy⟩
      have hx := congrArg Prod.fst hxy
      have hy := congrArg Prod.snd hxy
      dsimp only [indexEdge] at hx hy
      exact Or.inl (Finset.mem_image.mpr ⟨e,he,by simpa [indexEdge,hx,hy,hp',hq']⟩)
    · rcases Finset.mem_image.mp h with ⟨e,he,hxy⟩
      have hy := congrArg Prod.fst hxy
      have hx := congrArg Prod.snd hxy
      dsimp only [indexEdge] at hx hy
      exact Or.inr (Finset.mem_image.mpr ⟨e,he,by simpa [indexEdge,hx,hy,hp',hq']⟩)

def TwoCellSample.label (D : TwoCellSample) (p : Phys) : Label D.full :=
  originalLabel D.full (orient D.donor p) (by cases orient D.donor p <;> simp [Active,full])

theorem TwoCellSample.label_exact (D : TwoCellSample) (p q : Phys) :
    D.label p = D.label q ↔ Relation.ReflTransGen (Adj D.selected) p q := by
  unfold label
  rw [originalLabel_eq_iff_selected_physical_reach]
  constructor
  · intro h
    have h' := MigrationListChain.reflTransGen_lift (orient D.donor) (fun a b hab =>
      (D.selected_iff _ _).mpr (by simpa only [orient_twice] using hab)) h
    simpa only [orient_twice] using h'
  · intro h
    exact MigrationListChain.reflTransGen_lift (orient D.donor)
      (fun a b hab => (D.selected_iff a b).mp hab) h

theorem typed_connected_pair {V : Type*} [DecidableEq V] (R : V → V → Prop)
    (hR : Symmetric R) (u v : V) (h : u = v ∨ R u v) :
    ∀ a ∈ ({u,v} : Finset V), ∀ b ∈ ({u,v} : Finset V),
      Relation.ReflTransGen (fun x y => x ∈ ({u,v} : Finset V) ∧
        y ∈ ({u,v} : Finset V) ∧ R x y) a b := by
  intro a ha b hb
  rcases h with rfl | h
  · simp only [Finset.insert_eq_of_mem (Finset.mem_singleton_self u),Finset.mem_singleton] at ha hb
    subst a; subst b
    exact Relation.ReflTransGen.refl
  · simp only [Finset.mem_insert,Finset.mem_singleton] at ha hb
    rcases ha with rfl | rfl <;> rcases hb with rfl | rfl
    · exact Relation.ReflTransGen.refl
    · exact Relation.ReflTransGen.single ⟨by simp,by simp,h⟩
    · exact Relation.ReflTransGen.single ⟨by simp,by simp,hR h⟩
    · exact Relation.ReflTransGen.refl

/-- The active-domain two-cell case also permits either donor cell. The source's
three-edge bound is retained in its data; this reused cap-two proof is stronger. -/
theorem exists_twoCell_active_embedding (D : TwoCellSample) :
    ∃ A : AppendixATheory.Alpha 16 D.activeData.count,
      AppendixATheory.Embedding targetEdges D.activeData.logicalEdges 2 A := by
  let B : Label D.full → Finset Phys := fun j => (branch D.full j).image (orient D.donor)
  apply D.activeData.embedding_of_full_model hardware_symmetric physEquiv targetEdges
    hardware_transport D.label D.label_exact B
  · intro j
    refine ⟨(branch_nonempty D.full j).image _,Finset.card_image_le.trans (branch_card D.full j),?_⟩
    rcases branch_pair D.full j with ⟨u,v,h,hc⟩
    dsimp only [B]
    simp only [h,Finset.image_insert,Finset.image_singleton]
    apply typed_connected_pair Hardware hardware_symmetric
    exact hc.imp (congrArg (orient D.donor)) ((orient_hardware D.donor u v).mpr)
  · intro j l hne
    apply Finset.disjoint_left.mpr
    intro p hp hq
    rcases Finset.mem_image.mp hp with ⟨x,hx,hxp⟩
    rcases Finset.mem_image.mp hq with ⟨y,hy,hyp⟩
    have hxy := orient_injective D.donor (hxp.trans hyp.symm)
    subst y
    exact Finset.disjoint_left.mp (branch_disjoint D.full j l hne) hx hy
  · intro u v huv
    rcases original_hardware_covered D.full (D.label u) (D.label v)
      (originalLabel_mem D.full (orient D.donor u) _)
      (originalLabel_mem D.full (orient D.donor v) _)
      ((orient_hardware D.donor u v).mpr huv) with ⟨a,ha,b,hb,hab⟩
    exact ⟨orient D.donor a,Finset.mem_image.mpr ⟨a,ha,rfl⟩,
      orient D.donor b,Finset.mem_image.mpr ⟨b,hb,rfl⟩,(orient_hardware D.donor a b).mpr hab⟩

theorem twoCell_logical_restriction (D : TwoCellSample) {m : ℕ}
    (L : Finset (Fin m × Fin m)) (f : Fin m → Fin D.activeData.count)
    (hf : Function.Injective f)
    (hL : ∀ j l, AppendixA.adjacent L j l → AppendixA.adjacent D.activeData.logicalEdges (f j) (f l)) :
    ∃ A : AppendixATheory.Alpha 16 m, AppendixATheory.Embedding targetEdges L 3 A := by
  rcases exists_twoCell_active_embedding D with ⟨A,hA⟩
  have hM := ((AppendixATheory.embedding_iff_branchModel _ _ _ _).mp hA).cap_mono (by decide : 2 ≤ 3)
  rcases hM.exists_restricted_embedding f hf hL with ⟨B,_,hB⟩
  exact ⟨B,hB⟩

/-- One combined source-family endpoint, with physical/logical restriction
parameters explicitly quantified for each of the two stated target sizes. -/
theorem source_sized_construction_cap_three :
    (∀ D : TwoCellSample, ∀ m (L : Finset (Fin m × Fin m))
      (f : Fin m → Fin D.activeData.count), Function.Injective f →
      (∀ j l, AppendixA.adjacent L j l → AppendixA.adjacent D.activeData.logicalEdges (f j) (f l)) →
      ∃ A : AppendixATheory.Alpha 16 m, AppendixATheory.Embedding targetEdges L 3 A) ∧
    (∀ D : PlacementSample, ∀ m (L : Finset (Fin m × Fin m))
      (f : Fin m → Fin D.activeData.count), Function.Injective f →
      (∀ j l, AppendixA.adjacent L j l → AppendixA.adjacent D.activeData.logicalEdges (f j) (f l)) →
      ∃ A : AppendixATheory.Alpha 32 m, AppendixATheory.Embedding targetEdges4 L 3 A) :=
  ⟨fun D _ L f hf hL => twoCell_logical_restriction D L f hf hL,
    fun D _ L f hf hL => anyPlacement_logical_restriction D L f hf hL⟩

end AppendixAChimeraConstruction
