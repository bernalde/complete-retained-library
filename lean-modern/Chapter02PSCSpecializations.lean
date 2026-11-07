module

public import Chapter02PSCOrder

@[expose] public section

/-! Representation qualifications for the separable feasible-anchor PSC model.
All projections use a shared witness. Rebuilt source variants have separate
definitions; no equality with a differently aggregated generic master is assumed. -/
noncomputable section
open scoped BigOperators
namespace Chapter02
variable {p q m l s nw nv : ℕ}

theorem psc_project_iff (d : PSCData p q m l s nw nv)
    (H : List (PSCEntry d)) (y : RealVector m) (alpha : ℝ) :
    (y,alpha) ∈ pscProject (pscMaster d H) ↔
      ∃ w v beta, d.base w v y ∧ alpha = d.a w+d.c y+beta ∧
        ∀ e ∈ H, pscRow d e.data w v y ≤ beta := by
  constructor
  · rintro ⟨z,hz,hy,ha⟩
    refine ⟨z.w,z.v,z.beta,?_,?_,?_⟩
    · simpa only [hy] using hz.1.1
    · simpa only [hy,ha] using hz.1.2
    · simpa only [hy] using hz.2
  · rintro ⟨w,v,beta,hb,ha,hh⟩
    exact ⟨⟨w,v,y,beta,alpha⟩,⟨⟨hb,ha⟩,hh⟩,rfl,rfl⟩

theorem psc_history_append (d : PSCData p q m l s nw nv)
    (H : List (PSCEntry d)) (e : PSCEntry d) :
    pscMaster d (H++[e]) = {z ∈ pscMaster d H | pscRow d e.data z.w z.v z.y ≤ z.beta} := by
  ext z
  simp only [pscMaster,Set.mem_setOf_eq,List.mem_append,List.mem_singleton]
  constructor
  · rintro ⟨hb,hh⟩
    exact ⟨⟨hb,fun e he => hh e (Or.inl he)⟩,hh e (Or.inr rfl)⟩
  · rintro ⟨⟨hb,hh⟩,he⟩
    exact ⟨hb,fun f hf => hf.elim (hh f) (fun h => h ▸ he)⟩

/-- Common restrictions may include objective floors, incumbent cutoffs or a
shared projected domain. Outer validity below requires the restriction itself. -/
def pscRestrict (S : Set (PSCPoint p q m)) (Q : RealVector m × ℝ → Prop) :=
  {z ∈ S | Q (z.y,z.alpha)}

theorem psc_restricted_order (d : PSCData p q m l s nw nv)
    (H : List (PSCEntry d)) (Q : RealVector m × ℝ → Prop) :
    pscRestrict (pscOAMaster d H) Q ⊆ pscRestrict (pscMaster d H) Q ∧
    pscProject (pscRestrict (pscMaster d H) Q) ⊆ {ya ∈ pscGBDMaster d H | Q ya} := by
  constructor
  · intro z hz
    exact ⟨psc_oa_subset d H hz.1,hz.2⟩
  · rintro ya ⟨z,hz,hy,ha⟩
    refine ⟨psc_projected_subset_gbd d H ⟨z,hz.1,hy,ha⟩,?_⟩
    simpa only [hy,ha,Prod.eta] using hz.2

theorem psc_original_mem_restricted (d : PSCData p q m l s nw nv)
    (H : List (PSCEntry d)) (hr : ConvexOn ℝ d.V d.r)
    (ht : ∀ j, ConvexOn ℝ d.V (d.t j))
    (w : RealVector p) (v : RealVector q) (y : RealVector m)
    (hf : d.feasible w v y) (Q : RealVector m × ℝ → Prop)
    (hQ : Q (y,d.objective w v y)) :
    pscOriginalPoint d w v y ∈ pscRestrict (pscOAMaster d H) Q :=
  ⟨psc_original_mem_oa d H hr ht w v y hf,hQ⟩

theorem psc_gzero_row (d : PSCData p q m l s nw nv) (hG : ∀ i, d.G i = 0)
    (e : PSCAnchor d) (w : RealVector p) (v : RealVector q) (y : RealVector m) :
    pscRow d e w v y = d.r e.v + ∑ j, e.lambda j*d.nonlinear j w e.v y := by
  simp [pscRow,hG]

theorem psc_gzero_project_iff (d : PSCData p q m l s nw nv)
    (hG : ∀ i, d.G i = 0) (hV : d.V.Nonempty)
    (H : List (PSCEntry d)) (y : RealVector m) (alpha : ℝ) :
    (y,alpha) ∈ pscProject (pscMaster d H) ↔
      ∃ w beta, w ∈ d.W ∧ y ∈ d.Y ∧
        (∀ i, d.E i y+d.F i w-d.b i ≤ 0) ∧
        alpha = d.a w+d.c y+beta ∧
        ∀ e ∈ H, d.r e.data.v+∑ j,e.data.lambda j*d.nonlinear j w e.data.v y ≤ beta := by
  rw [psc_project_iff]
  constructor
  · rintro ⟨w,v,beta,hb,ha,hh⟩
    refine ⟨w,beta,hb.1,hb.2.2.1,?_,ha,?_⟩
    · simpa [PSCData.coupling,hG] using hb.2.2.2
    · simpa only [psc_gzero_row d hG] using hh
  · rintro ⟨w,beta,hw,hy,hc,ha,hh⟩
    obtain ⟨v,hv⟩ := hV
    refine ⟨w,v,beta,⟨hw,hv,hy,?_⟩,ha,?_⟩
    · simpa [PSCData.coupling,hG] using hc
    · simpa only [psc_gzero_row d hG] using hh

/-- Source equation (15): W is the zero-dimensional singleton and there are
no coupling rows. The facet presentation still must admit its sole point. -/
theorem psc_no_w_no_coupling_equality (d : PSCData 0 q m l 0 nw nv)
    (hW : (0 : RealVector 0) ∈ d.W) (hV : d.V.Nonempty)
    (H : List (PSCEntry d)) : pscProject (pscMaster d H) = pscGBDMaster d H := by
  apply Set.Subset.antisymm (psc_projected_subset_gbd d H)
  intro ya hya
  obtain ⟨v,hv⟩ := hV
  rw [show ya = (ya.1,ya.2) from rfl,psc_project_iff]
  refine ⟨0,v,ya.2-d.c ya.1,⟨hW,hv,hya.1,fun i => Fin.elim0 i⟩,?_,?_⟩
  · simp only [map_zero,zero_add]
    ring
  · intro e he
    have hi := psc_gbd_surrogate_identity d e.data e.kkt 0 v ya.1
    have hw : (0 : RealVector 0) = e.data.w := Subsingleton.elim _ _
    have hn : e.data.normalW (0-e.data.w) = 0 := by rw [hw,sub_self,map_zero]
    simp only [map_zero,Finset.univ_eq_empty,Finset.sum_empty,neg_zero,zero_add,hn,
      sub_zero] at hi
    have hb := hya.2 e he
    linarith

def pscRZeroRebuilt (d : PSCData p q m l s nw nv) (H : List (PSCEntry d)) :
    Set (PSCPoint p q m) :=
  {z | d.base z.w z.v z.y ∧ z.beta = 0 ∧ z.alpha = d.a z.w+d.c z.y ∧
    ∀ e ∈ H, pscRow d e.data z.w z.v z.y ≤ 0}

theorem psc_rzero_rebuilt_eq (d : PSCData p q m l s nw nv) (H : List (PSCEntry d)) :
    pscRZeroRebuilt d H = pscBetaZeroMaster d H := by
  ext z
  constructor
  · rintro ⟨hb,h0,ha,hh⟩
    refine ⟨⟨⟨hb,?_⟩,?_⟩,h0⟩
    · simpa only [h0,add_zero] using ha
    · simpa only [h0] using hh
  · rintro ⟨⟨⟨hb,ha⟩,hh⟩,h0⟩
    exact ⟨hb,h0,by simpa only [h0,add_zero] using ha,by simpa only [h0] using hh⟩

theorem psc_rzero_original_mem (d : PSCData p q m l s nw nv)
    (H : List (PSCEntry d)) (hr : d.r = fun _ => 0)
    (ht : ∀ j, ConvexOn ℝ d.V (d.t j))
    (w : RealVector p) (v : RealVector q) (y : RealVector m) (hf : d.feasible w v y) :
    pscOriginalPoint d w v y ∈ pscRZeroRebuilt d H := by
  rw [psc_rzero_rebuilt_eq]
  have hc : ConvexOn ℝ d.V d.r := by
    rw [hr]
    apply convexOn_const
    intro x hx z hz a b ha hb hab i
    change d.Vrow i (a • x+b • z) ≤ d.Vbound i
    simp only [map_add,map_smul,smul_eq_mul]
    calc
      a * d.Vrow i x+b * d.Vrow i z ≤ a * d.Vbound i+b * d.Vbound i :=
        add_le_add (mul_le_mul_of_nonneg_left (hx i) ha)
          (mul_le_mul_of_nonneg_left (hz i) hb)
      _ = d.Vbound i := by rw [← add_mul,hab,one_mul]
  exact ⟨psc_original_mem_psc d H hc ht w v y hf,by simp [pscOriginalPoint,hr]⟩

theorem psc_rzero_rebuilt_subset (d : PSCData p q m l s nw nv) (H : List (PSCEntry d)) :
    pscRZeroRebuilt d H ⊆ pscMaster d H := by
  rw [psc_rzero_rebuilt_eq]
  exact fun _ h => h.1

/-- A linear or affine r need not vanish: its actual tangent equals r. -/
theorem psc_affine_r_derivative (d : PSCData p q m l s nw nv)
    (R : RealVector q →L[ℝ] ℝ) (b : ℝ) (hr : d.r = fun v => R v+b)
    (e : PSCAnchor d) (hk : PSCKKT d e) : e.Dr = R := by
  have hd : HasFDerivAt (fun v => R v+b) R e.v := R.hasFDerivAt.add_const b
  have hd' : HasFDerivAt d.r R e.v := by simpa only [hr] using hd
  exact hk.derivative_r.unique hd'

theorem psc_affine_r_tangent_exact (d : PSCData p q m l s nw nv)
    (R : RealVector q →L[ℝ] ℝ) (b : ℝ) (hr : d.r = fun v => R v+b)
    (e : PSCAnchor d) (hk : PSCKKT d e) (v : RealVector q) :
    pscObjectiveTangent d e v = d.r v := by
  rw [pscObjectiveTangent,psc_affine_r_derivative d R b hr e hk,hr]
  simp only [map_sub]
  ring

theorem psc_empty_V_projection (d : PSCData p q m l s nw nv)
    (hV : d.V = ∅) (H : List (PSCEntry d)) : pscProject (pscMaster d H) = ∅ := by
  ext ya
  simp only [Set.mem_empty_iff_false,iff_false]
  rintro ⟨z,hz,_,_⟩
  have hv := hz.1.1.2.1
  simp only [hV,Set.mem_empty_iff_false] at hv

def pscOriginalEpigraph (d : PSCData p q m l s nw nv) : Set (PSCPoint p q m) :=
  {z | d.feasible z.w z.v z.y ∧ z.alpha=d.a z.w+d.c z.y+z.beta ∧ d.r z.v ≤ z.beta}

theorem psc_original_epigraph_subset_oa (d : PSCData p q m l s nw nv)
    (H : List (PSCEntry d)) (hr : ConvexOn ℝ d.V d.r)
    (ht : ∀ j, ConvexOn ℝ d.V (d.t j)) : pscOriginalEpigraph d ⊆ pscOAMaster d H := by
  intro z hz
  have ho := psc_original_mem_oa d H hr ht z.w z.v z.y hz.1
  refine ⟨⟨hz.1.1,hz.2.1⟩,fun e he => ?_⟩
  exact ⟨(ho.2 e he).1.trans hz.2.2,(ho.2 e he).2⟩

theorem psc_duplicate_history (d : PSCData p q m l s nw nv)
    (H : List (PSCEntry d)) : pscMaster d (H++H) = pscMaster d H := by
  ext z
  simp only [pscMaster,Set.mem_setOf_eq,List.mem_append,or_self]

#print axioms psc_affine_r_derivative
#print axioms psc_affine_r_tangent_exact
#print axioms psc_empty_V_projection
#print axioms psc_original_epigraph_subset_oa
#print axioms psc_duplicate_history
#print axioms psc_project_iff
#print axioms psc_history_append
#print axioms psc_restricted_order
#print axioms psc_original_mem_restricted
#print axioms psc_gzero_row
#print axioms psc_gzero_project_iff
#print axioms psc_no_w_no_coupling_equality
#print axioms psc_rzero_rebuilt_eq
#print axioms psc_rzero_original_mem
#print axioms psc_rzero_rebuilt_subset

end Chapter02
