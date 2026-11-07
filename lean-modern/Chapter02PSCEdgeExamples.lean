module

public import Chapter02PSCSource
public import Chapter02PSCAttainment

@[expose] public section

/-! Exact full-model edge controls for qualified PSC: every dimension and row
count is zero, actual source minimum and CQ are inhabited, singleton masters
attain zero, and the empty history leaves all three free heights unbounded.
These controls instantiate the same model, KKT and master definitions used by
the general theorem. -/
noncomputable section
open scoped BigOperators
namespace Chapter02.PSCEdgeExamples

def zeroData : PSCData 0 0 0 0 0 0 0 where
  a := 0
  c := 0
  r := fun _ => 0
  C := 0
  D := 0
  t := 0
  E := 0
  F := 0
  G := 0
  b := 0
  Wrow := 0
  Wbound := 0
  Vrow := 0
  Vbound := 0
  Y := Set.univ

def zeroAnchor : PSCAnchor zeroData where
  w := 0
  v := 0
  y := 0
  Dr := 0
  Dt := 0
  lambda := 0
  mu := 0
  nuW := 0
  nuV := 0

theorem zero_kkt : PSCKKT zeroData zeroAnchor := by
  refine ⟨?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · intro i; exact Fin.elim0 i
  · intro i; exact Fin.elim0 i
  · exact Set.mem_univ _
  · intro i; exact Fin.elim0 i
  · intro i; exact Fin.elim0 i
  · exact hasFDerivAt_const _ _
  · intro i; exact Fin.elim0 i
  · intro i; exact Fin.elim0 i
  · intro i; exact Fin.elim0 i
  · intro i; exact Fin.elim0 i
  · intro i; exact Fin.elim0 i
  · intro i; exact Fin.elim0 i
  · intro i; exact Fin.elim0 i
  · intro i; exact Fin.elim0 i
  · intro i; exact Fin.elim0 i
  · intro dw
    simp [zeroData,zeroAnchor,PSCAnchor.normalW]
  · intro dv
    simp [zeroData,zeroAnchor,PSCAnchor.normalV]

def zeroEntry : PSCEntry zeroData := ⟨zeroAnchor,zero_kkt⟩

/-- The original minimum is proved from the literal feasible problem, before
using any KKT sufficiency or master lower-bound conclusion. -/
theorem zero_original_minimum :
    IsMinimizer (zeroData.fiberFeasible 0) (zeroData.fiberObjective 0)
      (weightedInsert 0 0) := by
  refine ⟨(zeroData.fiberFeasible_insert_iff 0 0 0).mpr
    ⟨(fun i => Fin.elim0 i),(fun i => Fin.elim0 i),
      (fun i => Fin.elim0 i),(fun i => Fin.elim0 i)⟩,?_⟩
  intro z _
  simp [PSCData.fiberObjective,PSCData.objective,zeroData]

theorem zero_slater :
    ∃ z ∈ zeroData.affineFiber 0, ∀ j, zeroData.fiberNonlinear 0 j z < 0 := by
  refine ⟨weightedInsert 0 0,(zeroData.affineFiber_insert_iff 0 0 0).mpr
    ⟨(fun i => Fin.elim0 i),(fun i => Fin.elim0 i),(fun i => Fin.elim0 i)⟩,?_⟩
  intro j
  exact Fin.elim0 j

theorem zero_relative_convexity : ConvexOn ℝ zeroData.V zeroData.r ∧
    ∀ j, ConvexOn ℝ zeroData.V (zeroData.t j) := by
  refine ⟨convexOn_const 0 ?_,fun j => Fin.elim0 j⟩
  intro x hx y hy a b ha hb hab i
  exact Fin.elim0 i

/-- This inhabits every hypothesis of the actual minimum-to-KKT existence
wrapper even when both coordinate blocks and all row families are empty. -/
theorem zero_source_entry_exists :
    ∃ e : PSCEntry zeroData, e.data.w = 0 ∧ e.data.v = 0 ∧ e.data.y = 0 ∧
      e.data.Dr = 0 ∧ e.data.Dt = 0 :=
  psc_entry_exists_of_minimum zeroData 0 0 0 0 0 (Set.mem_univ _)
    zero_relative_convexity.1 zero_relative_convexity.2 (hasFDerivAt_const _ _)
    (fun j => Fin.elim0 j) zero_original_minimum zero_slater

def zeroSourceAnchor : PSCSourceAnchor zeroData where
  w := 0
  v := 0
  y := 0
  Dr := 0
  Dt := 0
  y_mem := Set.mem_univ _
  derivative_r := hasFDerivAt_const _ _
  derivative_t := fun j => Fin.elim0 j
  minimum := zero_original_minimum
  slater := zero_slater

/-- The selected source history is also inhabited, preserving its literal
source coordinates and derivatives at its one list position. -/
theorem zero_source_history_correspondence :
    let H := pscSourceHistory zeroData zero_relative_convexity.1
      zero_relative_convexity.2 [zeroSourceAnchor]
    H.length = 1 ∧ List.Forall₂ pscSourceMatches [zeroSourceAnchor] H := by
  exact ⟨psc_source_history_length _ _ _ _,psc_source_history_matches _ _ _ _⟩

def zeroPoint : PSCPoint 0 0 0 := ⟨0,0,0,0,0⟩

/-- Every full KKT singleton of this zero-dimensional model has the same
literal minima; this covers both the explicit anchor and the derived source
entry without identifying their multiplier choices. -/
theorem zero_singleton_master_minima (e : PSCEntry zeroData) :
    IsMinimizer (pscOAMaster zeroData [e]) PSCPoint.alpha zeroPoint ∧
    IsMinimizer (pscMaster zeroData [e]) PSCPoint.alpha zeroPoint ∧
    IsMinimizer (pscGBDMaster zeroData [e]) Prod.snd (0,0) := by
  have hd : e.data.Dr = 0 := by
    ext x
    have hx : x = 0 := Subsingleton.elim _ _
    change e.data.Dr x = 0
    rw [hx]
    exact map_zero e.data.Dr
  have hb : pscPointBase zeroData zeroPoint := by
    refine ⟨⟨(fun i => Fin.elim0 i),(fun i => Fin.elim0 i),Set.mem_univ _,
      (fun i => Fin.elim0 i)⟩,?_⟩
    simp [zeroPoint,zeroData]
  have ho : zeroPoint ∈ pscOAMaster zeroData [e] := by
    refine ⟨hb,?_⟩
    intro e' he
    have he' : e' = e := by simpa using he
    subst e'
    constructor
    · simp [pscObjectiveTangent,zeroData,zeroPoint,hd]
    · intro j; exact Fin.elim0 j
  have hp := psc_oa_subset zeroData [e] ho
  have hg : ((0 : RealVector 0),(0 : ℝ)) ∈ pscGBDMaster zeroData [e] :=
    psc_projected_subset_gbd zeroData [e] ⟨zeroPoint,hp,rfl,rfl⟩
  refine ⟨⟨ho,?_⟩,⟨hp,?_⟩,⟨hg,?_⟩⟩
  · intro z hz
    have h := (hz.2 e (by simp)).1
    have hb' : 0 ≤ z.beta := by simpa [pscObjectiveTangent,zeroData,hd] using h
    have he : z.alpha = z.beta := by simpa [zeroData] using hz.1.2
    simpa [zeroPoint,he] using hb'
  · intro z hz
    have h := hz.2 e (by simp)
    have hb' : 0 ≤ z.beta := by simpa [pscRow,zeroData] using h
    have he : z.alpha = z.beta := by simpa [zeroData] using hz.1.2
    simpa [zeroPoint,he] using hb'
  · intro z hz
    have h := hz.2 e (by simp)
    simpa [pscGBDRow,PSCData.objective,zeroData] using h

/-- The source-derived history, not merely a disconnected scalar witness,
attains zero in all three actual master definitions. -/
theorem zero_selected_source_master_minima :
    let H := pscSourceHistory zeroData zero_relative_convexity.1
      zero_relative_convexity.2 [zeroSourceAnchor]
    IsMinimizer (pscOAMaster zeroData H) PSCPoint.alpha zeroPoint ∧
    IsMinimizer (pscMaster zeroData H) PSCPoint.alpha zeroPoint ∧
    IsMinimizer (pscGBDMaster zeroData H) Prod.snd (0,0) := by
  exact zero_singleton_master_minima (pscSelectSourceEntry zeroData
    zero_relative_convexity.1 zero_relative_convexity.2 zeroSourceAnchor)

/-- Empty source history leaves actual OA, PSC and cut-only GBD heights
unbounded, despite the same original problem having attained value zero. -/
theorem zero_empty_masters_unbounded :
    (∀ B : ℝ, ∃ z ∈ pscOAMaster zeroData [], z.alpha < B) ∧
    (∀ B : ℝ, ∃ z ∈ pscMaster zeroData [], z.alpha < B) ∧
    (∀ B : ℝ, ∃ z ∈ pscGBDMaster zeroData [], z.2 < B) := by
  have hb : (pscRetainedBase zeroData).Nonempty :=
    ⟨((0,0),0),⟨(fun i => Fin.elim0 i),(fun i => Fin.elim0 i),Set.mem_univ _,
      (fun i => Fin.elim0 i)⟩⟩
  exact ⟨psc_empty_oa_unbounded zeroData hb,psc_empty_master_unbounded zeroData hb,
    psc_empty_gbd_unbounded zeroData ⟨0,Set.mem_univ _⟩⟩

#print axioms zero_kkt
#print axioms zero_original_minimum
#print axioms zero_slater
#print axioms zero_relative_convexity
#print axioms zero_source_entry_exists
#print axioms zero_source_history_correspondence
#print axioms zero_singleton_master_minima
#print axioms zero_selected_source_master_minima
#print axioms zero_empty_masters_unbounded

end Chapter02.PSCEdgeExamples
