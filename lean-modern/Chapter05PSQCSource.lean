module

public import Chapter05PSQCMaster
public import Chapter02PSCSource

@[expose] public section

/-! Source-facing structured quadratic PSC consumers. The only selected
multipliers are those derived from actual fixed-fiber minima and local Slater.
Every row and scale uses that same entry; matching preserves coordinates and
first derivatives, not equality to a hand-picked multiplier vector. -/
noncomputable section
open Set Chapter02
namespace Chapter05.PSQC

variable {p q m l s nw nv : ℕ}

theorem v_convex (d : PSCData p q m l s nw nv) : Convex ℝ d.V := by
  intro x hx y hy a b ha hb hab i
  change d.Vrow i (a • x + b • y) ≤ d.Vbound i
  simp only [map_add, map_smul, smul_eq_mul]
  calc
    a * d.Vrow i x + b * d.Vrow i y ≤ a * d.Vbound i + b * d.Vbound i :=
      add_le_add (mul_le_mul_of_nonneg_left (hx i) ha)
        (mul_le_mul_of_nonneg_left (hy i) hb)
    _ = d.Vbound i := by rw [← add_mul, hab, one_mul]

theorem r_onV (d : PSCData p q m l s nw nv) (hr : ConvexOn ℝ univ d.r) :
    ConvexOn ℝ d.V d.r := hr.subset (subset_univ _) (v_convex d)

theorem t_onV (d : PSCData p q m l s nw nv)
    (ht : ∀ j, ConvexOn ℝ univ (d.t j)) (j : Fin l) :
    ConvexOn ℝ d.V (d.t j) := (ht j).subset (subset_univ _) (v_convex d)

def sourceEntry (d : PSCData p q m l s nw nv)
    (hr : ConvexOn ℝ univ d.r) (ht : ∀ j, ConvexOn ℝ univ (d.t j))
    (a : PSCSourceAnchor d) : PSCEntry d :=
  pscSelectSourceEntry d (r_onV d hr) (t_onV d ht) a

theorem source_entry_matches (d : PSCData p q m l s nw nv)
    (hr : ConvexOn ℝ univ d.r) (ht : ∀ j, ConvexOn ℝ univ (d.t j))
    (a : PSCSourceAnchor d) : pscSourceMatches a (sourceEntry d hr ht a) :=
  psc_select_source_entry_matches d (r_onV d hr) (t_onV d ht) a

def sourceHistory (d : PSCData p q m l s nw nv)
    (hr : ConvexOn ℝ univ d.r) (ht : ∀ j, ConvexOn ℝ univ (d.t j))
    (S : List (PSCSourceAnchor d × ℝ)) : List (PSCEntry d × ℝ) :=
  S.map (fun a => (sourceEntry d hr ht a.1, a.2))

def sourceScalesValid (d : PSCData p q m l s nw nv)
    (hr : ConvexOn ℝ univ d.r) (ht : ∀ j, ConvexOn ℝ univ (d.t j))
    (S : List (PSCSourceAnchor d × ℝ)) : Prop :=
  ∀ a ∈ S, 0 ≤ a.2 ∧ a.2 ≤ Quadratic.safeScale
    (lagrangian d (sourceEntry d hr ht a.1).data) (sourceEntry d hr ht a.1).data.v d.V

theorem source_history_entries (d : PSCData p q m l s nw nv)
    (hr : ConvexOn ℝ univ d.r) (ht : ∀ j, ConvexOn ℝ univ (d.t j))
    (S : List (PSCSourceAnchor d × ℝ)) :
    matchedHistory (sourceHistory d hr ht S) =
      pscSourceHistory d (r_onV d hr) (t_onV d ht) (S.map Prod.fst) := by
  simp [matchedHistory, sourceHistory, pscSourceHistory, sourceEntry, List.map_map]

theorem source_history_matches (d : PSCData p q m l s nw nv)
    (hr : ConvexOn ℝ univ d.r) (ht : ∀ j, ConvexOn ℝ univ (d.t j))
    (S : List (PSCSourceAnchor d × ℝ)) :
    List.Forall₂ pscSourceMatches (S.map Prod.fst)
      (matchedHistory (sourceHistory d hr ht S)) := by
  rw [source_history_entries]
  exact psc_source_history_matches d (r_onV d hr) (t_onV d ht) _

theorem source_history_scales (d : PSCData p q m l s nw nv)
    (hr : ConvexOn ℝ univ d.r) (ht : ∀ j, ConvexOn ℝ univ (d.t j))
    (S : List (PSCSourceAnchor d × ℝ)) :
    (sourceHistory d hr ht S).map Prod.snd = S.map Prod.snd := by
  simp [sourceHistory, List.map_map]

theorem source_history_valid (d : PSCData p q m l s nw nv)
    (hr : ConvexOn ℝ univ d.r) (ht : ∀ j, ConvexOn ℝ univ (d.t j))
    (S : List (PSCSourceAnchor d × ℝ)) (hS : sourceScalesValid d hr ht S) :
    scalesValid d (sourceHistory d hr ht S) := by
  intro ea hea
  obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hea
  exact hS a ha

theorem source_history_comparison (d : PSCData p q m l s nw nv)
    (hr : ConvexOn ℝ univ d.r) (ht : ∀ j, ConvexOn ℝ univ (d.t j))
    (hC2 : ContDiff ℝ 2 d.r) (ht2 : ∀ j, ContDiff ℝ 2 (d.t j))
    (S : List (PSCSourceAnchor d × ℝ)) (hS : sourceScalesValid d hr ht S) :
    let H := sourceHistory d hr ht S
    List.Forall₂ pscSourceMatches (S.map Prod.fst) (matchedHistory H) ∧
      H.map Prod.snd = S.map Prod.snd ∧
      psqcMaster d H ⊆ pscMaster d (matchedHistory H) ∧
      pscProject (psqcMaster d H) ⊆ pscGBDMaster d (matchedHistory H) ∧
      ∀ w v y, d.feasible w v y → pscOriginalPoint d w v y ∈ psqcMaster d H := by
  dsimp only
  have hv := source_history_valid d hr ht S hS
  exact ⟨source_history_matches d hr ht S, source_history_scales d hr ht S,
    master_subset_linear d hr ht hC2 ht2 _ hv,
    projected_master_subset_gbd d hr ht hC2 ht2 _ hv,
    fun w v y hf => original_mem_master d hr ht hC2 ht2 _ hv w v y hf⟩

theorem source_history_attained_order (d : PSCData p q m l s nw nv)
    (hr : ConvexOn ℝ univ d.r) (ht : ∀ j, ConvexOn ℝ univ (d.t j))
    (hC2 : ContDiff ℝ 2 d.r) (ht2 : ∀ j, ContDiff ℝ 2 (d.t j))
    (S : List (PSCSourceAnchor d × ℝ)) (hS : sourceScalesValid d hr ht S)
    (gb : RealVector m × ℝ) (ps qs : PSCPoint p q m)
    (hg : IsMinimizer (pscGBDMaster d (matchedHistory (sourceHistory d hr ht S))) Prod.snd gb)
    (hp : IsMinimizer (pscMaster d (matchedHistory (sourceHistory d hr ht S))) PSCPoint.alpha ps)
    (hq : IsMinimizer (psqcMaster d (sourceHistory d hr ht S)) PSCPoint.alpha qs) :
    gb.2 ≤ ps.alpha ∧ ps.alpha ≤ qs.alpha ∧
      ∀ w v y, d.feasible w v y → qs.alpha ≤ d.objective w v y := by
  have hv := source_history_valid d hr ht S hS
  have ho := attained_value_order d hr ht hC2 ht2 _ hv gb ps qs hg hp hq
  exact ⟨ho.1, ho.2, fun w v y hf =>
    attained_original_bound d hr ht hC2 ht2 _ hv qs hq w v y hf⟩

theorem source_history_attainment (d : PSCData p q m l s nw nv)
    (hr : ConvexOn ℝ univ d.r) (ht : ∀ j, ConvexOn ℝ univ (d.t j))
    (hC2 : ContDiff ℝ 2 d.r) (ht2 : ∀ j, ContDiff ℝ 2 (d.t j))
    (S : List (PSCSourceAnchor d × ℝ)) (hS : sourceScalesValid d hr ht S)
    (hne : S ≠ []) (hcompact : IsCompact (pscRetainedBase d)) :
    ∃ z, IsMinimizer (psqcMaster d (sourceHistory d hr ht S)) PSCPoint.alpha z ∧
      ∀ w v y, d.feasible w v y → z.alpha ≤ d.objective w v y := by
  have hH : sourceHistory d hr ht S ≠ [] := by
    cases S with
    | nil => exact (hne rfl).elim
    | cons a S => simp [sourceHistory]
  obtain ⟨z, hz⟩ := master_attainment d _ hH hcompact
  exact ⟨z, hz, fun w v y hf => attained_original_bound d hr ht hC2 ht2 _
    (source_history_valid d hr ht S hS) z hz w v y hf⟩

/-- A source-only row endpoint uses its actually selected entry and its own
sufficient scale. No equality to a supplied multiplier vector is asserted. -/
theorem source_safe_row (d : PSCData p q m l s nw nv)
    (hr : ConvexOn ℝ univ d.r) (ht : ∀ j, ConvexOn ℝ univ (d.t j))
    (hC2 : ContDiff ℝ 2 d.r) (ht2 : ∀ j, ContDiff ℝ 2 (d.t j))
    (a : PSCSourceAnchor d) :
    let e := sourceEntry d hr ht a
    let α := Quadratic.safeScale (lagrangian d e.data) e.data.v d.V
    pscSourceMatches a e ∧ (0 ≤ α ∧ α ≤ 1) ∧
      ∀ w v y, d.feasible w v y →
        pscRow d e.data w v y ≤ psqcRow d e.data α w v y ∧
        psqcRow d e.data α w v y ≤ d.r v ∧
        fullCut d e.data α w v y ≤ d.objective w v y := by
  dsimp only
  let e := sourceEntry d hr ht a
  have hα := Quadratic.safeScale_bounds (lagrangian_convex d e.data e.kkt hr ht)
    (lagrangian_contDiff d e.data hC2 ht2) e.data.v d.V
  refine ⟨source_entry_matches d hr ht a, hα, ?_⟩
  intro w v y hf
  have hb := row_bounds d e.data e.kkt hr ht hC2 ht2 hα.1 le_rfl w v y hf
  refine ⟨hb.1, hb.2, ?_⟩
  dsimp [fullCut, PSCData.objective]
  linarith [hb.2]

#print axioms source_entry_matches
#print axioms source_history_comparison
#print axioms source_history_attained_order
#print axioms source_history_attainment
#print axioms source_safe_row

end Chapter05.PSQC
