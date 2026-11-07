module

public import Chapter03OAExecModel

@[expose] public section

/-! Chronological seed and event tangents, exact source row selection, and
bridges for every past event into the accepted KKT history interface. -/
noncomputable section
open scoped BigOperators
open Chapter02 Chapter03.OAKKT
namespace Chapter03.OAExec
variable {n m l r : ℕ}

def family (d : Data n m l r) (seed : Point n m) (H : List (Event d)) :
    TangentFamily n m l (H.length+1) where
  origin := Fin.cases seed (fun i => (H.get i).anchor)
  selected := Fin.cases Set.univ (fun i => d.selected (H.get i).anchor)
  derivative i := d.Dg (Fin.cases seed (fun i => (H.get i).anchor) i)

def familyDf (d : Data n m l r) (seed : Point n m) (H : List (Event d)) :
    Fin (H.length+1) → Point n m →L[ℝ] ℝ :=
  fun i => d.Df ((family d seed H).origin i)

def Event.rows {d : Data n m l r} (e : Event d) (z : Point n m × ℝ) : Prop :=
  d.f e.anchor + d.Df e.anchor (z.1-e.anchor) ≤ z.2 ∧
    ∀ j ∈ d.selected e.anchor,
      d.model.g j e.anchor + d.Dg e.anchor j (z.1-e.anchor) ≤ 0

def noGoods {d : Data n m l r} (H : List (Event d)) (p : Point n m) : Prop :=
  ∀ e ∈ H, e.restoration ≠ none → p.2 ≠ intCast e.target

def epigraph (d : Data n m l r) (seed : Point n m) (H : List (Event d)) :
    Set (Point n m × ℝ) :=
  Chapter06.EpigraphMaster d.model d.f (family d seed H) (familyDf d seed H) Set.univ

def master (d : Data n m l r) (seed : Point n m) (H : List (Event d)) :
    Set (Point n m × ℝ) := {z | z ∈ epigraph d seed H ∧ noGoods H z.1}

def ValidHistory (d : Data n m l r) (seed : Point n m) (H : List (Event d)) : Prop :=
  seed ∈ d.domain ∧ ∀ e ∈ H, EventValid d e

@[simp] theorem family_seed_origin (d : Data n m l r) (seed : Point n m)
    (H : List (Event d)) : (family d seed H).origin 0 = seed := rfl

@[simp] theorem family_event_origin (d : Data n m l r) (seed : Point n m)
    (H : List (Event d)) (i : Fin H.length) :
    (family d seed H).origin i.succ = (H.get i).anchor := rfl

theorem epigraph_mem_iff (d : Data n m l r) (seed : Point n m)
    (H : List (Event d)) (z : Point n m × ℝ) :
    z ∈ epigraph d seed H ↔ z.1 ∈ d.model.linearRegion ∧
      z.1 ∈ IntegerCylinder (n := n) d.model.lo d.model.hi ∧
      (∀ j, d.model.g j seed + d.Dg seed j (z.1-seed) ≤ 0) ∧
      d.f seed + d.Df seed (z.1-seed) ≤ z.2 ∧ ∀ e ∈ H, e.rows z := by
  constructor
  · rintro ⟨⟨⟨⟨_,hc⟩,hl⟩,hy⟩,hf⟩
    refine ⟨hl,hy,fun j => hc 0 j (Set.mem_univ j),hf 0,?_⟩
    intro e he
    obtain ⟨i,rfl⟩ := List.mem_iff_get.mp he
    exact ⟨hf i.succ,fun j hj => hc i.succ j hj⟩
  · rintro ⟨hl,hy,hg,hf,he⟩
    refine ⟨⟨⟨⟨Set.mem_univ _,?_⟩,hl⟩,hy⟩,?_⟩
    · intro i
      refine Fin.cases ?_ ?_ i
      · exact fun j _ => hg j
      · intro a
        exact (he (H.get a) (List.get_mem H a)).2
    · intro i
      refine Fin.cases hf ?_ i
      intro a
      exact (he (H.get a) (List.get_mem H a)).1

theorem master_mem_iff (d : Data n m l r) (seed : Point n m)
    (H : List (Event d)) (z : Point n m × ℝ) :
    z ∈ master d seed H ↔ z.1 ∈ d.model.linearRegion ∧
      z.1 ∈ IntegerCylinder (n := n) d.model.lo d.model.hi ∧
      (∀ j, d.model.g j seed + d.Dg seed j (z.1-seed) ≤ 0) ∧
      d.f seed + d.Df seed (z.1-seed) ≤ z.2 ∧
      (∀ e ∈ H, e.rows z) ∧ noGoods H z.1 := by
  simp only [master, Set.mem_setOf_eq, epigraph_mem_iff, and_assoc]

theorem master_epigraph_intersection (d : Data n m l r) (seed : Point n m)
    (H : List (Event d)) :
    master d seed H = Chapter06.EpigraphMaster d.model d.f (family d seed H)
      (familyDf d seed H) Set.univ ∩ {z | noGoods H z.1} := rfl

/-- Exact thesis master correspondence: duplicated integer-bound metadata
is supplied by the unchanged all-row seed, without hardening any g row. -/
theorem thesis_master_iff (d : Data n m l 0) (B : IntegerBoundRows d.model)
    (a : Analytic d) (seed : Point n m) (H : List (Event d))
    (hs : seed ∈ d.domain) (z : Point n m × ℝ) :
    z ∈ master d seed H ↔
      z ∈ sourceMaster d.model d.f (family d seed H) (familyDf d seed H) ∧
      noGoods H z.1 := by
  have hh := B.master_iff d.f (family d seed H) (familyDf d seed H) 0 rfl
    (a.derivative_g seed hs) z
  exact and_congr hh.symm Iff.rfl

theorem master_integer {d : Data n m l r} {seed : Point n m} {H : List (Event d)}
    {z : Point n m × ℝ} (hz : z ∈ master d seed H) :
    ∃ y ∈ IntegerBox d.model.lo d.model.hi, z.1.2 = intCast y := hz.1.1.2

theorem master_append (d : Data n m l r) (seed : Point n m)
    (H : List (Event d)) (e : Event d) :
    master d seed (H++[e]) = master d seed H ∩
      {z | e.rows z ∧ (e.restoration ≠ none → z.1.2 ≠ intCast e.target)} := by
  ext z
  simp only [master_mem_iff, Set.mem_inter_iff, Set.mem_setOf_eq, noGoods,
    List.mem_append, List.mem_singleton, or_imp, forall_and]
  simp only [forall_eq]
  tauto

theorem validHistory_append {d : Data n m l r} {seed : Point n m}
    {H : List (Event d)} (hH : ValidHistory d seed H) {e : Event d}
    (he : EventValid d e) : ValidHistory d seed (H++[e]) := by
  refine ⟨hH.1,?_⟩
  intro a ha
  rcases List.mem_append.mp ha with ha | ha
  · exact hH.2 a ha
  · simpa only [List.mem_singleton.mp ha] using he

theorem family_origins_domain {d : Data n m l r} {seed : Point n m}
    {H : List (Event d)} (hH : ValidHistory d seed H) :
    ∀ i, (family d seed H).origin i ∈ d.domain := by
  intro i
  refine Fin.cases hH.1 ?_ i
  intro a
  exact (hH.2 (H.get a) (List.get_mem H a)).1

def eventHistory (d : Data n m l r) (a : Analytic d) (seed : Point n m)
    (H : List (Event d)) (hH : ValidHistory d seed H) (i : Fin H.length) :
    History d.model d.f d.nonlinear (family d seed H) (familyDf d seed H)
      (H.get i).x (intCast (H.get i).target) where
  seed := 0
  current := i.succ
  distinct := by
    intro he
    have hv := congrArg Fin.val he
    change 0 = i.val+1 at hv
    omega
  initial_all := rfl
  current_origin := rfl
  current_selected := rfl
  affine := d.affine_of_not_nonlinear
  g_derivative j k := a.derivative_g _ (family_origins_domain hH j) k
  f_derivative j := a.derivative_f _ (family_origins_domain hH j)

theorem event_master_lower {d : Data n m l r} (a : Analytic d)
    {seed : Point n m} {H : List (Event d)} (hH : ValidHistory d seed H)
    {e : Event d} (he : e ∈ H) (hn : e.restoration = none)
    {z : Point n m × ℝ} (hz : z ∈ master d seed H)
    (hy : z.1.2 = intCast e.target) : d.f e.anchor ≤ z.2 := by
  obtain ⟨i,rfl⟩ := List.mem_iff_get.mp he
  obtain ⟨K⟩ := event_fixed_kkt (hH.2 _ (List.get_mem H i)) hn
  exact fixed_kkt_master_lower (eventHistory d a seed H hH i) K hz.1 hy

theorem noGood_valid {d : Data n m l r} {H : List (Event d)}
    (hH : ∀ e ∈ H, EventValid d e) {p : Point n m} (hp : p ∈ d.original) :
    noGoods H p := by
  intro e he hn hy
  apply event_empty (hH e he) hn
  refine ⟨p.1,?_⟩
  have hpoint : p = (p.1,intCast e.target) := Prod.ext rfl hy
  exact (fiber_original_iff d.model e.target e.target_mem p.1).mpr (hpoint ▸ hp)

theorem original_epigraph_mem {d : Data n m l r} (a : Analytic d)
    {seed : Point n m} {H : List (Event d)} (hH : ValidHistory d seed H)
    {p : Point n m} (hp : p ∈ d.original) : (p,d.f p) ∈ master d seed H := by
  refine ⟨?_,noGood_valid hH.2 hp⟩
  exact source_epigraph_contains_on_domain d.model d.f (family d seed H)
    (familyDf d seed H) d.domain a.convex_g a.convex_f
    (family_origins_domain hH)
    (fun i j _ => a.derivative_g _ (family_origins_domain hH i) j)
    (fun i => a.derivative_f _ (family_origins_domain hH i)) a.original_domain hp

theorem master_lower_bound {d : Data n m l r} (a : Analytic d)
    {seed : Point n m} {H : List (Event d)} (hH : ValidHistory d seed H)
    {z : Point n m × ℝ} (hz : IsMinimizer (master d seed H) Prod.snd z) :
    IsLowerBound d.original d.f z.2 := by
  intro p hp
  exact hz.2 (p,d.f p) (original_epigraph_mem a hH hp)

theorem empty_master_original_empty {d : Data n m l r} (a : Analytic d)
    {seed : Point n m} {H : List (Event d)} (hH : ValidHistory d seed H)
    (he : master d seed H = ∅) : ¬ d.original.Nonempty := by
  rintro ⟨p,hp⟩
  have hm := original_epigraph_mem a hH hp
  rw [he] at hm
  exact hm


end Chapter03.OAExec

#print axioms Chapter03.OAExec.thesis_master_iff
#print axioms Chapter03.OAExec.eventHistory
#print axioms Chapter03.OAExec.event_master_lower
#print axioms Chapter03.OAExec.original_epigraph_mem
