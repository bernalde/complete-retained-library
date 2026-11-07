module

public import Chapter03OAKKTMaps

@[expose] public section

/-! Source-local bounds for the Chapter3 constraint-slack master. Objective
linearizations remain hard. Each selected (history,row) occurrence has its own
nonnegative slack, and the explicit `keep` predicate retains the actual
exclusions. The hard domain is not enlarged by the convexity-domain premise.

This static certificate is conditional on an actual attained penalized
optimizer. It does not assert an optimizer exists, identify solver marginals,
prove exact penalty, or establish finite return. -/
noncomputable section
open scoped BigOperators
open Chapter02
namespace Chapter03.OASoftMaster

variable {n m l r k : ℕ}

/-- Independent constraint occurrence, including repeated rows at different
origins. This makes explicit the article's total slack dimension. -/
abbrev Occurrence (c : TangentFamily n m l k) :=
  {a : Fin k × Fin l // a.2 ∈ c.selected a.1}

/-- Point, hard-objective epigraph variable, and constraint slacks. There is no
objective slack. -/
abbrev Candidate (c : TangentFamily n m l k) :=
  Point n m × ℝ × (Occurrence c → ℝ)

/-- Literal hard-domain, hard-objective, soft-constraint master at a fixed
history, with all retained exclusion conditions represented by `keep`. -/
def master (d : ModelData n m l r) (f : Point n m → ℝ)
    (c : TangentFamily n m l k) (df : Fin k → Point n m →L[ℝ] ℝ)
    (keep : Point n m → Prop) : Set (Candidate c) :=
  {z | z.1 ∈ d.linearRegion ∧ z.1 ∈ IntegerCylinder d.lo d.hi ∧ keep z.1 ∧
    (∀ a, 0 ≤ z.2.2 a) ∧
    (∀ i, f (c.origin i) + df i (z.1 - c.origin i) ≤ z.2.1) ∧
    ∀ a : Occurrence c,
      d.g a.1.2 (c.origin a.1.1) +
        c.derivative a.1.1 a.1.2 (z.1 - c.origin a.1.1) ≤ z.2.2 a}

def penalty {c : TangentFamily n m l k} (w : Occurrence c → ℝ)
    (z : Candidate c) : ℝ := by
  classical
  exact ∑ a : Occurrence c, w a * z.2.2 a

def cost {c : TangentFamily n m l k} (w : Occurrence c → ℝ)
    (z : Candidate c) : ℝ := z.2.1 + penalty w z

def embed (f : Point n m → ℝ) (c : TangentFamily n m l k)
    (p : Point n m) : Candidate c := (p, f p, fun _ => 0)

/-- Bounds are over original feasible points that the retained exclusions
preserve. Global-original bounds require an explicit preservation premise. -/
def remaining (d : ModelData n m l r) (keep : Point n m → Prop) :
    Set (Point n m) := {p | p ∈ d.feasibleOn Set.univ ∧ keep p}

/-- Reuse the accepted hard epigraph certificate through zero constraint slacks. -/
theorem embed_of_hard_epigraph {d : ModelData n m l r} {f : Point n m → ℝ}
    {c : TangentFamily n m l k} {df : Fin k → Point n m →L[ℝ] ℝ}
    {keep : Point n m → Prop} {p : Point n m}
    (hp : (p, f p) ∈ Chapter06.EpigraphMaster d f c df Set.univ) (hk : keep p) :
    embed f c p ∈ master d f c df keep := by
  refine ⟨hp.1.1.2, hp.1.2, hk, ?_, hp.2, ?_⟩
  · intro a
    exact le_rfl
  · intro a
    exact hp.1.1.1.2 a.1.1 a.1.2 a.2

theorem cost_embed {f : Point n m → ℝ} {c : TangentFamily n m l k}
    (w : Occurrence c → ℝ) (p : Point n m) : cost w (embed f c p) = f p := by
  classical
  simp [cost, penalty, embed]

theorem penalty_nonneg {d : ModelData n m l r} {f : Point n m → ℝ}
    {c : TangentFamily n m l k} {df : Fin k → Point n m →L[ℝ] ℝ}
    {keep : Point n m → Prop} {w : Occurrence c → ℝ} {z : Candidate c}
    (hw : ∀ a, 0 ≤ w a) (hz : z ∈ master d f c df keep) : 0 ≤ penalty w z := by
  classical
  exact Finset.sum_nonneg (fun a _ => mul_nonneg (hw a) (hz.2.2.2.1 a))

/-- One bound certificate for the displayed source master. Actual convexity and
ambient derivatives at in-domain origins justify objective-preserving zero-slack
embedding. Comparison with the actual penalized minimum bounds its full cost;
nonnegative weights also bound the same optimizer's stripped alpha. No binary
or affine-in-y restriction, positive-weight assumption, or exclusion policy is
inserted. -/
theorem source_soft_master_bounds (d : ModelData n m l r) (f : Point n m → ℝ)
    (c : TangentFamily n m l k) (df : Fin k → Point n m →L[ℝ] ℝ)
    (keep : Point n m → Prop) (D : Set (Point n m))
    (hg : ∀ j, ConvexOn ℝ D (d.g j)) (hf : ConvexOn ℝ D f)
    (ha : ∀ i, c.origin i ∈ D)
    (hdg : ∀ i j, j ∈ c.selected i →
      HasFDerivAt (d.g j) (c.derivative i j) (c.origin i))
    (hdf : ∀ i, HasFDerivAt f (df i) (c.origin i))
    (hcover : d.feasibleOn Set.univ ⊆ D)
    (w : Occurrence c → ℝ) (hw : ∀ a, 0 ≤ w a) (z : Candidate c)
    (hm : IsMinimizer (master d f c df keep) (cost w) z) :
    (∀ p ∈ remaining d keep,
      embed f c p ∈ master d f c df keep ∧ cost w (embed f c p) = f p) ∧
    0 ≤ penalty w z ∧ z.2.1 ≤ cost w z ∧
    IsLowerBound (remaining d keep) f (cost w z) ∧
    IsLowerBound (remaining d keep) f z.2.1 := by
  have he : ∀ p ∈ remaining d keep,
      embed f c p ∈ master d f c df keep ∧ cost w (embed f c p) = f p := by
    intro p hp
    exact ⟨embed_of_hard_epigraph
      (OAKKT.source_epigraph_contains_on_domain d f c df D hg hf ha hdg hdf hcover hp.1)
      hp.2, cost_embed w p⟩
  have hn : 0 ≤ penalty w z := penalty_nonneg hw hm.1
  have haCost : z.2.1 ≤ cost w z := le_add_of_nonneg_right hn
  have hb : IsLowerBound (remaining d keep) f (cost w z) := by
    intro p hp
    calc
      cost w z ≤ cost w (embed f c p) := hm.2 _ (he p hp).1
      _ = f p := (he p hp).2
  exact ⟨he, hn, haCost, hb, fun p hp => haCost.trans (hb p hp)⟩

/-- A global-original bound follows only when every original feasible point
survives the retained exclusion predicate. -/
theorem global_bound_of_preserved {d : ModelData n m l r} {f : Point n m → ℝ}
    {keep : Point n m → Prop} {a : ℝ}
    (hkeep : ∀ p ∈ d.feasibleOn Set.univ, keep p)
    (hb : IsLowerBound (remaining d keep) f a) :
    IsLowerBound (d.feasibleOn Set.univ) f a := by
  intro p hp
  exact hb p ⟨hp, hkeep p hp⟩

end Chapter03.OASoftMaster
