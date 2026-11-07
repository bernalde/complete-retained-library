module

public import Chapter02Model
public import Mathlib.Analysis.Calculus.ContDiff.Defs
public import Mathlib.Analysis.Normed.Group.Bounded
public import Mathlib.Topology.Sequences
public import Mathlib.Topology.MetricSpace.Cauchy
public import Mathlib.Topology.Order.MonotoneConvergence

@[expose] public section

/-! Analytic compactness engine for the Chapter 2 ECP/ESH procedures.
The ECP separation constant is derived from canonical C1 derivatives. The
generic packing and limiting lemmas expose internal analytic interfaces;
source-procedure endpoints must discharge them from retained actual cuts.
No finite zero-tolerance return or whole-point-sequence convergence is asserted.
-/

noncomputable section
open scoped BigOperators Topology
open Filter
namespace Chapter02

section Derivatives
variable {E J : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [Fintype J]

theorem cp_compact_derivative_bound {B : Set E} {g : J → E → ℝ}
    (hB : IsCompact B) (hg : ∀ j, ContDiff ℝ 1 (g j)) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ j q, q ∈ B → ‖fderiv ℝ (g j) q‖ ≤ M := by
  classical
  have hb : ∀ j, ∃ M : ℝ, 0 < M ∧ ∀ q ∈ B, ‖fderiv ℝ (g j) q‖ ≤ M := by
    intro j
    obtain ⟨M, hM, hb⟩ :=
      (hB.image ((hg j).continuous_fderiv (by norm_num))).isBounded.exists_pos_norm_le
    exact ⟨M, hM, fun q hq => hb _ ⟨q, hq, rfl⟩⟩
  choose M hM hb using hb
  refine ⟨∑ j, M j, Finset.sum_nonneg (fun j _ => (hM j).le), ?_⟩
  intro j q hq
  exact (hb j q hq).trans (Finset.single_le_sum (fun k _ => (hM k).le) (Finset.mem_univ j))

theorem ecp_uniform_separation {B : Set E} {g : J → E → ℝ}
    (hB : IsCompact B) (hg : ∀ j, ContDiff ℝ 1 (g j))
    {eps : ℝ} (heps : 0 < eps) :
    ∃ delta : ℝ, 0 < delta ∧ ∀ q ∈ B, ∀ w j,
      eps < g j q →
      g j q + fderiv ℝ (g j) q (w - q) ≤ 0 →
      delta ≤ dist q w := by
  obtain ⟨M, hM, hbound⟩ := cp_compact_derivative_bound hB hg
  have hden : 0 < M + 1 := by linarith
  refine ⟨eps / (M + 1), div_pos heps hden, ?_⟩
  intro q hq w j hviol hcut
  have hneg : fderiv ℝ (g j) q (q - w) = -fderiv ℝ (g j) q (w - q) := by
    rw [← map_neg, neg_sub]
  have h1 : g j q ≤ fderiv ℝ (g j) q (q - w) := by rw [hneg]; linarith
  have h2 : fderiv ℝ (g j) q (q - w) ≤ ‖fderiv ℝ (g j) q‖ * ‖q - w‖ :=
    (le_abs_self _).trans ((fderiv ℝ (g j) q).le_opNorm _)
  have h3 := mul_le_mul_of_nonneg_right (hbound j q hq) (norm_nonneg (q - w))
  apply (div_le_iff₀ hden).mpr
  rw [dist_eq_norm]
  nlinarith [norm_nonneg (q - w)]

end Derivatives

section Packing
variable {E : Type*} [PseudoMetricSpace E]

theorem cp_compact_separated_prefix_bound {B : Set E} (hB : IsCompact B)
    {delta : ℝ} (hdelta : 0 < delta) :
    ∃ N : ℕ, ∀ k : ℕ, ∀ q : Fin k → E,
      (∀ i, q i ∈ B) →
      (∀ i j, i < j → delta ≤ dist (q i) (q j)) → k ≤ N := by
  classical
  obtain ⟨T, hT, hcover⟩ := Metric.totallyBounded_iff.mp hB.totallyBounded
    (delta / 3) (by positivity)
  letI := hT.fintype
  refine ⟨Fintype.card T, ?_⟩
  intro k q hq hsep
  have hc : ∀ i, ∃ c : T, dist (q i) c < delta / 3 := by
    intro i
    obtain ⟨c, hc, hball⟩ := Set.mem_iUnion₂.mp (hcover (hq i))
    exact ⟨⟨c, hc⟩, hball⟩
  choose c hc using hc
  have hinj : Function.Injective c := by
    intro i j heq
    by_contra hne
    have hdist : dist (q i) (q j) < delta := by
      calc
        dist (q i) (q j) ≤ dist (q i) (c i : E) + dist (c i : E) (q j) := dist_triangle _ _ _
        _ < delta / 3 + delta / 3 := add_lt_add (hc i) (by simpa [heq, dist_comm] using hc j)
        _ < delta := by linarith
    rcases lt_or_gt_of_ne hne with hij | hji
    · exact (not_lt_of_ge (hsep i j hij)) hdist
    · exact (not_lt_of_ge (hsep j i hji)) (by simpa [dist_comm] using hdist)
  simpa using Fintype.card_le_of_injective c hinj

/-- A threshold separation theorem is an internal analytic interface. Actual
ECP/ESH executions derive it from their retained rows and canonical tangents. -/
theorem cp_eventually_residual_le {J : Type*} {B : Set E} {g : J → E → ℝ}
    (hB : IsCompact B) (q : ℕ → E) (hq : ∀ k, q k ∈ B)
    (hsep : ∀ eps : ℝ, 0 < eps → ∃ delta : ℝ, 0 < delta ∧
      ∀ i k, i < k → (∃ j, eps < g j (q i)) → delta ≤ dist (q i) (q k)) :
    ∀ eps : ℝ, 0 < eps → ∀ᶠ k in atTop, ∀ j, g j (q k) ≤ eps := by
  intro eps heps
  by_contra hnot
  have hfreq : ∃ᶠ k in atTop, ∃ j, eps < g j (q k) := by
    simpa only [Filter.Frequently, not_exists, not_lt] using hnot
  obtain ⟨phi, hphi, hbad⟩ := extraction_of_frequently_atTop hfreq
  obtain ⟨p, _, psi, hpsi, hlim⟩ := hB.tendsto_subseq (fun k => hq (phi k))
  obtain ⟨delta, hdelta, hd⟩ := hsep eps heps
  obtain ⟨N, hN⟩ := Metric.cauchySeq_iff.mp hlim.cauchySeq delta hdelta
  have hclose := hN N le_rfl (N + 1) (by omega)
  have hfar := hd (phi (psi N)) (phi (psi (N + 1)))
    (hphi (hpsi (by omega))) (hbad (psi N))
  exact (not_lt_of_ge hfar) hclose

theorem cp_threshold_indices_finite {J : Type*} {B : Set E} {g : J → E → ℝ}
    (hB : IsCompact B) (q : ℕ → E) (hq : ∀ k, q k ∈ B)
    (hsep : ∀ eps : ℝ, 0 < eps → ∃ delta : ℝ, 0 < delta ∧
      ∀ i k, i < k → (∃ j, eps < g j (q i)) → delta ≤ dist (q i) (q k))
    {eps : ℝ} (heps : 0 < eps) : {k | ∃ j, eps < g j (q k)}.Finite := by
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp (cp_eventually_residual_le hB q hq hsep eps heps)
  apply (Set.finite_lt_nat N).subset
  intro k hk
  by_contra hnot
  obtain ⟨j, hj⟩ := hk
  exact (not_lt_of_ge (hN k (Nat.le_of_not_gt hnot) j)) hj

end Packing

section Limits
variable {E J : Type*} [MetricSpace E]

theorem cp_subsequence_feasible {B : Set E} {g : J → E → ℝ} {q : ℕ → E}
    (hB : IsClosed B) (hq : ∀ k, q k ∈ B) (hg : ∀ j, Continuous (g j))
    (hsmall : ∀ eps : ℝ, 0 < eps → ∀ᶠ k in atTop, ∀ j, g j (q k) ≤ eps)
    {phi : ℕ → ℕ} (hphi : StrictMono phi) {p : E}
    (hlim : Tendsto (q ∘ phi) atTop (𝓝 p)) : p ∈ B ∧ ∀ j, g j p ≤ 0 := by
  refine ⟨hB.mem_of_tendsto hlim (Eventually.of_forall (fun k => hq (phi k))), ?_⟩
  intro j
  apply le_of_forall_pos_le_add
  intro eps heps
  have hrow := ((hg j).tendsto p).comp hlim
  have hevent := hphi.tendsto_atTop.eventually (hsmall eps heps)
  have hle : g j p ≤ eps := le_of_tendsto hrow (hevent.mono (fun k hk => hk j))
  simpa using hle

theorem cp_mapClusterPt_feasible {B : Set E} {g : J → E → ℝ} {q : ℕ → E}
    (hB : IsClosed B) (hq : ∀ k, q k ∈ B) (hg : ∀ j, Continuous (g j))
    (hsmall : ∀ eps : ℝ, 0 < eps → ∀ᶠ k in atTop, ∀ j, g j (q k) ≤ eps)
    {p : E} (hp : MapClusterPt p atTop q) : p ∈ B ∧ ∀ j, g j p ≤ 0 := by
  obtain ⟨phi, hphi, hlim⟩ := hp.tendsto_subseq
  exact cp_subsequence_feasible hB hq hg hsmall hphi hlim

theorem cp_subsequence_minimizer {F : Set E} {f : E → ℝ} {q : ℕ → E}
    (hf : Continuous f) (hlower : ∀ k, IsLowerBound F f (f (q k)))
    {phi : ℕ → ℕ} {p : E} (hp : p ∈ F)
    (hlim : Tendsto (q ∘ phi) atTop (𝓝 p)) : IsMinimizer F f p := by
  refine ⟨hp, ?_⟩
  intro x hx
  exact le_of_tendsto' ((hf.tendsto p).comp hlim) (fun k => hlower (phi k) x hx)

theorem cp_mapClusterPt_minimizer {F : Set E} {f : E → ℝ} {q : ℕ → E}
    (hf : Continuous f) (hlower : ∀ k, IsLowerBound F f (f (q k)))
    {p : E} (hpF : p ∈ F) (hp : MapClusterPt p atTop q) : IsMinimizer F f p := by
  obtain ⟨phi, _, hlim⟩ := hp.tendsto_subseq
  exact cp_subsequence_minimizer hf hlower hpF hlim

theorem cp_optimal_subsequence_exists {B : Set E} {g : J → E → ℝ}
    {f : E → ℝ} {q : ℕ → E}
    (hB : IsCompact B) (hq : ∀ k, q k ∈ B) (hg : ∀ j, Continuous (g j))
    (hf : Continuous f)
    (hsmall : ∀ eps : ℝ, 0 < eps → ∀ᶠ k in atTop, ∀ j, g j (q k) ≤ eps)
    (hlower : ∀ k, IsLowerBound {p | p ∈ B ∧ ∀ j, g j p ≤ 0} f (f (q k))) :
    ∃ p, IsMinimizer {p | p ∈ B ∧ ∀ j, g j p ≤ 0} f p ∧
      ∃ phi : ℕ → ℕ, StrictMono phi ∧ Tendsto (q ∘ phi) atTop (𝓝 p) := by
  obtain ⟨p, _, phi, hphi, hlim⟩ := hB.tendsto_subseq hq
  have hp := cp_subsequence_feasible hB.isClosed hq hg hsmall hphi hlim
  exact ⟨p, cp_subsequence_minimizer hf hlower hp hlim, phi, hphi, hlim⟩

theorem cp_objective_tendsto_of_subsequence {f : E → ℝ} {q : ℕ → E}
    (hf : Continuous f) (hmono : Monotone (f ∘ q))
    {phi : ℕ → ℕ} (hphi : StrictMono phi) {p : E}
    (hlim : Tendsto (q ∘ phi) atTop (𝓝 p)) :
    Tendsto (f ∘ q) atTop (𝓝 (f p)) := by
  apply (tendsto_iff_tendsto_subseq_of_monotone hmono hphi.tendsto_atTop).mpr
  exact (hf.tendsto p).comp hlim

/-- Complete internal limiting package. Source procedure theorems must prove
`hsep`, `hlower`, and `hmono` from their actual append-only execution. The
conclusion gives every cluster point, not convergence of the point sequence.
The feasible set is proved nonempty, including when the row type is empty. -/
theorem cp_compact_limiting_certificate {B : Set E} {g : J → E → ℝ}
    {f : E → ℝ} {q : ℕ → E}
    (hB : IsCompact B) (hq : ∀ k, q k ∈ B) (hg : ∀ j, Continuous (g j))
    (hf : Continuous f)
    (hsep : ∀ eps : ℝ, 0 < eps → ∃ delta : ℝ, 0 < delta ∧
      ∀ i k, i < k → (∃ j, eps < g j (q i)) → delta ≤ dist (q i) (q k))
    (hlower : ∀ k, IsLowerBound {p | p ∈ B ∧ ∀ j, g j p ≤ 0} f (f (q k)))
    (hmono : Monotone (f ∘ q)) :
    (∀ eps : ℝ, 0 < eps → {k | ∃ j, eps < g j (q k)}.Finite) ∧
    {p | p ∈ B ∧ ∀ j, g j p ≤ 0}.Nonempty ∧
    (∀ p, MapClusterPt p atTop q →
      IsMinimizer {p | p ∈ B ∧ ∀ j, g j p ≤ 0} f p) ∧
    ∃ p, IsMinimizer {p | p ∈ B ∧ ∀ j, g j p ≤ 0} f p ∧
      ∃ phi : ℕ → ℕ, StrictMono phi ∧ Tendsto (q ∘ phi) atTop (𝓝 p) ∧
        Tendsto (f ∘ q) atTop (𝓝 (f p)) := by
  have hsmall := cp_eventually_residual_le hB q hq hsep
  obtain ⟨p, hp, phi, hphi, hlim⟩ := cp_optimal_subsequence_exists hB hq hg hf hsmall hlower
  refine ⟨fun eps heps => cp_threshold_indices_finite hB q hq hsep heps,
    ⟨p, hp.1⟩, ?_, p, hp, phi, hphi, hlim,
    cp_objective_tendsto_of_subsequence hf hmono hphi hlim⟩
  intro x hx
  exact cp_mapClusterPt_minimizer hf hlower
    (cp_mapClusterPt_feasible hB.isClosed hq hg hsmall hx) hx

end Limits
end Chapter02

#print axioms Chapter02.cp_compact_derivative_bound
#print axioms Chapter02.ecp_uniform_separation
#print axioms Chapter02.cp_compact_separated_prefix_bound
#print axioms Chapter02.cp_eventually_residual_le
#print axioms Chapter02.cp_threshold_indices_finite
#print axioms Chapter02.cp_subsequence_feasible
#print axioms Chapter02.cp_mapClusterPt_feasible
#print axioms Chapter02.cp_subsequence_minimizer
#print axioms Chapter02.cp_mapClusterPt_minimizer
#print axioms Chapter02.cp_optimal_subsequence_exists
#print axioms Chapter02.cp_objective_tendsto_of_subsequence
#print axioms Chapter02.cp_compact_limiting_certificate
