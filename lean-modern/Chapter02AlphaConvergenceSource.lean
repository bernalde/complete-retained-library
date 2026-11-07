module

public import Chapter02AlphaSource
public import Chapter02AlphaConvergence
public import Chapter02ECPAnalysis
public import Mathlib.Data.Finset.Sort

@[expose] public section

/-! Dynamic retained alpha rows. All helpers are uncounted. The source endpoint
will expose exact source identities, residual/cluster scope and actual histories.
No nestedness, objective monotonicity or numerical solver guarantee is assumed. -/
noncomputable section
open scoped Topology
open Filter
namespace Chapter02
attribute [local instance] Classical.propDecidable

variable {E J : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

def alphaDynamicMaster (B : Set E) (g : J → E → ℝ)
    (G : J → E → E →L[ℝ] ℝ) (tau : ℝ) (q : ℕ → E)
    (row : ℕ → J) (alpha : ℕ → ℕ → ℝ) (k : ℕ) : Set E :=
  {p | p ∈ B ∧ ∀ i, i < k → tau < g (row i) (q i) →
    g (row i) (q i) + alpha i k * G (row i) (q i) (p - q i) ≤ 0}

theorem alpha_dynamic_separation (B : Set E) (g : J → E → ℝ)
    (G : J → E → E →L[ℝ] ℝ) (tau : ℝ) (q : ℕ → E)
    (row : ℕ → J) (alpha : ℕ → ℕ → ℝ)
    (hmem : ∀ k, q k ∈ alphaDynamicMaster B g G tau q row alpha k)
    (hmax : ∀ k j, g j (q k) ≤ g (row k) (q k))
    {eps C : ℝ} (heps : 0 < eps) (ht : tau ≤ eps) (hC : 0 ≤ C)
    (hcap : ∀ i k, i < k → eps < g (row i) (q i) →
      ‖alpha i k • G (row i) (q i)‖ ≤ C) :
    0 < eps / (C + 1) ∧ ∀ i k, i < k → (∃ j, eps < g j (q i)) →
      eps / (C + 1) ≤ dist (q i) (q k) := by
  have hden : 0 < C + 1 := by linarith
  refine ⟨div_pos heps hden, ?_⟩
  intro i k hik hbad
  obtain ⟨j,hj⟩ := hbad
  have hr := hj.trans_le (hmax i j)
  have hcut := (hmem k).2 i hik (ht.trans_lt hr)
  let L : E →L[ℝ] ℝ := alpha i k • G (row i) (q i)
  have hcut' : g (row i) (q i) + L (q k - q i) ≤ 0 := by
    simpa only [L, ContinuousLinearMap.smul_apply, smul_eq_mul] using hcut
  have hneg : L (q i - q k) = -L (q k - q i) := by rw [← map_neg, neg_sub]
  have h1 : g (row i) (q i) ≤ L (q i - q k) := by rw [hneg]; linarith
  have h2 : L (q i - q k) ≤ ‖L‖ * ‖q i - q k‖ :=
    (le_abs_self _).trans (L.le_opNorm _)
  have h3 := mul_le_mul_of_nonneg_right (hcap i k hik hr) (norm_nonneg (q i - q k))
  apply (div_le_iff₀ hden).mpr
  rw [dist_eq_norm]
  change ‖L‖ * ‖q i - q k‖ ≤ C * ‖q i - q k‖ at h3
  nlinarith [norm_nonneg (q i - q k)]

omit [NormedSpace ℝ E] in
theorem alpha_separated_bad_count (B : Set E) (g : J → E → ℝ)
    (q : ℕ → E) (hB : IsCompact B) (hq : ∀ k, q k ∈ B)
    {eps delta : ℝ} (hd : 0 < delta)
    (hsep : ∀ i k, i < k → (∃ j, eps < g j (q i)) → delta ≤ dist (q i) (q k)) :
    ∃ N : ℕ, (∀ n, ((Finset.range n).filter (fun i => ∃ j, eps < g j (q i))).card ≤ N) ∧
      {i | ∃ j, eps < g j (q i)}.Finite ∧
      ∀ᶠ k in atTop, ∀ j, g j (q k) ≤ eps := by
  classical
  obtain ⟨N,hN⟩ := cp_compact_separated_prefix_bound hB hd
  have hprefix (n : ℕ) :
      ((Finset.range n).filter (fun i => ∃ j, eps < g j (q i))).card ≤ N := by
    let T := (Finset.range n).filter (fun i => ∃ j, eps < g j (q i))
    let f : Fin T.card ↪o ℕ := T.orderEmbOfFin rfl
    apply hN T.card (fun i => q (f i)) (fun i => hq _)
    intro i k hik
    apply hsep (f i) (f k) (f.strictMono hik)
    exact (Finset.mem_filter.mp (T.orderEmbOfFin_mem rfl i)).2
  have hsmall : ∀ᶠ k in atTop, ∀ j, g j (q k) ≤ eps := by
    by_contra hnot
    have hfreq : ∃ᶠ k in atTop, ∃ j, eps < g j (q k) := by
      simpa only [Filter.Frequently, not_exists, not_lt] using hnot
    obtain ⟨phi,hphi,hbad⟩ := extraction_of_frequently_atTop hfreq
    have hh := hN (N+1) (fun i : Fin (N+1) => q (phi i)) (fun i => hq _)
      (fun i k hik => hsep _ _ (hphi hik) (hbad i))
    omega
  have hfinite : {i | ∃ j, eps < g j (q i)}.Finite := by
    obtain ⟨n,hn⟩ := Filter.eventually_atTop.mp hsmall
    apply (Set.finite_lt_nat n).subset
    intro k hk
    by_contra hnot
    obtain ⟨j,hj⟩ := hk
    exact (not_lt_of_ge (hn k (Nat.le_of_not_gt hnot) j)) hj
  exact ⟨N,hprefix,hfinite,hsmall⟩

theorem alpha_dynamic_cap_limits (B : Set E) (g : J → E → ℝ)
    (G : J → E → E →L[ℝ] ℝ) (tau : ℝ) (q : ℕ → E)
    (row : ℕ → J) (alpha : ℕ → ℕ → ℝ) (hB : IsCompact B)
    (hmem : ∀ k, q k ∈ alphaDynamicMaster B g G tau q row alpha k)
    (hmax : ∀ k j, g j (q k) ≤ g (row k) (q k))
    (hcaps : ∀ eps : ℝ, 0 < eps → tau ≤ eps → ∃ C : ℝ, 0 ≤ C ∧
      ∀ i k, i < k → eps < g (row i) (q i) → ‖alpha i k • G (row i) (q i)‖ ≤ C) :
    ∀ eps : ℝ, 0 < eps → tau ≤ eps → ∃ N : ℕ,
      (∀ n, ((Finset.range n).filter (fun i => ∃ j, eps < g j (q i))).card ≤ N) ∧
      {i | ∃ j, eps < g j (q i)}.Finite ∧
      ∀ᶠ k in atTop, ∀ j, g j (q k) ≤ eps := by
  intro eps heps ht
  obtain ⟨C,hC,hcap⟩ := hcaps eps heps ht
  obtain ⟨hd,hsep⟩ := alpha_dynamic_separation B g G tau q row alpha hmem hmax heps ht hC hcap
  obtain ⟨N,hprefix,hfinite,hsmall⟩ :=
    alpha_separated_bad_count B g q hB (fun k => (hmem k).1) hd hsep
  by_cases hz : tau = 0
  · have hall : ∀ e : ℝ, 0 < e → ∃ delta : ℝ, 0 < delta ∧
        ∀ i k, i < k → (∃ j, e < g j (q i)) → delta ≤ dist (q i) (q k) := by
      intro e he
      obtain ⟨Ce,hCe,hce⟩ := hcaps e he (by simpa [hz] using he.le)
      exact ⟨e / (Ce + 1), alpha_dynamic_separation B g G tau q row alpha
        hmem hmax he (by simpa [hz] using he.le) hCe hce⟩
    exact ⟨N,hprefix,
      cp_threshold_indices_finite hB q (fun k => (hmem k).1) hall heps,
      cp_eventually_residual_le hB q (fun k => (hmem k).1) hall eps heps⟩
  · exact ⟨N,hprefix,hfinite,hsmall⟩

omit [NormedSpace ℝ E] in
theorem alpha_relative_subsequence_feasible (B : Set E) (g : J → E → ℝ)
    (q : ℕ → E) (hB : IsClosed B) (hq : ∀ k, q k ∈ B)
    (hg : ∀ j, ContinuousOn (g j) B)
    (hsmall : ∀ eps : ℝ, 0 < eps → ∀ᶠ k in atTop, ∀ j, g j (q k) ≤ eps)
    {phi : ℕ → ℕ} (hphi : StrictMono phi) {p : E}
    (hlim : Tendsto (q ∘ phi) atTop (𝓝 p)) :
    p ∈ B ∧ ∀ j, g j p ≤ 0 := by
  have hp := hB.mem_of_tendsto hlim (Eventually.of_forall fun k => hq (phi k))
  refine ⟨hp,?_⟩
  intro j
  apply le_of_forall_pos_le_add
  intro eps heps
  have hwithin : Tendsto (q ∘ phi) atTop (𝓝[B] p) :=
    tendsto_nhdsWithin_iff.mpr ⟨hlim, Eventually.of_forall fun k => hq (phi k)⟩
  have hrow := (hg j p hp).tendsto.comp hwithin
  have hevent := hphi.tendsto_atTop.eventually (hsmall eps heps)
  have hle : g j p ≤ eps := le_of_tendsto hrow (hevent.mono fun k hk => hk j)
  simpa using hle

/-- Complete retained masters are compact even if the scale changes with k. -/
theorem alpha_dynamic_master_compact (B : Set E) (g : J → E → ℝ)
    (G : J → E → E →L[ℝ] ℝ) (tau : ℝ) (q : ℕ → E)
    (row : ℕ → J) (alpha : ℕ → ℕ → ℝ) (hB : IsCompact B) (k : ℕ) :
    IsCompact (alphaDynamicMaster B g G tau q row alpha k) := by
  have heq : alphaDynamicMaster B g G tau q row alpha k =
      B ∩ ⋂ i, ⋂ (_ : i < k), ⋂ (_ : tau < g (row i) (q i)),
        {p | g (row i) (q i) + alpha i k * G (row i) (q i) (p - q i) ≤ 0} := by
    ext p; simp [alphaDynamicMaster]
  rw [heq]
  apply hB.inter_right
  exact isClosed_iInter fun i => isClosed_iInter fun _ => isClosed_iInter fun _ =>
    isClosed_le (continuous_const.add (continuous_const.mul
      ((G (row i) (q i)).continuous.comp (continuous_id.sub continuous_const))))
      continuous_const

/-- A retained-history statement; definitions expose every policy and limit claim. -/
def AlphaHistoryConclusions (B S : Set E) (g : J → E → ℝ)
    (G : J → E → E →L[ℝ] ℝ) (f : E → ℝ) (tau : ℝ)
    (q : ℕ → E) (row : ℕ → J) (alpha : ℕ → ℕ → ℝ) : Prop :=
  (∀ k, IsCompact (alphaDynamicMaster B g G tau q row alpha k) ∧
    (alphaDynamicMaster B g G tau q row alpha k).Nonempty ∧
    S ⊆ alphaDynamicMaster B g G tau q row alpha k ∧
    ∃ p, IsMinimizer (alphaDynamicMaster B g G tau q row alpha k) f p) ∧
  (∀ eps : ℝ, 0 < eps → tau ≤ eps → ∃ N : ℕ,
    (∀ n, ((Finset.range n).filter (fun i => ∃ j, eps < g j (q i))).card ≤ N) ∧
    {i | ∃ j, eps < g j (q i)}.Finite ∧
    ∀ᶠ k in atTop, ∀ j, g j (q k) ≤ eps) ∧
  (tau = 0 → (∀ p, MapClusterPt p atTop q → p ∈ S) ∧
    ∃ p ∈ S, ∃ phi : ℕ → ℕ, StrictMono phi ∧ Tendsto (q ∘ phi) atTop (𝓝 p)) ∧
  (tau = 0 → (∀ k, IsMinimizer (alphaDynamicMaster B g G tau q row alpha k) f (q k)) →
    (∀ p, MapClusterPt p atTop q → IsMinimizer S f p) ∧
    ∃ p, IsMinimizer S f p ∧
      ∃ phi : ℕ → ℕ, StrictMono phi ∧ Tendsto (q ∘ phi) atTop (𝓝 p)) ∧
  (∀ k, IsMinimizer (alphaDynamicMaster B g G tau q row alpha k) f (q k) →
    q k ∈ S → IsMinimizer S f (q k))

theorem alpha_history_conclusions (B : Set E) (g : J → E → ℝ)
    (G : J → E → E →L[ℝ] ℝ) (f : E → ℝ) (tau : ℝ)
    (q : ℕ → E) (row : ℕ → J) (alpha : ℕ → ℕ → ℝ)
    (hB : IsCompact B) (hne : (alphaScaleFeasible B g).Nonempty)
    (hg : ∀ j, ContinuousOn (g j) B) (hf : Continuous f)
    (hmem : ∀ k, q k ∈ alphaDynamicMaster B g G tau q row alpha k)
    (hmax : ∀ k j, g j (q k) ≤ g (row k) (q k))
    (houter : ∀ k, alphaScaleFeasible B g ⊆ alphaDynamicMaster B g G tau q row alpha k)
    (hcaps : ∀ eps : ℝ, 0 < eps → tau ≤ eps → ∃ C : ℝ, 0 ≤ C ∧
      ∀ i k, i < k → eps < g (row i) (q i) → ‖alpha i k • G (row i) (q i)‖ ≤ C) :
    AlphaHistoryConclusions B (alphaScaleFeasible B g) g G f tau q row alpha := by
  have hq : ∀ k, q k ∈ B := fun k => (hmem k).1
  have hprogress := alpha_dynamic_cap_limits B g G tau q row alpha hB hmem hmax hcaps
  have hsmall (ht : tau = 0) : ∀ eps : ℝ, 0 < eps → ∀ᶠ k in atTop, ∀ j, g j (q k) ≤ eps := by
    intro eps heps
    exact (hprogress eps heps (by simpa [ht] using heps.le)).choose_spec.2.2
  have hsub (ht : tau = 0) {phi : ℕ → ℕ} (hphi : StrictMono phi) {p : E}
      (hlim : Tendsto (q ∘ phi) atTop (𝓝 p)) : p ∈ alphaScaleFeasible B g :=
    alpha_relative_subsequence_feasible B g q hB.isClosed hq hg (hsmall ht) hphi hlim
  have hcluster (ht : tau = 0) (p : E) (hp : MapClusterPt p atTop q) :
      p ∈ alphaScaleFeasible B g := by
    obtain ⟨phi,hphi,hlim⟩ := hp.tendsto_subseq
    exact hsub ht hphi hlim
  refine ⟨?_,hprogress,?_,?_,?_⟩
  · intro k
    have hc := alpha_dynamic_master_compact B g G tau q row alpha hB k
    have hn := hne.mono (houter k)
    exact ⟨hc,hn,houter k,compact_feasible_attainment hc hn hf.continuousOn⟩
  · intro ht
    obtain ⟨p,_,phi,hphi,hlim⟩ := hB.tendsto_subseq hq
    exact ⟨hcluster ht,p,hsub ht hphi hlim,phi,hphi,hlim⟩
  · intro ht hmin
    have hlower : ∀ k, IsLowerBound (alphaScaleFeasible B g) f (f (q k)) :=
      fun k p hp => (hmin k).2 p (houter k hp)
    refine ⟨fun p hp => cp_mapClusterPt_minimizer hf hlower (hcluster ht p hp) hp,?_⟩
    obtain ⟨p,_,phi,hphi,hlim⟩ := hB.tendsto_subseq hq
    exact ⟨p,cp_subsequence_minimizer hf hlower (hsub ht hphi hlim) hlim,phi,hphi,hlim⟩
  · intro k hmin hp
    exact minimizer_of_relaxation_feasible (houter k) hmin hp

/-- Mathematical nonvacuity: static safe scales and genuine compact global
minimizers produce an infinite history. This is not solver executability. -/
theorem alpha_static_history_exists [Fintype J] [Nonempty J]
    (B : Set E) (g : J → E → ℝ) (G : J → E → E →L[ℝ] ℝ)
    (f : E → ℝ) (a : J → E → ℝ) (hB : IsCompact B)
    (hne : (alphaScaleFeasible B g).Nonempty) (hf : Continuous f)
    (hsafe : ∀ j x, x ∈ B → 0 < g j x → ∀ p ∈ alphaScaleFeasible B g,
      g j x + a j x * G j x (p-x) ≤ 0) (tau : ℝ) (ht : 0 ≤ tau) :
    ∃ (q : ℕ → E) (row : ℕ → J),
      (∀ k, IsMinimizer (alphaDynamicMaster B g G tau q row
        (fun i _ => a (row i) (q i)) k) f (q k)) ∧
      (∀ k j, g j (q k) ≤ g (row k) (q k)) ∧
      (∀ k, q k ∈ alphaDynamicMaster B g G tau q row (fun i _ => a (row i) (q i)) k) ∧
      (∀ i k, i < k → tau < g (row i) (q i) →
        a (row i) (q i) ≤ a (row i) (q i) ∧
        a (row i) (q i) ≤ 1 * a (row i) (q i)) := by
  classical
  let T := B × J
  have hstep (k : ℕ) (s : ℕ → T) : ∃ z : T,
      IsMinimizer (alphaDynamicMaster B g G tau (fun i => (s i).1.val)
        (fun i => (s i).2) (fun i _ => a (s i).2 (s i).1.val) k) f z.1.val ∧
      ∀ j, g j z.1.val ≤ g z.2 z.1.val := by
    let q : ℕ → E := fun i => (s i).1.val
    let row : ℕ → J := fun i => (s i).2
    let alpha : ℕ → ℕ → ℝ := fun i _ => a (row i) (q i)
    have houter : alphaScaleFeasible B g ⊆ alphaDynamicMaster B g G tau q row alpha k := by
      intro p hp
      refine ⟨hp.1,?_⟩
      intro i _ hi
      exact hsafe (row i) (q i) (s i).1.property (ht.trans_lt hi) p hp
    obtain ⟨p,hp⟩ := compact_feasible_attainment
      (alpha_dynamic_master_compact B g G tau q row alpha hB k)
      (hne.mono houter) hf.continuousOn
    obtain ⟨j,_,hj⟩ := Finset.exists_max_image Finset.univ (fun j => g j p) Finset.univ_nonempty
    exact ⟨(⟨p,hp.1.1⟩,j),hp,fun i => hj i (Finset.mem_univ _)⟩
  let chooseStep : ℕ → (ℕ → T) → T := fun k s => (hstep k s).choose
  have hchoose (k : ℕ) (s : ℕ → T) := (hstep k s).choose_spec
  obtain ⟨p,hp⟩ := hne
  let initial : ℕ → T := fun _ => (⟨p,hp.1⟩,Classical.choice inferInstance)
  let states : ℕ → ℕ → T := fun n => Nat.rec initial
    (fun k s => Function.update s k (chooseStep k s)) n
  let chosen : ℕ → T := fun k => chooseStep k (states k)
  have hprefix : ∀ n i, i < n → states n i = chosen i := by
    intro n
    induction n with
    | zero => intro i hi; omega
    | succ n ih =>
      intro i hi
      by_cases he : i = n
      · subst i
        simp [states,chosen]
      · have hin : i < n := by omega
        change Function.update (states n) n (chooseStep n (states n)) i = chosen i
        rw [Function.update_of_ne he]
        exact ih i hin
  let q : ℕ → E := fun i => (chosen i).1.val
  let row : ℕ → J := fun i => (chosen i).2
  have heq (k : ℕ) : alphaDynamicMaster B g G tau (fun i => (states k i).1.val)
      (fun i => (states k i).2) (fun i _ => a (states k i).2 (states k i).1.val) k =
      alphaDynamicMaster B g G tau q row (fun i _ => a (row i) (q i)) k := by
    ext x
    constructor <;> intro hx <;> refine ⟨hx.1,?_⟩ <;> intro i hi hv
    · have hs := hx.2 i hi
      simpa only [hprefix k i hi] using hs (by simpa only [hprefix k i hi] using hv)
    · have hs := hx.2 i hi
      simpa only [hprefix k i hi] using hs (by simpa only [hprefix k i hi] using hv)
  have hmin (k : ℕ) : IsMinimizer
      (alphaDynamicMaster B g G tau q row (fun i _ => a (row i) (q i)) k) f (q k) := by
    have h := (hchoose k (states k)).1
    change IsMinimizer (alphaDynamicMaster B g G tau (fun i => (states k i).1.val)
      (fun i => (states k i).2) (fun i _ => a (states k i).2 (states k i).1.val) k) f (q k) at h
    rw [heq k] at h
    exact h
  refine ⟨q,row,hmin,?_,fun k => (hmin k).1,?_⟩
  · intro k j
    exact (hchoose k (states k)).2 j
  · intro i k _ _
    exact ⟨le_rfl,by simp⟩

/-- Transparent certificate for the exact scale output of Endpoint A, with an
explicit feasible set parameter for literal source transport. -/
def AlphaScaleCertificate (B S : Set E) (g : J → E → ℝ)
    (G : J → E → E →L[ℝ] ℝ) (a : J → E → ℝ) (M : ℝ) : Prop :=
  (∀ j q, 1 ≤ a j q) ∧
  (∀ j q, q ∉ B ∨ g j q ≤ 0 → a j q = 1) ∧
  1 ≤ M ∧ (∀ j q, q ∈ B → ‖G j q‖ ≤ M) ∧
  (∀ j q, q ∈ B → 0 < g j q → ∀ alpha : ℝ, a j q ≤ alpha →
    ∀ p ∈ S, g j q + alpha * G j q (p-q) ≤ g j p ∧ g j p ≤ 0) ∧
  (∀ eps : ℝ, 0 < eps → ∃ A : ℝ, 1 ≤ A ∧
    ∀ j q, q ∈ B → eps ≤ g j q → a j q ≤ A ∧
      ∀ rho : ℝ, 1 ≤ rho → ∀ alpha : ℝ, a j q ≤ alpha → alpha ≤ rho * a j q →
        ‖alpha • G j q‖ ≤ rho * A * M)

/-- The quantitative premise uses the actual retained row at every later k. -/
def AlphaControlledHistory (B : Set E) (g : J → E → ℝ)
    (G : J → E → E →L[ℝ] ℝ) (a : J → E → ℝ) (tau rho : ℝ)
    (q : ℕ → E) (row : ℕ → J) (alpha : ℕ → ℕ → ℝ) : Prop :=
  (∀ k, q k ∈ alphaDynamicMaster B g G tau q row alpha k) ∧
  (∀ k j, g j (q k) ≤ g (row k) (q k)) ∧
  (∀ i k, i < k → tau < g (row i) (q i) →
    a (row i) (q i) ≤ alpha i k ∧ alpha i k ≤ rho * a (row i) (q i))

theorem alpha_controlled_history_conclusions (B : Set E) (g : J → E → ℝ)
    (G : J → E → E →L[ℝ] ℝ) (f : E → ℝ) (a : J → E → ℝ) (M : ℝ)
    (hB : IsCompact B) (hne : (alphaScaleFeasible B g).Nonempty)
    (hg : ∀ j, ContinuousOn (g j) B) (hf : Continuous f)
    (hscale : AlphaScaleCertificate B (alphaScaleFeasible B g) g G a M)
    (tau rho : ℝ) (ht : 0 ≤ tau) (hr : 1 ≤ rho)
    (q : ℕ → E) (row : ℕ → J) (alpha : ℕ → ℕ → ℝ)
    (hh : AlphaControlledHistory B g G a tau rho q row alpha) :
    AlphaHistoryConclusions B (alphaScaleFeasible B g) g G f tau q row alpha := by
  rcases hh with ⟨hmem,hmax,hpolicy⟩
  rcases hscale with ⟨_,_,hM,_,hsafe,hthreshold⟩
  apply alpha_history_conclusions B g G f tau q row alpha hB hne hg hf hmem hmax
  · intro k p hp
    refine ⟨hp.1,?_⟩
    intro i hik hi
    exact (hsafe (row i) (q i) (hmem i).1 (ht.trans_lt hi) (alpha i k)
      (hpolicy i k hik hi).1 p hp).1.trans (hp.2 (row i))
  · intro eps heps hte
    obtain ⟨A,hA,hbound⟩ := hthreshold eps heps
    refine ⟨rho*A*M,mul_nonneg (mul_nonneg (by linarith) (by linarith)) (by linarith),?_⟩
    intro i k hik hi
    have hpol := hpolicy i k hik (hte.trans_lt hi)
    exact (hbound (row i) (q i) (hmem i).1 hi.le).2 rho hr (alpha i k) hpol.1 hpol.2

/-- Source endpoint for controlled smooth retained-cut histories. Ambient rows
agree on every integer slice; smoothness is relative to the entire mixed base.
The final existential uses exactly the same a as the scale certificate.
Limits keep original integer witnesses and the original linear objective.
No finite zero-tolerance return, point convergence or solver execution follows. -/
theorem source_alpha_controlled_history_limits {n m l r : ℕ} [Nonempty (Fin l)]
    (d : ModelData n m l r)
    (gMixed : Fin l → RealVector n → IntVector m → ℝ) (K : Set (Point n m))
    (G : Fin l → Point n m → Point n m →L[ℝ] ℝ)
    (hExtension : ∀ j x y, d.g j (x, fun i => (y i : ℝ)) = gMixed j x y)
    (hK : IsCompact K) (hne : (sourceMixedFeasible d gMixed K).Nonempty)
    (hderiv : ∀ j x, x ∈ alphaMixedBase d K → HasFDerivAt (d.g j) (G j x) x)
    (hG : ∀ j, ContinuousOn (G j) (alphaMixedBase d K))
    (hpseudo : ∀ j x, x ∈ alphaMixedBase d K → ∀ y, y ∈ alphaMixedBase d K →
      d.g j y < d.g j x → G j x (y-x) < 0) :
    sourceMixedFeasible d gMixed K = d.feasibleOn K ∧
    sourceMixedFeasible d gMixed K = alphaScaleFeasible (alphaMixedBase d K) d.g ∧
    IsCompact (alphaMixedBase d K) ∧ IsCompact (sourceMixedFeasible d gMixed K) ∧
    ∃ (a : Fin l → Point n m → ℝ) (M : ℝ),
      AlphaScaleCertificate (alphaMixedBase d K) (sourceMixedFeasible d gMixed K) d.g G a M ∧
      (∀ tau rho : ℝ, 0 ≤ tau → 1 ≤ rho →
        ∀ (q : ℕ → Point n m) (row : ℕ → Fin l) (alpha : ℕ → ℕ → ℝ),
          AlphaControlledHistory (alphaMixedBase d K) d.g G a tau rho q row alpha →
          AlphaHistoryConclusions (alphaMixedBase d K) (sourceMixedFeasible d gMixed K)
            d.g G d.objective tau q row alpha) ∧
      (∀ tau : ℝ, 0 ≤ tau → ∃ (q : ℕ → Point n m) (row : ℕ → Fin l),
        AlphaControlledHistory (alphaMixedBase d K) d.g G a tau 1 q row
          (fun i _ => a (row i) (q i)) ∧
        (∀ k, IsMinimizer (alphaDynamicMaster (alphaMixedBase d K) d.g G tau q row
          (fun i _ => a (row i) (q i)) k) d.objective (q k))) := by
  classical
  have hempty := source_alpha_cut_family (k := 0) d gMixed K G
    (fun i => Fin.elim0 i) (fun i => Fin.elim0 i)
    hExtension hK hne hderiv hpseudo (fun i => Fin.elim0 i) (fun i => Fin.elim0 i)
  have hsource := hempty.1
  have hB := hempty.2.1
  have hS := hempty.2.2.1
  have hset : sourceMixedFeasible d gMixed K = alphaScaleFeasible (alphaMixedBase d K) d.g := by
    rw [hsource]
    ext p
    constructor
    · rintro ⟨⟨⟨hpK,hrows⟩,hpL⟩,hpY⟩
      exact ⟨⟨⟨hpK,hpL⟩,hpY⟩,hrows⟩
    · rintro ⟨⟨⟨hpK,hpL⟩,hpY⟩,hrows⟩
      exact ⟨⟨⟨hpK,hrows⟩,hpL⟩,hpY⟩
  have hn : (alphaScaleFeasible (alphaMixedBase d K) d.g).Nonempty := hset ▸ hne
  obtain ⟨a,M,ha⟩ := alpha_uniform_threshold_scale_control
    (alphaMixedBase d K) d.g G hB hn hderiv hG hpseudo
  change AlphaScaleCertificate (alphaMixedBase d K)
    (alphaScaleFeasible (alphaMixedBase d K) d.g) d.g G a M at ha
  have hg : ∀ j, ContinuousOn (d.g j) (alphaMixedBase d K) :=
    fun j x hx => (hderiv j x hx).continuousAt.continuousWithinAt
  have hf : Continuous d.objective := linearForm_continuous d.c1 d.c2
  refine ⟨hsource,hset,hB,hS,a,M,?_,?_,?_⟩
  · simpa only [hset] using ha
  · intro tau rho ht hr q row alpha hh
    have hc := alpha_controlled_history_conclusions (alphaMixedBase d K) d.g G
      d.objective a M hB hn hg hf ha tau rho ht hr q row alpha hh
    simpa only [hset] using hc
  · intro tau ht
    have hs : ∀ j x, x ∈ alphaMixedBase d K → 0 < d.g j x →
        ∀ p ∈ alphaScaleFeasible (alphaMixedBase d K) d.g,
        d.g j x + a j x * G j x (p-x) ≤ 0 := by
      intro j x hx hv p hp
      exact (ha.2.2.2.2.1 j x hx hv (a j x) le_rfl p hp).1.trans (hp.2 j)
    obtain ⟨q,row,hmin,hmax,hmem,hpolicy⟩ := alpha_static_history_exists
      (alphaMixedBase d K) d.g G d.objective a hB hn hf hs tau ht
    exact ⟨q,row,⟨hmem,hmax,hpolicy⟩,hmin⟩

end Chapter02

#print axioms Chapter02.source_alpha_controlled_history_limits
