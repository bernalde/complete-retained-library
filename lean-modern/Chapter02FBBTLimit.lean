module

public import Chapter02FBBTBounds
public import Mathlib.Topology.Order.MonotoneConvergence
public import Mathlib.Dynamics.FixedPoints.Topology

@[expose] public section

/-! Uncounted endpoint infrastructure for a finite simultaneous FBBT candidate.
The concrete operator must discharge every continuity/order/run hypothesis.
No LP, source-feasibility, empty-state or source-certification claim is made here. -/
noncomputable section
open scoped BigOperators Topology
open Filter Function
namespace Chapter02FBBT

variable {ι : Type*}

theorem limit_within_refl (q : Bounds ι) : Within q q :=
  fun _ => ⟨le_rfl, le_rfl⟩

theorem limit_within_trans {p q r : Bounds ι} (hpq : Within p q)
    (hqr : Within q r) : Within p r :=
  fun i => ⟨(hqr i).1.trans (hpq i).1, (hpq i).2.trans (hqr i).2⟩

theorem limit_within_antisymm {p q : Bounds ι} (hpq : Within p q)
    (hqp : Within q p) : p = q := by
  apply Prod.ext <;> funext i
  · exact le_antisymm (hqp i).1 (hpq i).1
  · exact le_antisymm (hpq i).2 (hqp i).2

/-- A canonical real endpoint limit; ordered iterates and boundedness are
proved before this total definition is used as a limit. -/
def endpointLimit (F : Bounds ι → Bounds ι) (q0 : Bounds ι) : Bounds ι :=
  (fun i => ⨆ k : ℕ, (F^[k] q0).1 i,
   fun i => ⨅ k : ℕ, (F^[k] q0).2 i)

/-- Actual iterates converge, their limit is ordered and fixed, and it contains
every ordered fixed box initially within q0. Empty coordinate types are allowed. -/
theorem bounds_iterate_limit (F : Bounds ι → Bounds ι) (q0 : Bounds ι)
    (hcont : Continuous F)
    (hcontract : ∀ q, Ordered q → Within (F q) q)
    (hmono : ∀ p q, Ordered p → Ordered q → Within p q → Within (F p) (F q))
    (hordered : ∀ k : ℕ, Ordered (F^[k] q0)) :
    Ordered (endpointLimit F q0) ∧
    Within (endpointLimit F q0) q0 ∧
    Tendsto (fun k : ℕ => F^[k] q0) atTop (𝓝 (endpointLimit F q0)) ∧
    F (endpointLimit F q0) = endpointLimit F q0 ∧
    (∀ q, Ordered q → Within q q0 → F q = q → Within q (endpointLimit F q0)) := by
  have hlmono (i : ι) : Monotone (fun k : ℕ => (F^[k] q0).1 i) := by
    apply monotone_nat_of_le_succ
    intro k
    simpa only [Function.iterate_succ_apply'] using (hcontract _ (hordered k) i).1
  have humono (i : ι) : Antitone (fun k : ℕ => (F^[k] q0).2 i) := by
    apply antitone_nat_of_succ_le
    intro k
    simpa only [Function.iterate_succ_apply'] using (hcontract _ (hordered k) i).2
  have hinit (k : ℕ) : Within (F^[k] q0) q0 := by
    intro i
    exact ⟨by simpa using hlmono i (Nat.zero_le k),
      by simpa using humono i (Nat.zero_le k)⟩
  have hlbound (i : ι) : BddAbove (Set.range (fun k : ℕ => (F^[k] q0).1 i)) := by
    refine ⟨q0.2 i, ?_⟩
    rintro x ⟨k, rfl⟩
    exact (hordered k i).trans (hinit k i).2
  have hubound (i : ι) : BddBelow (Set.range (fun k : ℕ => (F^[k] q0).2 i)) := by
    refine ⟨q0.1 i, ?_⟩
    rintro x ⟨k, rfl⟩
    exact (hinit k i).1.trans (hordered k i)
  have hlt (i : ι) : Tendsto (fun k : ℕ => (F^[k] q0).1 i)
      atTop (𝓝 ((endpointLimit F q0).1 i)) :=
    tendsto_atTop_ciSup (hlmono i) (hlbound i)
  have hut (i : ι) : Tendsto (fun k : ℕ => (F^[k] q0).2 i)
      atTop (𝓝 ((endpointLimit F q0).2 i)) :=
    tendsto_atTop_ciInf (humono i) (hubound i)
  have hlimorder : Ordered (endpointLimit F q0) := by
    intro i
    exact le_of_tendsto_of_tendsto' (hlt i) (hut i) (fun k => hordered k i)
  have hlimwithin : Within (endpointLimit F q0) q0 := by
    intro i
    exact ⟨le_of_tendsto_of_tendsto' tendsto_const_nhds (hlt i)
        (fun k => (hinit k i).1),
      le_of_tendsto_of_tendsto' (hut i) tendsto_const_nhds (fun k => (hinit k i).2)⟩
  have ht : Tendsto (fun k : ℕ => F^[k] q0) atTop (𝓝 (endpointLimit F q0)) := by
    exact (tendsto_pi_nhds.mpr hlt).prodMk_nhds (tendsto_pi_nhds.mpr hut)
  refine ⟨hlimorder, hlimwithin, ht,
    isFixedPt_of_tendsto_iterate ht hcont.continuousAt, ?_⟩
  intro q hq hq0 hfixed
  have hinside (k : ℕ) : Within q (F^[k] q0) := by
    induction k with
    | zero => simpa using hq0
    | succ k ih =>
      simpa only [Function.iterate_succ_apply', hfixed] using
        hmono q (F^[k] q0) hq (hordered k) ih
  intro i
  exact ⟨le_of_tendsto_of_tendsto' (hlt i) tendsto_const_nhds
      (fun k => (hinside k i).1),
    le_of_tendsto_of_tendsto' tendsto_const_nhds (hut i) (fun k => (hinside k i).2)⟩

variable [Fintype ι]

theorem bounds_width_le {q r : Bounds ι} (h : Within q r) : width q ≤ width r := by
  apply Finset.sum_le_sum
  intro i _
  exact sub_le_sub (h i).2 (h i).1

/-- Equality of total width for nested endpoint boxes forces equality of every
endpoint, without a positive-dimension premise. -/
theorem bounds_eq_of_within_width_eq {q r : Bounds ι} (h : Within q r)
    (hw : width q = width r) : q = r := by
  have hnonneg (i : ι) : 0 ≤ (q.1 i - r.1 i) + (r.2 i - q.2 i) :=
    add_nonneg (sub_nonneg.mpr (h i).1) (sub_nonneg.mpr (h i).2)
  have hsum : ∑ i, ((q.1 i - r.1 i) + (r.2 i - q.2 i)) = 0 := by
    have hidentity : (∑ i, ((q.1 i - r.1 i) + (r.2 i - q.2 i))) = width r - width q := by
      simp only [width, Finset.sum_add_distrib, Finset.sum_sub_distrib]
      ring
    rw [hidentity, hw, sub_self]
  have hzero (i : ι) : (q.1 i - r.1 i) + (r.2 i - q.2 i) = 0 :=
    (Finset.sum_eq_zero_iff_of_nonneg (fun j _ => hnonneg j)).mp hsum i (Finset.mem_univ i)
  apply Prod.ext <;> funext i
  · have hi := h i
    have hz := hzero i
    linarith [hi.1, hi.2]
  · have hi := h i
    have hz := hzero i
    linarith [hi.1, hi.2]

theorem bounds_width_lt_of_within_ne {q r : Bounds ι} (h : Within q r)
    (hne : q ≠ r) : width q < width r := by
  by_contra hn
  exact hne (bounds_eq_of_within_width_eq h
    (le_antisymm (bounds_width_le h) (le_of_not_gt hn)))

/-- A greatest box is the unique width maximizer over any family it belongs to.
The concrete LP correspondence must establish this family and greatestness. -/
theorem bounds_greatest_unique_width (S : Set (Bounds ι)) (q : Bounds ι)
    (hq : q ∈ S) (hgreatest : ∀ r ∈ S, Within r q) :
    (q ∈ S ∧ ∀ r ∈ S, width r ≤ width q) ∧
    ∀ r ∈ S, width q ≤ width r → r = q := by
  refine ⟨⟨hq, fun r hr => bounds_width_le (hgreatest r hr)⟩, ?_⟩
  intro r hr hw
  exact bounds_eq_of_within_width_eq (hgreatest r hr)
    (le_antisymm (bounds_width_le (hgreatest r hr)) hw)

end Chapter02FBBT
