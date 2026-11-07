module

public import Chapter02KLWSource
public import Mathlib

@[expose] public section
set_option maxHeartbeats 800000
noncomputable section
open scoped BigOperators
open Chapter02
namespace Chapter02KLWExamples


def squares {I : Type*} [Fintype I] (x : I → ℝ) : ℝ := ∑ i, (x i)^2

def dsquares {I : Type*} [Fintype I] (x : I → ℝ) : (I → ℝ) →L[ℝ] ℝ :=
  ∑ i, (2*x i) • ContinuousLinearMap.proj i

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
theorem squares_derivative {I : Type*} [Fintype I] (x : I → ℝ) :
    HasFDerivAt squares (dsquares x) x := by
  apply HasFDerivAt.fun_sum
  intro i _
  have h := (hasDerivAt_pow 2 (x i)).comp_hasFDerivAt x
    (ContinuousLinearMap.proj i : (I → ℝ) →L[ℝ] ℝ).hasFDerivAt
  simpa only [Function.comp_def, ContinuousLinearMap.proj_apply, Nat.cast_ofNat, Nat.reduceSub, pow_one] using h

theorem squares_continuous {I : Type*} [Fintype I] :
    Continuous (squares : (I → ℝ) → ℝ) :=
  continuous_iff_continuousAt.mpr (fun x => (squares_derivative x).continuousAt)

theorem squares_strict {I : Type*} [Fintype I] :
    StrictConvexOn ℝ Set.univ (squares : (I → ℝ) → ℝ) := by
  classical
  have hs : StrictConvexOn ℝ Set.univ (fun t : ℝ => t^2) :=
    (by decide : Even 2).strictConvexOn_pow (by norm_num)
  refine ⟨convex_univ, ?_⟩
  intro x _ y _ hxy a b ha hb hab
  obtain ⟨k,hk⟩ := Function.ne_iff.mp hxy
  simp only [squares, Pi.add_apply, Pi.smul_apply, smul_eq_mul,
    Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_lt_sum
  · intro i _
    exact hs.convexOn.2 (Set.mem_univ _) (Set.mem_univ _) ha.le hb.le hab
  · exact ⟨k,Finset.mem_univ _,hs.2 (Set.mem_univ _) (Set.mem_univ _) hk ha hb hab⟩



def point2 (u v : ℝ) : Fin 2 → ℝ := ![u,v]
def point3 (u v w : ℝ) : Fin 3 → ℝ := ![u,v,w]
@[simp] theorem point3_zero (u v w : ℝ) : point3 u v w 0 = u := rfl
@[simp] theorem point3_one (u v w : ℝ) : point3 u v w 1 = v := rfl
@[simp] theorem point3_two (u v w : ℝ) : point3 u v w 2 = w := rfl

def box (n : ℕ) : Set (Fin n → ℝ) := {x | ∀ k, 0 ≤ x k ∧ x k ≤ 1}
def diagonal : Set (Fin 2 → ℝ) := {x | x ∈ box 2 ∧ x 0 = x 1}
def oneVarying (j : Fin 2) : Fin 2 → ℝ := if j=0 then point2 0 0 else point2 1 0
def cartesian : Fin 4 → Fin 2 → ℝ :=
  ![point2 0 0, point2 1 0, point2 0 1, point2 1 1]
@[simp] theorem cartesian_zero : cartesian 0 = point2 0 0 := rfl
@[simp] theorem cartesian_one : cartesian 1 = point2 1 0 := rfl
@[simp] theorem cartesian_two : cartesian 2 = point2 0 1 := rfl
@[simp] theorem cartesian_three : cartesian 3 = point2 1 1 := rfl

def diagonalAnchor (j : Fin 2) : Fin 2 → ℝ := if j=0 then point2 0 0 else point2 1 1
def overlapAnchor (j : Fin 2) : Fin 3 → ℝ := if j=0 then point3 0 0 0 else point3 1 0 1

def singletonCoordinate (i : Fin 2) : Fin 1 ↪ Fin 2 :=
  ⟨fun _ => i, fun _ _ _ => Subsingleton.elim _ _⟩
abbrev overlapSize (i : Fin 3) : ℕ := if i.val = 2 then 1 else 2

def overlapCoordinate (i : Fin 3) : Fin (overlapSize i) ↪ Fin 3 where
  toFun k := ⟨if i.val=0 then k.val else if i.val=1 then k.val+1 else 1, by
    have hi := i.isLt
    have hk := k.isLt
    dsimp [overlapSize] at hk
    split_ifs at hk ⊢ <;> omega⟩
  inj' := by
    intro a b h
    have hv := congrArg Fin.val h
    apply Fin.ext
    have hi := i.isLt
    have ha := a.isLt
    have hb := b.isLt
    dsimp [overlapSize] at ha hb
    dsimp at hv
    split_ifs at hv <;> split_ifs at ha hb <;> omega

theorem coordinate_proper {n d : ℕ} (e : Fin n ↪ Fin d) (h : n < d) :
    Set.range e ≠ Set.univ := by
  intro heq
  have hs : Function.Surjective e := Set.range_eq_univ.mp heq
  have hc := Fintype.card_le_of_surjective e hs
  simp only [Fintype.card_fin] at hc
  omega

theorem singleton_proper (i : Fin 2) : Set.range (singletonCoordinate i) ≠ Set.univ :=
  coordinate_proper _ (by norm_num)

theorem overlap_proper (i : Fin 3) : Set.range (overlapCoordinate i) ≠ Set.univ := by
  apply coordinate_proper
  fin_cases i <;> norm_num [overlapSize]

theorem box_zero (n : ℕ) : (0 : Fin n → ℝ) ∈ box n := by
  intro k; simp

theorem all_anchors_in_box :
    (∀ j, oneVarying j ∈ box 2) ∧ (∀ j, cartesian j ∈ box 2) ∧
    (∀ j, diagonalAnchor j ∈ box 2) ∧ (∀ j, overlapAnchor j ∈ box 3) := by
  refine ⟨?_,?_,?_,?_⟩ <;> intro j k <;> fin_cases j <;> fin_cases k <;>
    norm_num [oneVarying,cartesian,diagonalAnchor,overlapAnchor,point2,point3]

theorem cartesian_injective : Function.Injective cartesian := by
  intro i j h
  have h0 := congrFun h 0
  have h1 := congrFun h 1
  fin_cases i <;> fin_cases j <;> simp_all [cartesian,point2]

theorem cartesian_max_identity (p q : ℝ) :
    max (max 0 p) (max q (p+q)) = max 0 p + max 0 q := by
  simp only [max_def]
  split_ifs <;> linarith

theorem diagonal_max_identity (t : ℝ) :
    max 0 (4*t-2) = max 0 (2*t-1) + max 0 (2*t-1) := by
  simp only [max_def]
  split_ifs <;> linarith

theorem scalar_envelope_bounds {t : ℝ} (ht : 0 ≤ t ∧ t ≤ 1) :
    0 ≤ max 0 (2*t-1) ∧ max 0 (2*t-1) ≤ 1 := by
  exact ⟨le_max_left _ _, max_le (by norm_num) (by linarith [ht.2])⟩


def sharedAgreement {n m : ℕ} (size : Fin m → ℕ)
    (coordinate : (i : Fin m) → Fin (size i) ↪ Fin n) (a b : Fin n → ℝ) : Prop :=
  ∀ i k, i ≠ k → ∀ u v, coordinate i u = coordinate k v →
    a (coordinate i u) = b (coordinate i u)

theorem singleton_shared (a b : Fin 2 → ℝ) :
    sharedAgreement (fun _ => 1) singletonCoordinate a b := by
  intro i k hne u v heq
  exact (hne heq).elim

theorem overlap_shared : sharedAgreement overlapSize overlapCoordinate
    (overlapAnchor 0) (overlapAnchor 1) := by
  intro i k hne u v heq
  fin_cases i <;> fin_cases k <;> try contradiction
  all_goals fin_cases u <;> fin_cases v <;>
    simp_all [overlapCoordinate,overlapSize,overlapAnchor,point3,Fin.ext_iff]

theorem genuine_overlap : ∃ i k : Fin 3, i ≠ k ∧
    ∃ u v, overlapCoordinate i u = overlapCoordinate k v := by
  exact ⟨0,1,by decide,⟨1,by decide⟩,⟨0,by decide⟩,by decide⟩

theorem selected_anchors_distinct :
    oneVarying 0 ≠ oneVarying 1 ∧ cartesian 0 ≠ cartesian 3 ∧
    diagonalAnchor 0 ≠ diagonalAnchor 1 ∧ overlapAnchor 0 ≠ overlapAnchor 1 := by
  refine ⟨?_,?_,?_,?_⟩ <;> intro h <;> have hc := congrFun h 0 <;>
    change (0 : ℝ) = 1 at hc
  all_goals norm_num at hc


def quadraticData {d m : ℕ} (size : Fin m → ℕ)
    (coordinate : (i : Fin m) → Fin (size i) ↪ Fin d)
    (proper : ∀ i, Set.range (coordinate i) ≠ Set.univ) : KLWData d m where
  size := size
  coordinate := coordinate
  proper := proper
  component := fun _ => squares
  domain := fun _ => Set.univ

def singletonData : KLWData 2 2 := quadraticData (fun _ => 1) singletonCoordinate singleton_proper
def overlapData : KLWData 3 3 := quadraticData overlapSize overlapCoordinate overlap_proper

/-- Compatibility-only evaluation of the unchanged singleton block projection;
this private helper receives no separate source claim or proof credit. -/
private lemma singleton_projection_compat (i : Fin 2) (x : RealVector 2) :
    klwProjection singletonData i x = fun _ => x i := by
  funext k
  exact klw_projection_apply singletonData i x k

def quadraticL {d m : ℕ} {J : Type*} (S : KLWData d m) (a : J → RealVector d)
    (i : Fin m) (j : J) : RealVector (S.size i) →L[ℝ] ℝ :=
  dsquares (klwProjection S i (a j))

/-- Literal source premises and the explicitly proved global analytic conventions.
The record contains no envelope equality, strict gap, or desired conclusion. -/
structure LiteralControl {n : ℕ} {J : Type*} (S : KLWData n n)
    (a : J → RealVector n)
    (L : (i : Fin n) → J → RealVector (S.size i) →L[ℝ] ℝ)
    (first : J) (tail : List J) (p q : J) (K : Set (RealVector n)) : Prop where
  positive_dimension : 0 < n
  component_nonempty : ∀ i, 0 < S.size i
  proper_blocks : ∀ i, klwBlock S i ≠ Set.univ
  full_component_domains : ∀ i, S.domain i = Set.univ
  continuous_components : ∀ i, Continuous (S.component i)
  differentiable_components : ∀ i, Differentiable ℝ (S.component i)
  strictly_convex_components : ∀ i, StrictConvexOn ℝ (S.domain i) (S.component i)
  actual_anchor_derivatives : ∀ i j, HasFDerivAt (S.component i) (L i j)
    (klwProjection S i (a j))
  actual_whole_anchor_derivatives : ∀ j, HasFDerivAt (klwFunction S)
    (klwWholeDerivative S L j) (a j)
  continuous_whole : Continuous (klwFunction S)
  differentiable_whole : Differentiable ℝ (klwFunction S)
  convex_whole : ConvexOn ℝ Set.univ (klwFunction S)
  selected_first_present : p ∈ first :: tail
  selected_second_present : q ∈ first :: tail
  selected_distinct : a p ≠ a q
  anchors_retained : ∀ j ∈ first :: tail, a j ∈ K
  shared_coordinates_equal : klwSharedCoordinatesAgree S (a p) (a q)

theorem shared_agreement_to_source {n m : ℕ} (S : KLWData n m)
    (a b : RealVector n) (h : sharedAgreement S.size S.coordinate a b) :
    klwSharedCoordinatesAgree S a b := by
  intro i k hne r hr hs
  obtain ⟨u,hu⟩ := hr
  obtain ⟨v,hv⟩ := hs
  rw [← hu]
  exact h i k hne u v (hu.trans hv.symm)

theorem quadratic_literal {n : ℕ} {J : Type*}
    (size : Fin n → ℕ) (coordinate : (i : Fin n) → Fin (size i) ↪ Fin n)
    (proper : ∀ i, Set.range (coordinate i) ≠ Set.univ)
    (hn : 0 < n) (hsize : ∀ i, 0 < size i)
    (a : J → RealVector n) (first : J) (tail : List J) (p q : J)
    (hp : p ∈ first :: tail) (hq : q ∈ first :: tail) (hpq : a p ≠ a q)
    (K : Set (RealVector n)) (ha : ∀ j ∈ first :: tail, a j ∈ K)
    (hshared : sharedAgreement size coordinate (a p) (a q)) :
    LiteralControl (quadraticData size coordinate proper) a
      (quadraticL (quadraticData size coordinate proper) a) first tail p q K := by
  let S := quadraticData size coordinate proper
  have hw (x : RealVector n) : HasFDerivAt (klwFunction S)
      (klwWholeDerivative S (quadraticL S (fun _ : Unit => x)) ()) x :=
    klw_whole_derivative S (fun _ : Unit => x) (quadraticL S (fun _ : Unit => x)) ()
      (fun _ => squares_derivative _)
  refine ⟨hn,hsize,fun i => proper i,fun _ => rfl,fun _ => squares_continuous,
    fun _ x => (squares_derivative x).differentiableAt,fun _ => squares_strict,
    fun _ _ => squares_derivative _,
    fun j => klw_whole_derivative S a (quadraticL S a) j (fun _ => squares_derivative _),
    continuous_iff_continuousAt.mpr (fun x => (hw x).continuousAt),
    fun x => (hw x).differentiableAt,?_,hp,hq,hpq,ha,?_⟩
  · refine ⟨convex_univ,?_⟩
    intro x _ y _ α β hα hβ hab
    simp only [klwFunction,quadraticData,smul_eq_mul,Finset.mul_sum,← Finset.sum_add_distrib]
    apply Finset.sum_le_sum
    intro i _
    have hc := (squares_strict (I := Fin (size i))).convexOn.2
      (Set.mem_univ (klwProjection S i x)) (Set.mem_univ (klwProjection S i y)) hα hβ hab
    change squares (klwProjection S i (α • x + β • y)) ≤
      α * squares (klwProjection S i x) + β * squares (klwProjection S i y)
    rw [(klwProjection S i).map_add,
      (klwProjection S i).map_smul, (klwProjection S i).map_smul]
    exact hc
  · exact shared_agreement_to_source S (a p) (a q) hshared

def c1A := klwDirectEnvelope singletonData oneVarying (quadraticL singletonData oneVarying) 0 [1]
def c1B := klwComponentEnvelope singletonData oneVarying (quadraticL singletonData oneVarying) 0 [1]
def c2A := klwDirectEnvelope singletonData cartesian (quadraticL singletonData cartesian) 0 [1,2,3]
def c2B := klwComponentEnvelope singletonData cartesian (quadraticL singletonData cartesian) 0 [1,2,3]
def p1A := klwDirectEnvelope singletonData diagonalAnchor (quadraticL singletonData diagonalAnchor) 0 [1]
def p1B := klwComponentEnvelope singletonData diagonalAnchor (quadraticL singletonData diagonalAnchor) 0 [1]
def p2A := klwDirectEnvelope overlapData overlapAnchor (quadraticL overlapData overlapAnchor) 0 [1]
def p2B := klwComponentEnvelope overlapData overlapAnchor (quadraticL overlapData overlapAnchor) 0 [1]

theorem singleton_function (x : RealVector 2) :
    klwFunction singletonData x = (x 0)^2 + (x 1)^2 := by
  change (∑ i : Fin 2, squares (klwProjection singletonData i x)) = _
  simp_rw [singleton_projection_compat]
  rw [Fin.sum_univ_two]
  change squares (fun _ : Fin 1 => x 0) + squares (fun _ : Fin 1 => x 1) = _
  simp only [squares, Fin.sum_univ_one]

theorem singleton_row {J : Type*} (a : J → RealVector 2) (i : Fin 2) (j : J)
    (x : RealVector 2) :
    klwRow singletonData a (quadraticL singletonData a) i j x =
      2*(a j i)*(x i)-(a j i)^2 := by
  change squares (klwProjection singletonData i (a j)) +
    dsquares (klwProjection singletonData i (a j))
      (klwProjection singletonData i x - klwProjection singletonData i (a j)) = _
  rw [singleton_projection_compat, singleton_projection_compat]
  change squares (fun _ : Fin 1 => a j i) +
    dsquares (fun _ : Fin 1 => a j i) ((fun _ : Fin 1 => x i) - (fun _ : Fin 1 => a j i)) = _
  simp [squares, dsquares, Fin.sum_univ_one, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.proj_apply, Pi.sub_apply, smul_eq_mul]
  ring

theorem singleton_whole_row {J : Type*} (a : J → RealVector 2) (j : J)
    (x : RealVector 2) :
    klwWholeRow singletonData a (quadraticL singletonData a) j x =
      (2*(a j 0)*(x 0)-(a j 0)^2) + (2*(a j 1)*(x 1)-(a j 1)^2) := by
  rw [klw_whole_row_eq_sum,Fin.sum_univ_two,singleton_row,singleton_row]

theorem c1_formulas (x : RealVector 2) :
    c1A x = max 0 (2*x 0-1) ∧ c1B x = max 0 (2*x 0-1) := by
  simp [c1A,c1B,klwDirectEnvelope,klwComponentEnvelope,pscEnvelope,pscEnvelopeTail,
    Fin.sum_univ_two,singleton_whole_row,singleton_row,oneVarying,point2,max_comm]

theorem c2_formulas (x : RealVector 2) :
    c2A x = max 0 (2*x 0-1)+max 0 (2*x 1-1) ∧
    c2B x = max 0 (2*x 0-1)+max 0 (2*x 1-1) := by
  constructor
  · simp only [c2A,klwDirectEnvelope,pscEnvelope,pscEnvelopeTail,singleton_whole_row]
    norm_num [point2]
    simp only [max_def]
    split_ifs <;> linarith
  · simp [c2B,klwComponentEnvelope,pscEnvelope,pscEnvelopeTail,Fin.sum_univ_two,
      singleton_row,point2,max_comm,max_left_comm,max_assoc]

theorem p1_formulas (x : RealVector 2) :
    p1A x = max 0 (2*x 0+2*x 1-2) ∧
    p1B x = max 0 (2*x 0-1)+max 0 (2*x 1-1) := by
  constructor
  · simp only [p1A,klwDirectEnvelope,pscEnvelope,pscEnvelopeTail,singleton_whole_row]
    norm_num [diagonalAnchor,point2]
    rw [max_comm]
    congr 1; ring
  · simp [p1B,klwComponentEnvelope,pscEnvelope,pscEnvelopeTail,Fin.sum_univ_two,
      singleton_row,diagonalAnchor,point2,max_comm]

theorem overlap_function (x : RealVector 3) :
    klwFunction overlapData x = (x 0)^2+3*(x 1)^2+(x 2)^2 := by
  change (∑ i : Fin 3, squares (fun k => x (overlapCoordinate i k))) = _
  rw [Fin.sum_univ_succ,Fin.sum_univ_two]
  change squares (fun k : Fin 2 => x (overlapCoordinate 0 k)) +
    (squares (fun k : Fin 2 => x (overlapCoordinate 1 k)) +
      squares (fun k : Fin 1 => x (overlapCoordinate 2 k))) = _
  simp only [squares,Fin.sum_univ_two,Fin.sum_univ_one]
  norm_num [overlapCoordinate,overlapSize]
  ring_nf

theorem overlap_row (i : Fin 3) (j : Fin 2) (x : RealVector 3) :
    klwRow overlapData overlapAnchor (quadraticL overlapData overlapAnchor) i j x =
      ∑ k : Fin (overlapSize i),
        (2*overlapAnchor j (overlapCoordinate i k)*x (overlapCoordinate i k) -
          (overlapAnchor j (overlapCoordinate i k))^2) := by
  change squares (fun k => overlapAnchor j (overlapCoordinate i k)) +
    dsquares (fun k => overlapAnchor j (overlapCoordinate i k))
      (fun k => x (overlapCoordinate i k)-overlapAnchor j (overlapCoordinate i k)) = _
  simp only [squares,dsquares,ContinuousLinearMap.sum_apply,ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.proj_apply,smul_eq_mul,← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro k _; ring

theorem overlap_row_first (j : Fin 2) (x : RealVector 3) :
    klwRow overlapData overlapAnchor (quadraticL overlapData overlapAnchor) 0 j x =
      (2*overlapAnchor j 0*x 0-(overlapAnchor j 0)^2) +
      (2*overlapAnchor j 1*x 1-(overlapAnchor j 1)^2) := by
  rw [overlap_row]
  change (∑ k : Fin 2, (2*overlapAnchor j (overlapCoordinate 0 k)*x (overlapCoordinate 0 k) -
    (overlapAnchor j (overlapCoordinate 0 k))^2)) = _
  rw [Fin.sum_univ_two]
  rfl

theorem overlap_row_second (j : Fin 2) (x : RealVector 3) :
    klwRow overlapData overlapAnchor (quadraticL overlapData overlapAnchor) 1 j x =
      (2*overlapAnchor j 1*x 1-(overlapAnchor j 1)^2) +
      (2*overlapAnchor j 2*x 2-(overlapAnchor j 2)^2) := by
  rw [overlap_row]
  change (∑ k : Fin 2, (2*overlapAnchor j (overlapCoordinate 1 k)*x (overlapCoordinate 1 k) -
    (overlapAnchor j (overlapCoordinate 1 k))^2)) = _
  rw [Fin.sum_univ_two]
  rfl

theorem overlap_row_third (j : Fin 2) (x : RealVector 3) :
    klwRow overlapData overlapAnchor (quadraticL overlapData overlapAnchor) 2 j x =
      2*overlapAnchor j 1*x 1-(overlapAnchor j 1)^2 := by
  rw [overlap_row]
  change (∑ k : Fin 1, (2*overlapAnchor j (overlapCoordinate 2 k)*x (overlapCoordinate 2 k) -
    (overlapAnchor j (overlapCoordinate 2 k))^2)) = _
  rw [Fin.sum_univ_one]
  rfl

theorem overlap_rows (x : RealVector 3) :
    (∀ i, klwRow overlapData overlapAnchor (quadraticL overlapData overlapAnchor) i 0 x = 0) ∧
    klwRow overlapData overlapAnchor (quadraticL overlapData overlapAnchor) 0 1 x = 2*x 0-1 ∧
    klwRow overlapData overlapAnchor (quadraticL overlapData overlapAnchor) 1 1 x = 2*x 2-1 ∧
    klwRow overlapData overlapAnchor (quadraticL overlapData overlapAnchor) 2 1 x = 0 := by
  refine ⟨?_,?_,?_,?_⟩
  · intro i; fin_cases i <;> simp [overlap_row_first,overlap_row_second,overlap_row_third,overlapAnchor]
  all_goals simp [overlap_row_first,overlap_row_second,overlap_row_third,overlapAnchor]

theorem p2_formulas (x : RealVector 3) :
    p2A x = max 0 (2*x 0+2*x 2-2) ∧
    p2B x = max 0 (2*x 0-1)+max 0 (2*x 2-1) := by
  obtain ⟨h0,h10,h11,h12⟩ := overlap_rows x
  have hw0 : klwWholeRow overlapData overlapAnchor (quadraticL overlapData overlapAnchor) 0 x = 0 := by
    rw [klw_whole_row_eq_sum]; simp [h0]
  have hw1 : klwWholeRow overlapData overlapAnchor (quadraticL overlapData overlapAnchor) 1 x =
      2*x 0+2*x 2-2 := by
    rw [klw_whole_row_eq_sum]
    norm_num [Fin.sum_univ_succ,h10,h11,h12]
    ring
  constructor
  · simp [p2A,klwDirectEnvelope,pscEnvelope,pscEnvelopeTail,hw0,hw1,max_comm]
  · simp [p2B,klwComponentEnvelope,pscEnvelope,pscEnvelopeTail,Fin.sum_univ_succ,
      h0,h10,h11,h12,max_comm]

theorem literal_singleton {J : Type*} (a : J → RealVector 2) (first : J)
    (tail : List J) (p q : J) (hp : p ∈ first :: tail) (hq : q ∈ first :: tail)
    (hpq : a p ≠ a q) (ha : ∀ j ∈ first :: tail, a j ∈ box 2) :
    LiteralControl singletonData a (quadraticL singletonData a) first tail p q (box 2) :=
  quadratic_literal (fun _ => 1) singletonCoordinate singleton_proper (by norm_num)
    (fun _ => by norm_num) a first tail p q hp hq hpq (box 2) ha
    (singleton_shared _ _)

theorem c1_literal : LiteralControl singletonData oneVarying
    (quadraticL singletonData oneVarying) 0 [1] 0 1 (box 2) :=
  literal_singleton _ _ _ _ _ (by simp) (by simp) selected_anchors_distinct.1
    (fun j _ => all_anchors_in_box.1 j)

theorem c2_literal : LiteralControl singletonData cartesian
    (quadraticL singletonData cartesian) 0 [1,2,3] 0 3 (box 2) :=
  literal_singleton _ _ _ _ _ (by simp) (by simp) selected_anchors_distinct.2.1
    (fun j _ => all_anchors_in_box.2.1 j)

theorem p1_literal : LiteralControl singletonData diagonalAnchor
    (quadraticL singletonData diagonalAnchor) 0 [1] 0 1 (box 2) :=
  literal_singleton _ _ _ _ _ (by simp) (by simp) selected_anchors_distinct.2.2.1
    (fun j _ => all_anchors_in_box.2.2.1 j)

theorem p2_literal : LiteralControl overlapData overlapAnchor
    (quadraticL overlapData overlapAnchor) 0 [1] 0 1 (box 3) := by
  exact quadratic_literal overlapSize overlapCoordinate overlap_proper (by norm_num)
    (by intro i; fin_cases i <;> norm_num [overlapSize]) overlapAnchor 0 [1] 0 1
    (by simp) (by simp) selected_anchors_distinct.2.2.2 (box 3)
    (fun j _ => all_anchors_in_box.2.2.2 j) overlap_shared

theorem c2_both_projections_change : ∀ i,
    klwProjection singletonData i (cartesian 0) ≠ klwProjection singletonData i (cartesian 3) := by
  intro i h
  have hc := congrFun h ⟨0,by norm_num [singletonData,quadraticData]⟩
  fin_cases i <;> change (0 : ℝ) = 1 at hc <;> norm_num at hc

theorem p1_cover : ∀ i, ∃ j ∈ (0 : Fin 2) :: [1],
    klwProjection singletonData i (point2 0 1) = klwProjection singletonData i (diagonalAnchor j) := by
  intro i
  fin_cases i
  · refine ⟨0, by simp, ?_⟩
    rw [singleton_projection_compat, singleton_projection_compat]
    rfl
  · refine ⟨1, by simp, ?_⟩
    rw [singleton_projection_compat, singleton_projection_compat]
    rfl

theorem p1_separation : ∀ j ∈ (0 : Fin 2) :: [1], ∃ i,
    klwProjection singletonData i (point2 0 1) ≠ klwProjection singletonData i (diagonalAnchor j) := by
  intro j _; fin_cases j
  · refine ⟨1,?_⟩; intro h; have hc := congrFun h ⟨0,by norm_num [singletonData,quadraticData]⟩
    change (1 : ℝ) = 0 at hc; norm_num at hc
  · refine ⟨0,?_⟩; intro h; have hc := congrFun h ⟨0,by norm_num [singletonData,quadraticData]⟩
    change (0 : ℝ) = 1 at hc; norm_num at hc

theorem p2_cover : ∀ i, ∃ j ∈ (0 : Fin 2) :: [1],
    klwProjection overlapData i (point3 0 0 1) = klwProjection overlapData i (overlapAnchor j) := by
  intro i; fin_cases i
  · refine ⟨0,by simp,?_⟩
    funext k
    change point3 0 0 1 (overlapCoordinate 0 k) = overlapAnchor 0 (overlapCoordinate 0 k)
    fin_cases k <;> norm_num [overlapCoordinate,overlapSize,point3,overlapAnchor]
  · refine ⟨1,by simp,?_⟩
    funext k
    change point3 0 0 1 (overlapCoordinate 1 k) = overlapAnchor 1 (overlapCoordinate 1 k)
    fin_cases k <;> norm_num [overlapCoordinate,overlapSize,point3,overlapAnchor]
  · refine ⟨0,by simp,?_⟩
    funext k
    change point3 0 0 1 (overlapCoordinate 2 k) = overlapAnchor 0 (overlapCoordinate 2 k)
    fin_cases k; norm_num [overlapCoordinate,overlapSize,point3,overlapAnchor]

theorem p2_separation : ∀ j ∈ (0 : Fin 2) :: [1], ∃ i,
    klwProjection overlapData i (point3 0 0 1) ≠ klwProjection overlapData i (overlapAnchor j) := by
  intro j _; fin_cases j
  · refine ⟨1,?_⟩; intro h
    have hc := congrFun h ⟨1,by norm_num [overlapData,quadraticData,overlapSize]⟩
    change (1 : ℝ) = 0 at hc; norm_num at hc
  · refine ⟨0,?_⟩; intro h
    have hc := congrFun h ⟨0,by norm_num [overlapData,quadraticData,overlapSize]⟩
    change (0 : ℝ) = 1 at hc; norm_num at hc

/-- Actual generic-repair invocation, with derived component strict support. -/
theorem p1_repair_application :
    p1A (point2 0 1) < p1B (point2 0 1) ∧
    p1B (point2 0 1) = klwFunction singletonData (point2 0 1) ∧
    (∀ x, p1A x ≤ p1B x ∧ p1B x ≤ klwFunction singletonData x) ∧
    (∃ r, (point2 0 1,r) ∈ klwEpigraph (box 2) p1A ∧
      (point2 0 1,r) ∉ klwEpigraph (box 2) p1B) := by
  have h := klw_strictness_of_covered_separated_point singletonData diagonalAnchor
    (quadraticL singletonData diagonalAnchor) 0 [1] (fun _ _ _ => Set.mem_univ _)
    p1_literal.strictly_convex_components (fun i j _ => p1_literal.actual_anchor_derivatives i j)
    (box 2) (fun _ _ _ => Set.mem_univ _) (point2 0 1)
    (by intro k; fin_cases k <;> norm_num [point2]) p1_cover p1_separation
  exact ⟨h.1,h.2.1,fun x => h.2.2.1 x (fun _ => Set.mem_univ _),h.2.2.2⟩

/-- Actual generic-repair invocation for genuinely overlapping coordinate blocks. -/
theorem p2_repair_application :
    p2A (point3 0 0 1) < p2B (point3 0 0 1) ∧
    p2B (point3 0 0 1) = klwFunction overlapData (point3 0 0 1) ∧
    (∀ x, p2A x ≤ p2B x ∧ p2B x ≤ klwFunction overlapData x) ∧
    (∃ r, (point3 0 0 1,r) ∈ klwEpigraph (box 3) p2A ∧
      (point3 0 0 1,r) ∉ klwEpigraph (box 3) p2B) := by
  have h := klw_strictness_of_covered_separated_point overlapData overlapAnchor
    (quadraticL overlapData overlapAnchor) 0 [1] (fun _ _ _ => Set.mem_univ _)
    p2_literal.strictly_convex_components (fun i j _ => p2_literal.actual_anchor_derivatives i j)
    (box 3) (fun _ _ _ => Set.mem_univ _) (point3 0 0 1)
    (by intro k; fin_cases k <;> norm_num [point3]) p2_cover p2_separation
  exact ⟨h.1,h.2.1,fun x => h.2.2.1 x (fun _ => Set.mem_univ _),h.2.2.2⟩

theorem p1_exact_values :
    p1A (point2 0 1) = 0 ∧ p1B (point2 0 1) = 1 ∧
    klwFunction singletonData (point2 0 1) = 1 := by
  rw [(p1_formulas _).1,(p1_formulas _).2,singleton_function]
  norm_num [point2]

theorem p2_exact_values :
    p2A (point3 0 0 1) = 0 ∧ p2B (point3 0 0 1) = 1 ∧
    klwFunction overlapData (point3 0 0 1) = 1 := by
  rw [(p2_formulas _).1,(p2_formulas _).2,overlap_function]
  norm_num [point3_zero,point3_one,point3_two]

theorem free_height_gaps :
    ((point2 0 1,(1:ℝ)/2) ∈ klwEpigraph (box 2) p1A ∧
      (point2 0 1,(1:ℝ)/2) ∉ klwEpigraph (box 2) p1B) ∧
    ((point3 0 0 1,(1:ℝ)/2) ∈ klwEpigraph (box 3) p2A ∧
      (point3 0 0 1,(1:ℝ)/2) ∉ klwEpigraph (box 3) p2B) := by
  refine ⟨⟨⟨?_,?_⟩,?_⟩,⟨⟨?_,?_⟩,?_⟩⟩
  · intro k; fin_cases k <;> norm_num [point2]
  · rw [p1_exact_values.1]; norm_num
  · intro h; have hh := h.2; rw [p1_exact_values.2.1] at hh; norm_num at hh
  · intro k; fin_cases k <;> norm_num [point3]
  · rw [p2_exact_values.1]; norm_num
  · intro h; have hh := h.2; rw [p2_exact_values.2.1] at hh; norm_num at hh

theorem original_epigraphs_nonempty :
    (klwEpigraph (box 2) (klwFunction singletonData)).Nonempty ∧
    (klwEpigraph diagonal (klwFunction singletonData)).Nonempty ∧
    (klwEpigraph (box 3) (klwFunction overlapData)).Nonempty := by
  refine ⟨⟨(0,0),box_zero 2,?_⟩,⟨(0,0),⟨box_zero 2,rfl⟩,?_⟩,
    ⟨(0,0),box_zero 3,?_⟩⟩
  · rw [singleton_function]; simp
  · rw [singleton_function]; simp
  · rw [overlap_function]; simp

theorem diagonal_domain_limit :
    (∀ j, diagonalAnchor j ∈ diagonal) ∧ point2 0 1 ∉ diagonal ∧
    (∀ x ∈ diagonal, p1A x = p1B x) := by
  refine ⟨?_,?_,?_⟩
  · intro j; refine ⟨all_anchors_in_box.2.2.1 j,?_⟩
    fin_cases j <;> norm_num [diagonalAnchor,point2]
  · intro h; have hh := h.2; norm_num [point2] at hh
  · intro x hx
    rw [(p1_formulas x).1,(p1_formulas x).2,hx.2]
    convert diagonal_max_identity (x 1) using 1; congr 1; ring

theorem attained_minima_limit :
    p1A 0 = 0 ∧ p1B 0 = 0 ∧ klwFunction singletonData 0 = 0 ∧
    IsMinimizer (box 2) p1A 0 ∧ IsMinimizer (box 2) p1B 0 ∧
    IsMinimizer (box 2) (klwFunction singletonData) 0 := by
  have ha : p1A 0 = 0 := by rw [(p1_formulas _).1]; norm_num
  have hb : p1B 0 = 0 := by rw [(p1_formulas _).2]; norm_num
  have hf : klwFunction singletonData 0 = 0 := by rw [singleton_function]; norm_num
  refine ⟨ha,hb,hf,⟨box_zero 2,?_⟩,⟨box_zero 2,?_⟩,⟨box_zero 2,?_⟩⟩
  · intro x _; rw [ha,(p1_formulas x).1]; exact le_max_left _ _
  · intro x _; rw [hb,(p1_formulas x).2]
    exact add_nonneg (le_max_left _ _) (le_max_left _ _)
  · intro x _; rw [hf,singleton_function]
    exact add_nonneg (sq_nonneg _) (sq_nonneg _)

theorem prescribed_threshold_limit :
    {x ∈ box 2 | p1A x ≤ 2} = box 2 ∧ {x ∈ box 2 | p1B x ≤ 2} = box 2 := by
  have hb (x : RealVector 2) (hx : x ∈ box 2) : p1B x ≤ 2 := by
    rw [(p1_formulas x).2]
    have h0 := (scalar_envelope_bounds (hx 0)).2
    have h1 := (scalar_envelope_bounds (hx 1)).2
    linarith
  constructor
  · ext x; constructor
    · intro h; exact h.1
    · intro hx; exact ⟨hx,(p1_repair_application.2.2.1 x).1.trans (hb x hx)⟩
  · ext x; constructor
    · intro h; exact h.1
    · intro hx; exact ⟨hx,hb x hx⟩

/-- The prescribed-zero-level consequence uses actual components shifted by one. -/
def shiftedData : KLWData 2 2 :=
  { singletonData with component := fun _ u => squares u - 1 }
def shiftedA := klwDirectEnvelope shiftedData diagonalAnchor
  (quadraticL shiftedData diagonalAnchor) 0 [1]
def shiftedB := klwComponentEnvelope shiftedData diagonalAnchor
  (quadraticL shiftedData diagonalAnchor) 0 [1]

theorem shifted_analytic : ∀ i,
    Continuous (shiftedData.component i) ∧
    StrictConvexOn ℝ (shiftedData.domain i) (shiftedData.component i) ∧
    ∀ u, HasFDerivAt (shiftedData.component i) (dsquares u) u := by
  intro i
  refine ⟨squares_continuous.sub continuous_const,?_,fun u => (squares_derivative u).sub_const 1⟩
  change StrictConvexOn ℝ Set.univ (fun u : RealVector 1 => squares u-1)
  apply ((squares_strict (I := Fin 1)).add_const (-1)).congr
  intro u hu
  simp [sub_eq_add_neg, Pi.add_apply]

theorem shifted_function (x : RealVector 2) :
    klwFunction shiftedData x = klwFunction singletonData x - 2 := by
  change (∑ i : Fin 2, (squares (klwProjection singletonData i x)-1)) =
    (∑ i : Fin 2, squares (klwProjection singletonData i x))-2
  simp only [Fin.sum_univ_two]; ring

theorem shifted_row (i : Fin 2) (j : Fin 2) (x : RealVector 2) :
    klwRow shiftedData diagonalAnchor (quadraticL shiftedData diagonalAnchor) i j x =
      klwRow singletonData diagonalAnchor (quadraticL singletonData diagonalAnchor) i j x-1 := by
  change (squares (klwProjection singletonData i (diagonalAnchor j))-1) +
    quadraticL singletonData diagonalAnchor i j
      (klwProjection singletonData i x-klwProjection singletonData i (diagonalAnchor j)) =
    (squares (klwProjection singletonData i (diagonalAnchor j)) +
    quadraticL singletonData diagonalAnchor i j
      (klwProjection singletonData i x-klwProjection singletonData i (diagonalAnchor j)))-1
  ring

theorem shifted_whole_row (j : Fin 2) (x : RealVector 2) :
    klwWholeRow shiftedData diagonalAnchor (quadraticL shiftedData diagonalAnchor) j x =
      klwWholeRow singletonData diagonalAnchor (quadraticL singletonData diagonalAnchor) j x-2 := by
  simp only [klw_whole_row_eq_sum,Fin.sum_univ_two,shifted_row]
  ring

theorem shifted_envelopes (x : RealVector 2) :
    shiftedA x = p1A x-2 ∧ shiftedB x = p1B x-2 := by
  constructor
  · simp only [shiftedA,p1A,klwDirectEnvelope,pscEnvelope,pscEnvelopeTail,shifted_whole_row]
    exact max_sub_sub_right _ _ _
  · simp only [shiftedB,p1B,klwComponentEnvelope,Fin.sum_univ_two,
      pscEnvelope,pscEnvelopeTail,shifted_row,max_sub_sub_right]
    ring

theorem shifted_zero_level_limit :
    {x ∈ box 2 | shiftedA x ≤ 0} = box 2 ∧
    {x ∈ box 2 | shiftedB x ≤ 0} = box 2 := by
  have hA : {x ∈ box 2 | shiftedA x ≤ 0} = {x ∈ box 2 | p1A x ≤ 2} := by
    ext x; simp only [Set.mem_setOf_eq]
    rw [(shifted_envelopes x).1]
    constructor <;> rintro ⟨hx,hh⟩ <;> exact ⟨hx,by linarith⟩
  have hB : {x ∈ box 2 | shiftedB x ≤ 0} = {x ∈ box 2 | p1B x ≤ 2} := by
    ext x; simp only [Set.mem_setOf_eq]
    rw [(shifted_envelopes x).2]
    constructor <;> rintro ⟨hx,hh⟩ <;> exact ⟨hx,by linarith⟩
  exact ⟨hA.trans prescribed_threshold_limit.1,hB.trans prescribed_threshold_limit.2⟩

theorem counter_epigraph_identities (K : Set (RealVector 2)) :
    klwEpigraph K c1A = klwEpigraph K c1B ∧
    klwEpigraph K c2A = klwEpigraph K c2B := by
  refine ⟨congrArg (klwEpigraph K) (funext ?_),congrArg (klwEpigraph K) (funext ?_)⟩
  · intro x; exact (c1_formulas x).1.trans (c1_formulas x).2.symm
  · intro x; exact (c2_formulas x).1.trans (c2_formulas x).2.symm

theorem counter_approximants_nonempty :
    (klwEpigraph (box 2) c1A).Nonempty ∧ (klwEpigraph (box 2) c1B).Nonempty ∧
    (klwEpigraph (box 2) c2A).Nonempty ∧ (klwEpigraph (box 2) c2B).Nonempty := by
  refine ⟨⟨(0,0),box_zero 2,?_⟩,⟨(0,0),box_zero 2,?_⟩,
    ⟨(0,0),box_zero 2,?_⟩,⟨(0,0),box_zero 2,?_⟩⟩
  · rw [(c1_formulas _).1]; norm_num
  · rw [(c1_formulas _).2]; norm_num
  · rw [(c2_formulas _).1]; norm_num
  · rw [(c2_formulas _).2]; norm_num

theorem actual_overlapping_blocks : ∃ i k : Fin 3, i ≠ k ∧
    (klwBlock overlapData i ∩ klwBlock overlapData k).Nonempty := by
  refine ⟨0,1,by decide,1,?_,?_⟩
  · change ∃ u : Fin 2, overlapCoordinate 0 u = 1
    exact ⟨1,rfl⟩
  · change ∃ u : Fin 2, overlapCoordinate 1 u = 1
    exact ⟨0,rfl⟩

/-- C1 and C2 satisfy the literal analytic/source premises but have universal
whole/component envelope equality. All epigraph heights are free real values. -/
theorem klw_literal_strictness_countermodels :
    LiteralControl singletonData oneVarying (quadraticL singletonData oneVarying)
      0 [1] 0 1 (box 2) ∧
    LiteralControl singletonData cartesian (quadraticL singletonData cartesian)
      0 [1,2,3] 0 3 (box 2) ∧
    Function.Injective cartesian ∧
    (∀ i, klwProjection singletonData i (cartesian 0) ≠
      klwProjection singletonData i (cartesian 3)) ∧
    (∀ x, c1A x = max 0 (2*x 0-1) ∧ c1B x = max 0 (2*x 0-1)) ∧
    (∀ x, c2A x = max 0 (2*x 0-1)+max 0 (2*x 1-1) ∧
      c2B x = max 0 (2*x 0-1)+max 0 (2*x 1-1)) ∧
    (¬ ∃ x, c1A x < c1B x) ∧ (¬ ∃ x, c2A x < c2B x) ∧
    (∀ K, klwEpigraph K c1A = klwEpigraph K c1B ∧
      klwEpigraph K c2A = klwEpigraph K c2B) ∧
    ((0,0) ∈ klwEpigraph (box 2) (klwFunction singletonData)) ∧
    (klwEpigraph (box 2) (klwFunction singletonData)).Nonempty ∧
    (klwEpigraph (box 2) c1A).Nonempty ∧ (klwEpigraph (box 2) c1B).Nonempty ∧
    (klwEpigraph (box 2) c2A).Nonempty ∧ (klwEpigraph (box 2) c2B).Nonempty := by
  refine ⟨c1_literal,c2_literal,cartesian_injective,c2_both_projections_change,
    c1_formulas,c2_formulas,?_,?_,counter_epigraph_identities,?_,
    original_epigraphs_nonempty.1,counter_approximants_nonempty⟩
  · rintro ⟨x,hx⟩
    rw [(c1_formulas x).1,(c1_formulas x).2] at hx
    exact (lt_irrefl _ hx)
  · rintro ⟨x,hx⟩
    rw [(c2_formulas x).1,(c2_formulas x).2] at hx
    exact (lt_irrefl _ hx)
  · refine ⟨box_zero 2,?_⟩; rw [singleton_function]; simp

/-- P1 and P2 genuinely apply the repaired theorem. D1, D2 and D3 separately
retain domain admissibility, attained minima and a prescribed threshold.
The shifted zero-level model is derived from actual shifted components. -/
theorem klw_repair_nonvacuity_and_limits :
    LiteralControl singletonData diagonalAnchor (quadraticL singletonData diagonalAnchor)
      0 [1] 0 1 (box 2) ∧
    LiteralControl overlapData overlapAnchor (quadraticL overlapData overlapAnchor)
      0 [1] 0 1 (box 3) ∧
    (∃ i k : Fin 3, i ≠ k ∧ (klwBlock overlapData i ∩ klwBlock overlapData k).Nonempty) ∧
    (∀ x, klwFunction singletonData x = (x 0)^2+(x 1)^2) ∧
    (∀ x, klwFunction overlapData x = (x 0)^2+3*(x 1)^2+(x 2)^2) ∧
    (∀ x, p1A x = max 0 (2*x 0+2*x 1-2) ∧
      p1B x = max 0 (2*x 0-1)+max 0 (2*x 1-1)) ∧
    (∀ x, p2A x = max 0 (2*x 0+2*x 2-2) ∧
      p2B x = max 0 (2*x 0-1)+max 0 (2*x 2-1)) ∧
    (p1A (point2 0 1) < p1B (point2 0 1) ∧
      p1B (point2 0 1) = klwFunction singletonData (point2 0 1) ∧
      (∀ x, p1A x ≤ p1B x ∧ p1B x ≤ klwFunction singletonData x) ∧
      ∃ r, (point2 0 1,r) ∈ klwEpigraph (box 2) p1A ∧
        (point2 0 1,r) ∉ klwEpigraph (box 2) p1B) ∧
    (p2A (point3 0 0 1) < p2B (point3 0 0 1) ∧
      p2B (point3 0 0 1) = klwFunction overlapData (point3 0 0 1) ∧
      (∀ x, p2A x ≤ p2B x ∧ p2B x ≤ klwFunction overlapData x) ∧
      ∃ r, (point3 0 0 1,r) ∈ klwEpigraph (box 3) p2A ∧
        (point3 0 0 1,r) ∉ klwEpigraph (box 3) p2B) ∧
    (p1A (point2 0 1) = 0 ∧ p1B (point2 0 1) = 1 ∧
      klwFunction singletonData (point2 0 1) = 1) ∧
    (p2A (point3 0 0 1) = 0 ∧ p2B (point3 0 0 1) = 1 ∧
      klwFunction overlapData (point3 0 0 1) = 1) ∧
    (((point2 0 1,(1:ℝ)/2) ∈ klwEpigraph (box 2) p1A ∧
      (point2 0 1,(1:ℝ)/2) ∉ klwEpigraph (box 2) p1B) ∧
      ((point3 0 0 1,(1:ℝ)/2) ∈ klwEpigraph (box 3) p2A ∧
      (point3 0 0 1,(1:ℝ)/2) ∉ klwEpigraph (box 3) p2B)) ∧
    ((klwEpigraph (box 2) (klwFunction singletonData)).Nonempty ∧
      (klwEpigraph diagonal (klwFunction singletonData)).Nonempty ∧
      (klwEpigraph (box 3) (klwFunction overlapData)).Nonempty) ∧
    ((∀ j, diagonalAnchor j ∈ diagonal) ∧ point2 0 1 ∉ diagonal ∧
      ∀ x ∈ diagonal, p1A x = p1B x) ∧
    (p1A 0 = 0 ∧ p1B 0 = 0 ∧ klwFunction singletonData 0 = 0 ∧
      IsMinimizer (box 2) p1A 0 ∧ IsMinimizer (box 2) p1B 0 ∧
      IsMinimizer (box 2) (klwFunction singletonData) 0) ∧
    ({x ∈ box 2 | p1A x ≤ 2} = box 2 ∧ {x ∈ box 2 | p1B x ≤ 2} = box 2) ∧
    (∀ i, Continuous (shiftedData.component i) ∧
      StrictConvexOn ℝ (shiftedData.domain i) (shiftedData.component i) ∧
      ∀ u, HasFDerivAt (shiftedData.component i) (dsquares u) u) ∧
    (∀ x, klwFunction shiftedData x = klwFunction singletonData x-2) ∧
    (∀ x, shiftedA x = p1A x-2 ∧ shiftedB x = p1B x-2) ∧
    ({x ∈ box 2 | shiftedA x ≤ 0} = box 2 ∧ {x ∈ box 2 | shiftedB x ≤ 0} = box 2) := by
  exact ⟨p1_literal,p2_literal,actual_overlapping_blocks,singleton_function,overlap_function,
    p1_formulas,p2_formulas,p1_repair_application,p2_repair_application,
    p1_exact_values,p2_exact_values,free_height_gaps,original_epigraphs_nonempty,
    diagonal_domain_limit,attained_minima_limit,prescribed_threshold_limit,
    shifted_analytic,shifted_function,shifted_envelopes,shifted_zero_level_limit⟩

end Chapter02KLWExamples

#print axioms Chapter02KLWExamples.klw_literal_strictness_countermodels
#print axioms Chapter02KLWExamples.klw_repair_nonvacuity_and_limits
