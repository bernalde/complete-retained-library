module

public import Chapter03FPUnboundedObjectiveBoundedData

@[expose] public section

/-! Exact permitted first master choice with no next projection minimum.
Objective boundedness cannot supply every exact local optimizer, even with
finite hard integer bounds, convex C1 data, and attained initial/integer optima. -/
noncomputable section
open scoped BigOperators RealInnerProductSpace
open Chapter02 Chapter03.FP
namespace Chapter03.FPUnboundedObjectiveBounded

theorem objective_tangent (p : P) :
    objective seed + objectiveDerivative seed (p-seed) = 0 := by
  norm_num [objective,objectiveDerivative,seed,pt]

theorem row_tangent (j : Fin 1) (p : P) :
    row j seed + rowDerivative j seed (p-seed) = 1-p.1 0/4-p.2 0 := by
  norm_num [row,rowDerivative,seed,pt,ContinuousLinearMap.sub_apply,
    ContinuousLinearMap.smul_apply,map_sub]
  ring

theorem row_not_affine (j : Fin 1) : ¬OAKKT.AffineRow (row j) := by
  intro ha
  have h := OAKKT.affine_tangent ha (row_derivative j seed seed_minimum.1.1) (pt 1 1)
  rw [row_tangent] at h
  norm_num [row,pt] at h

theorem nonlinear_all : data.nonlinear = Set.univ := by
  ext j
  simp [FPUnbounded.Data.nonlinear,data,row_not_affine]

theorem seed_not_integral : ¬∃ y : IntVector 1, seed.2 = intCast y := by
  rintro ⟨y,hy⟩
  have he : (1/2:ℝ) = (y 0 : ℝ) := congrFun hy 0
  have h0 : (0:ℤ) < y 0 := by exact_mod_cast (show (0:ℝ) < (y 0:ℝ) by linarith)
  have h1 : y 0 < (1:ℤ) := by exact_mod_cast (show (y 0:ℝ) < (1:ℝ) by linarith)
  omega

theorem initial_master_iff (z : P × ℝ) : z ∈ FPUnbounded.master data start ↔
    z.1 ∈ base ∧ (∃ y : IntVector 1, z.1.2 = intCast y) ∧
      1-z.1.1 0/4-z.1.2 0 ≤ 0 ∧ 0 ≤ z.2 := by
  have hg : row 0 seed + (rowDerivative 0 seed z.1 - rowDerivative 0 seed seed) =
      1-z.1.1 0/4-z.1.2 0 := by simpa only [map_sub] using row_tangent 0 z.1
  have hf : objective seed + (objectiveDerivative seed z.1 - objectiveDerivative seed seed) = 0 := by
    simpa only [map_sub] using objective_tangent z.1
  simp [FPUnbounded.master,FPUnbounded.epigraph,FPUnbounded.family,
    FPUnbounded.anchors,start,initialState,retainedNormals,
    FPUnbounded.Data.level,Allows,data,Fin.forall_fin_one,hg,hf]

theorem initial_master_binary {z : P × ℝ} (hz : z ∈ FPUnbounded.master data start) :
    z.1.2 0 = 0 ∨ z.1.2 0 = 1 := by
  rcases (initial_master_iff z).mp hz with ⟨hb,⟨y,hy⟩,_,_⟩
  have he : z.1.2 0 = (y 0 : ℝ) := congrFun hy 0
  have h0 : (0:ℤ) ≤ y 0 := by exact_mod_cast (show (0:ℝ) ≤ (y 0:ℝ) by linarith [hb.2.1])
  have h1 : y 0 ≤ (1:ℤ) := by exact_mod_cast (show (y 0:ℝ) ≤ (1:ℝ) by linarith [hb.2.2])
  have hi : y 0 = 0 ∨ y 0 = 1 := by omega
  rcases hi with hi | hi
  · exact Or.inl (by simpa [hi] using he)
  · exact Or.inr (by simpa [hi] using he)

theorem initial_master_cost {z : P × ℝ} (hz : z ∈ FPUnbounded.master data start) :
    FPUnbounded.masterCost start z = 1/2 := by
  rcases initial_master_binary hz with h | h <;>
    norm_num [FPUnbounded.masterCost,start,State.reference,initialState,l1,
      seed,pt,Fin.sum_univ_one,h]

def target0Witness : P × ℝ := (pt 4 0,0)
def target1Witness : P × ℝ := (pt 1 1,0)

theorem target0_master : target0Witness ∈ FPUnbounded.master data start := by
  rw [initial_master_iff]
  refine ⟨?_,⟨iv 0,by funext j; norm_num [target0Witness,pt,intCast,iv]⟩,?_,?_⟩ <;> norm_num [target0Witness,base,pt]

theorem target1_master : target1Witness ∈ FPUnbounded.master data start := by
  rw [initial_master_iff]
  refine ⟨?_,⟨iv 1,by funext j; norm_num [target1Witness,pt,intCast,iv]⟩,?_,?_⟩ <;> norm_num [target1Witness,base,pt]

theorem target0_minimum :
    IsMinimizer (FPUnbounded.master data start) (FPUnbounded.masterCost start) target0Witness := by
  refine ⟨target0_master,fun z hz => ?_⟩
  rw [initial_master_cost target0_master,initial_master_cost hz]

theorem target1_minimum :
    IsMinimizer (FPUnbounded.master data start) (FPUnbounded.masterCost start) target1Witness := by
  refine ⟨target1_master,fun z hz => ?_⟩
  rw [initial_master_cost target1_master,initial_master_cost hz]

def exactInitialization : FPUnbounded.Initialization data :=
  .minimum seed seed_minimum

def exactBadMasterChoice : FPUnbounded.MasterChoice data start :=
  .minimum target0Witness target0_minimum

theorem initial_region_identity : data.region (data.level start.incumbent) = data.relaxation := by
  ext p
  simp [FPUnbounded.Data.region,FPUnbounded.Data.level,start,initialState,Allows]

theorem initial_region_nonempty : (data.region (data.level start.incumbent)).Nonempty := by
  rw [initial_region_identity]
  exact ⟨seed,seed_minimum.1⟩

theorem zero_target_distance (p : P) : distance (iv 0) p = (p.2 0)^2 := by
  simp [distance,intY,intCast,iv,Chapter03.yMap,PiLp.norm_sq_eq_of_L2,
    Fin.sum_univ_one,Real.norm_eq_abs,sq_abs]

/-- Every candidate is strictly improved by doubling x and halving y. -/
theorem strict_projection_improvement (p : P) (hp : p ∈ data.relaxation) :
    ∃ q ∈ data.relaxation, distance (iv 0) q < distance (iv 0) p := by
  have h := (relaxation_iff p).mp hp
  have hy := relaxation_y_positive hp
  refine ⟨pt (2*p.1 0) (p.2 0/2),?_,?_⟩
  · rw [relaxation_iff]
    refine ⟨⟨by dsimp [pt]; linarith [h.1.1],by dsimp [pt]; linarith [h.1.2.1],
      by dsimp [pt]; linarith [h.1.2.2]⟩,?_⟩
    change (2*p.1 0)⁻¹ ≤ p.2 0/2
    calc
      _ = (p.1 0)⁻¹ / 2 := by rw [mul_inv_rev]; ring
      _ ≤ p.2 0 / 2 := div_le_div_of_nonneg_right h.2 (by norm_num)
  · rw [zero_target_distance,zero_target_distance]
    change (p.2 0/2)^2 < (p.2 0)^2
    nlinarith [sq_pos_of_pos hy]

theorem projection_not_attained :
    ¬∃ p, IsMinimizer (data.region (data.level start.incumbent)) (distance (iv 0)) p := by
  rw [initial_region_identity]
  rintro ⟨p,hp,hm⟩
  obtain ⟨q,hq,hlt⟩ := strict_projection_improvement p hp
  exact (not_lt_of_ge (hm q hq)) hlt

/-- The requested exact projection choice is genuinely unavailable, even
though its feasible region is nonempty. Empty-projection completion cannot help. -/
theorem no_projection_choice : ¬Nonempty (FPUnbounded.ProjectionChoice data start (iv 0)) := by
  rintro ⟨choice⟩
  cases choice with
  | empty he => exact he initial_region_nonempty
  | minimum p hp => exact projection_not_attained ⟨p,hp⟩

theorem no_completed_reply (e : Event 1 1) :
    ¬FPUnbounded.EventReply data start target0Witness e := by
  intro h
  have he : e.target = iv 0 := FP.intCast_injective (by
    calc
      intCast e.target = target0Witness.1.2 := h.target_eq.symm
      _ = intCast (iv 0) := by funext j; norm_num [target0Witness,pt,intCast,iv])
  exact projection_not_attained ⟨e.projection,by simpa [he] using h.projection_min⟩

theorem delta_positive : 0 < data.delta := by norm_num [data]

/-- Explicit conjunction identifying the weaker-source obstruction. The
positive main theorem is not contradicted: its bounded feasible set fails. -/
theorem objective_bounded_projection_obstruction :
    0 < data.delta ∧ IsClosed base ∧ Convex ℝ base ∧ ConvexOn ℝ base data.f ∧
    (∀ j, ConvexOn ℝ base (data.g j)) ∧
    ContDiffOn ℝ 1 data.f base ∧ (∀ j, ContDiffOn ℝ 1 (data.g j) base) ∧
    (∀ p ∈ data.relaxation, 0 ≤ data.f p ∧ data.f p ≤ 1/4) ∧
    IsMinimizer data.relaxation data.f seed ∧
    IsMinimizer data.original data.f integerOptimum ∧
    (¬∃ y : IntVector 1, seed.2 = intCast y) ∧
    IsMinimizer (FPUnbounded.master data start) (FPUnbounded.masterCost start) target0Witness ∧
    (data.region (data.level start.incumbent)).Nonempty ∧
    (¬∃ p, IsMinimizer (data.region (data.level start.incumbent)) (distance (iv 0)) p) ∧
    ¬Bornology.IsBounded data.relaxation :=
  ⟨delta_positive,base_closed,base_convex,objective_convex,row_convex,objective_C1,row_C1,
    fun _ hp => objective_bounded hp,seed_minimum,original_minimum,seed_not_integral,
    target0_minimum,initial_region_nonempty,projection_not_attained,relaxation_unbounded⟩

end Chapter03.FPUnboundedObjectiveBounded
