module

public import Chapter03PumpOAC2Source

@[expose] public section

/-! Scalar binary square with no continuous coordinate and no constraint rows.
The two integer fibers have equal value 1/4; the fractional seed has value 0.
This supporting control will remove both successful fibers and retain a tie. -/
noncomputable section
open scoped BigOperators RealInnerProductSpace
open Chapter02 Chapter03.OAKKT
namespace Chapter03.PumpOA.Symmetric

abbrev P := Point 0 1
def pt (y : ℝ) : P := (fun _ => 0,fun _ => y)
def iv (y : ℤ) : IntVector 1 := fun _ => y
def yc : P →L[ℝ] ℝ :=
  (ContinuousLinearMap.proj (0 : Fin 1)).comp
    (ContinuousLinearMap.snd ℝ (RealVector 0) (RealVector 1))
@[simp] theorem yc_apply (p : P) : yc p = p.2 0 := rfl

def model : ModelData 0 1 0 0 where
  g j := Fin.elim0 j
  A j := Fin.elim0 j
  B j := Fin.elim0 j
  rhs j := Fin.elim0 j
  c1 := fun _ => 0
  c2 := fun _ => 0
  lo := fun _ => 0
  hi := fun _ => 1

def spec : OAExec.Data 0 1 0 0 where
  model := model
  f p := (p.2 0-1/2)^2
  Df p := (2*(p.2 0-1/2)) • yc
  Dg _ j := Fin.elim0 j
  domain := {p | 0≤p.2 0 ∧ p.2 0≤1}

def pump : FP.Data 0 1 0 0 := asFPDelta spec 0
def seed : P := pt (1/2)

theorem point_ext {p q : P} (h : p.2 0=q.2 0) : p=q := by
  apply Prod.ext
  · exact Subsingleton.elim _ _
  · funext j
    fin_cases j
    exact h

theorem relaxation (p : P) : p∈spec.relaxation ↔ 0≤p.2 0 ∧ p.2 0≤1 := by
  simp [OAExec.relaxation_mem_iff,spec,model,ModelData.linearRegion,Fin.forall_fin_one]

theorem domain_base : spec.domain=(OAExec.asFP spec).base := by
  ext p
  simp [spec,OAExec.asFP,FP.Data.base,model,ModelData.linearRegion,Fin.forall_fin_one]

theorem analytic : OAExec.Analytic spec where
  convex_f := FPTrace.square_convex
    (by rw [domain_base]; exact FP.base_convex _) yc (1/2)
  convex_g j := Fin.elim0 j
  original_domain := fun p hp => (relaxation p).mp (OAExec.original_subset_relaxation spec hp)
  derivative_f p _ := FPTrace.square_derivative yc (1/2) p
  derivative_g _ _ j := Fin.elim0 j

theorem bounded_relaxation : Bornology.IsBounded spec.relaxation := by
  apply (isCompact_Icc : IsCompact (Set.Icc (pt 0) (pt 1))).isBounded.subset
  intro p hp
  have h := (relaxation p).mp hp
  refine ⟨⟨?_,?_⟩,⟨?_,?_⟩⟩
  · intro j; exact Fin.elim0 j
  · intro j; fin_cases j; exact h.1
  · intro j; exact Fin.elim0 j
  · intro j; fin_cases j; exact h.2

def bounds : Bounds 0 where
  lower j := Fin.elim0 j
  upper j := Fin.elim0 j
def encoding : HardBoundEncoding bounds spec.model where
  valid j := Fin.elim0 j
  side j := Fin.elim0 j
  injective := by intro i; exact Fin.elim0 i
  lower_cover j := Fin.elim0 j
  upper_cover j := Fin.elim0 j
  row_spec j := Fin.elim0 j

theorem source_package : OAExec.AvailabilityAssumptions spec :=
  OAExec.article_availability_assumptions bounds spec encoding analytic
    (domain_base.trans (OAExec.articleDomain_eq_base bounds spec encoding).symm)
    bounded_relaxation (fun _ _ _ _ => linearIndependent_empty_type)

theorem pump_analytic : FP.Analytic pump := asFPDelta_analytic source_package (le_refl 0)

theorem seed_minimum : IsMinimizer spec.relaxation spec.f seed := by
  refine ⟨(relaxation _).mpr (by norm_num [seed,pt]),?_⟩
  intro p _
  change ((1/2:ℝ)-1/2)^2≤(p.2 0-1/2)^2
  norm_num only [sub_self,zero_pow]
  exact sq_nonneg _

theorem seed_not_integral : ¬ integral seed := by
  rintro ⟨y,hy⟩
  have he := congrFun hy (0 : Fin 1)
  norm_num [seed,pt,intCast] at he
  have hlo : (0 : ℤ) < y 0 := by exact_mod_cast (show (0 : ℝ) < (y 0 : ℝ) by linarith)
  have hhi : y 0 < (1 : ℤ) := by exact_mod_cast (show (y 0 : ℝ) < 1 by linarith)
  omega

theorem seed_valid : OAExec.SeedValid spec seed :=
  ⟨seed_minimum,(relaxation _).mp seed_minimum.1,seed_not_integral⟩

theorem binary {y : IntVector 1} (hy : y∈IntegerBox model.lo model.hi) :
    y=iv 0 ∨ y=iv 1 := by
  have h := hy 0
  change 0≤(y 0:ℝ) ∧ (y 0:ℝ)≤1 at h
  have h0 : (0:ℤ)≤y 0 := by exact_mod_cast h.1
  have h1 : y 0≤(1:ℤ) := by exact_mod_cast h.2
  have he : y 0=0 ∨ y 0=1 := by omega
  rcases he with he|he
  · left; funext j; fin_cases j; exact he
  · right; funext j; fin_cases j; exact he

theorem iv_mem (k : ℤ) (hk : k=0 ∨ k=1) : iv k∈IntegerBox model.lo model.hi := by
  rcases hk with rfl|rfl <;> intro j <;> norm_num [model,iv]

theorem box_card : pump.box.card=2 := by
  have he : pump.box={iv 0,iv 1} := by
    ext y
    simp only [FP.Data.box,Set.Finite.mem_toFinset,Finset.mem_insert,Finset.mem_singleton]
    exact ⟨binary,fun h => by rcases h with rfl|rfl; exact iv_mem 0 (Or.inl rfl); exact iv_mem 1 (Or.inr rfl)⟩
  rw [he]
  have hn : iv 0≠iv 1 := by intro h; have := congrFun h 0; norm_num [iv] at this
  simp [hn]

theorem distance (y : IntVector 1) (p : P) : FP.distance y p=((y 0:ℝ)-p.2 0)^2 := by
  rw [FP.distance,EuclideanSpace.real_norm_sq_eq]
  simp [Chapter03.yMap,FP.intY,FP.intCast,Fin.sum_univ_one]

theorem point_cast (k : ℤ) : (pt (k:ℝ)).2=FP.intCast (iv k) := rfl

theorem tangent_seed (p : P) : pump.f seed+pump.Df seed (p-seed)=0 := by
  norm_num [pump,asFPDelta,OAExec.asFP,spec,seed,pt]

theorem tangent_zero (p : P) : pump.f (pt 0)+pump.Df (pt 0) (p-pt 0)=1/4-p.2 0 := by
  norm_num [pump,asFPDelta,OAExec.asFP,spec,pt]
  ring

theorem tangent_one (p : P) : pump.f (pt 1)+pump.Df (pt 1) (p-pt 1)=p.2 0-3/4 := by
  norm_num [pump,asFPDelta,OAExec.asFP,spec,pt]
  ring

end Chapter03.PumpOA.Symmetric

#print axioms Chapter03.PumpOA.Symmetric.source_package
#print axioms Chapter03.PumpOA.Symmetric.seed_valid
#print axioms Chapter03.PumpOA.Symmetric.box_card
