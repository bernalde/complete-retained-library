module

public import Chapter02DICOPTKKT
public import Chapter02DICOPTQuasiconvex
public import Mathlib.LinearAlgebra.LinearIndependent.Basic

@[expose] public section

noncomputable section
open Set Filter
open scoped BigOperators Topology
namespace Chapter02.DICOPTQuarticAdapter
open DICOPT

def v (a : ℝ) : RealVector 1 := fun _ => a

def model : Data 1 1 1 0 0 where
  f := fun x => DICOPTQuasiconvex.f (x 0)
  h := fun _ x => DICOPTQuasiconvex.h (x 0)
  g := fun i => Fin.elim0 i
  A := fun _ => v 1
  B := fun i => Fin.elim0 i
  C := fun i => Fin.elim0 i
  D := fun i => Fin.elim0 i
  rhs := 0
  xL := v (-1)
  xU := v 0
  c := v (-1)

def coord : RealVector 1 →L[ℝ] ℝ := ContinuousLinearMap.proj 0

def jet (x : RealVector 1) : Jet model x where
  Df := ((6/5)*(x 0)^3-4/5) • coord
  Dh := fun _ => ((3*(x 0)^2+1)/2) • coord
  Dg := fun i => Fin.elim0 i
  fderiv := by
    simpa [model,coord,Function.comp_def] using (DICOPTQuasiconvex.f_deriv (x 0)).comp_hasFDerivAt x coord.hasFDerivAt
  hderiv := by
    intro i
    simpa [model,coord,Function.comp_def] using (DICOPTQuasiconvex.h_deriv (x 0)).comp_hasFDerivAt x coord.hasFDerivAt
  gderiv := fun i => Fin.elim0 i

@[simp] theorem v_apply (a : ℝ) (i : Fin 1) : v a i = a := rfl
@[simp] theorem v_coord (x : RealVector 1) : v (x 0) = x := by
  funext i
  have hi : i=0 := Fin.eq_zero i
  simp [hi,v]

def decode (z : RealVector 1 × RealVector 1) : ℝ × ℝ := (z.1 0,z.2 0)
def encode (z : ℝ × ℝ) : RealVector 1 × RealVector 1 := (v z.1,v z.2)

@[simp] theorem decode_encode (z : ℝ × ℝ) : decode (encode z)=z := rfl
@[simp] theorem encode_decode (z : RealVector 1 × RealVector 1) : encode (decode z)=z := by
  simp [encode,decode]

theorem feasible_iff (x y : RealVector 1) : model.Feasible x y ↔
    x 0 ∈ Icc (-1 : ℝ) 0 ∧ y 0+DICOPTQuasiconvex.h (x 0)=0 := by
  simp [Data.Feasible,Data.Hard,Data.xBox,Data.eqRow,Data.ineqRow,Data.affineRow,
    model,dot,v,Set.mem_Icc,Pi.le_def,Fin.forall_fin_one]

theorem original_iff (z : RealVector 1 × RealVector 1) :
    z ∈ model.original ↔ decode z ∈ DICOPTQuasiconvex.original := by
  simp only [Data.original,Set.mem_setOf_eq,feasible_iff]
  simp [Binary,Fin.forall_fin_one,DICOPTQuasiconvex.original,decode,and_assoc,and_left_comm,and_comm]

theorem relaxed_iff (z : RealVector 1 × RealVector 1) :
    z ∈ model.relaxed ↔ decode z ∈ DICOPTQuasiconvex.relaxed := by
  simp only [Data.relaxed,Set.mem_setOf_eq,feasible_iff]
  simp [Data.yBox,Set.mem_Icc,Pi.le_def,Fin.forall_fin_one,DICOPTQuasiconvex.relaxed,decode,and_assoc,and_left_comm,and_comm]

@[simp] theorem objective_decode (z : RealVector 1 × RealVector 1) :
    model.objective z.1 z.2 = DICOPTQuasiconvex.objective (decode z) := by
  simp [Data.objective,model,dot,v,DICOPTQuasiconvex.objective,decode]

@[simp] theorem objective_coords (x y : RealVector 1) :
    model.objective x y = DICOPTQuasiconvex.objective (x 0,y 0) := by
  simp [Data.objective,model,dot,v,DICOPTQuasiconvex.objective]

def fixed (a b lam : ℝ) (hf : model.Feasible (v a) (v b))
    (hs : ((6/5)*a^3-4/5)+lam*((3*a^2+1)/2)=0) : FixedKKT model (v a) (v b) where
  jet := jet (v a)
  alpha := DICOPTQuasiconvex.f a
  sigma := 1
  lambda := v lam
  mu := 0
  nu := 0
  xLower := 0
  xUpper := 0
  feasible := hf
  alphaFeasible := le_rfl
  sigmaNonneg := by norm_num
  muNonneg := fun _ => le_rfl
  nuNonneg := fun _ => le_rfl
  lowerNonneg := fun _ => le_rfl
  upperNonneg := fun _ => le_rfl
  alphaComp := by simp [model,v]
  ineqComp := by intro i; exact Fin.elim0 i
  affineComp := by intro i; exact Fin.elim0 i
  lowerComp := by simp
  upperComp := by simp
  alphaStationarity := by norm_num
  stationarity := by
    intro w
    simp [jet,coord,v,ContinuousLinearMap.smul_apply,smul_eq_mul]
    nlinarith [mul_eq_zero.mpr (Or.inl hs : ((6/5)*a^3-4/5)+lam*((3*a^2+1)/2)=0 ∨ w 0=0)]

def initialFixed : FixedKKT model (v (-1)) (v 1) :=
  fixed (-1) 1 1 (by rw [feasible_iff]; norm_num [v,DICOPTQuasiconvex.h]) (by norm_num)

def otherFixed : FixedKKT model (v 0) (v 0) :=
  fixed 0 0 (8/5) (by rw [feasible_iff]; norm_num [v,DICOPTQuasiconvex.h]) (by norm_num)

def initialJoint : JointKKT model (v (-1)) (v 1) where
  toFixedKKT := initialFixed
  yFeasible := by simp [Data.yBox,Set.mem_Icc,Pi.le_def,v]
  yLower := 0
  yUpper := 0
  yLowerNonneg := fun _ => le_rfl
  yUpperNonneg := fun _ => le_rfl
  yLowerComp := by simp
  yUpperComp := by simp
  yStationarity := by
    intro w
    simp [initialFixed,fixed,model,dot,v]


theorem source_f_convex : ConvexOn ℝ univ model.f := by
  simpa [model,coord,Function.comp_def] using
    DICOPTQuasiconvex.f_convex.comp_linearMap coord.toLinearMap

theorem source_h_quasiconvex : QuasiconvexOn ℝ univ (model.h 0) := by
  intro a
  simpa [model,coord,Function.comp_def] using (DICOPTQuasiconvex.h_quasiconvex a).linear_preimage coord.toLinearMap

theorem initial_signed_not_convex : ¬ SignedConvex model initialFixed := by
  intro hc
  apply DICOPTQuasiconvex.h_not_convex
  refine ⟨convex_Icc _ _,?_⟩
  intro a ha b hb s t hs ht hst
  have hxa : v a ∈ model.xBox := by simpa [Data.xBox,model,Set.mem_Icc,Pi.le_def,v] using ha
  have hxb : v b ∈ model.xBox := by simpa [Data.xBox,model,Set.mem_Icc,Pi.le_def,v] using hb
  have hh := (hc.equalities 0).2 hxa hxb hs ht hst
  simpa [initialFixed,fixed,model,v,signReal,smul_eq_mul] using hh

theorem source_original_points (z : RealVector 1 × RealVector 1) :
    z ∈ model.original ↔ z=(v (-1),v 1) ∨ z=(v 0,v 0) := by
  rw [original_iff,DICOPTQuasiconvex.original_points]
  constructor
  · rintro (h|h)
    · left
      simpa [encode,h] using (encode_decode z).symm
    · right
      simpa [encode,h] using (encode_decode z).symm
  · rintro (rfl|rfl) <;> simp [decode,v]

theorem source_original_minimum :
    IsMinimizer model.original (fun z => model.objective z.1 z.2) (v 0,v 0) := by
  refine ⟨(source_original_points _).mpr (Or.inr rfl),?_⟩
  intro z hz
  have hm := DICOPTQuasiconvex.original_minimum.2 (decode z) ((original_iff z).mp hz)
  simpa only [objective_coords,decode,v] using hm

def sourceLocalNeighborhood : Set (RealVector 1 × RealVector 1) := {z | z.1 0 < -(3/4)}

theorem source_strict_local : IsOpen sourceLocalNeighborhood ∧
    (v (-1),v 1) ∈ sourceLocalNeighborhood ∧
    ∀ z ∈ sourceLocalNeighborhood ∩ model.relaxed, z ≠ (v (-1),v 1) →
      model.objective (v (-1)) (v 1) < model.objective z.1 z.2 := by
  refine ⟨isOpen_lt ((continuous_apply 0).comp continuous_fst) continuous_const,by norm_num [sourceLocalNeighborhood,v],?_⟩
  intro z hz hne
  have hn : decode z ≠ (-1,1) := by
    intro he
    apply hne
    simpa [encode,he] using (encode_decode z).symm
  have hh := DICOPTQuasiconvex.local_strict_on_open_set.2.2 (decode z)
    ⟨hz.1,(relaxed_iff z).mp hz.2⟩ hn
  simpa only [objective_coords,decode,v] using hh

theorem source_local_minimum :
    IsLocalMinOn (fun z => model.objective z.1 z.2) model.relaxed (v (-1),v 1) := by
  have hd : Continuous decode := by unfold decode; fun_prop
  have hf : (v (-1),v 1) ∈ model.relaxed :=
    (relaxed_iff _).mpr DICOPTQuasiconvex.relaxed_anchor_feasible
  have hh := DICOPTQuasiconvex.local_minimum.comp_continuousOn
    (s := model.relaxed) (g := decode) (b := (v (-1),v 1))
    (fun z hz => (relaxed_iff z).mp hz) hd.continuousOn hf
  simpa only [Function.comp_def,← objective_decode] using hh

theorem source_not_relaxed_global :
    ¬ IsMinimizer model.relaxed (fun z => model.objective z.1 z.2) (v (-1),v 1) := by
  intro hm
  have hz : (v 0,v 0) ∈ model.relaxed := by rw [relaxed_iff]; norm_num [decode,v,DICOPTQuasiconvex.relaxed,DICOPTQuasiconvex.h]
  have hh := hm.2 (v 0,v 0) hz
  norm_num [objective_coords,decode,v,DICOPTQuasiconvex.objective,DICOPTQuasiconvex.f] at hh

theorem tangent_objective (x : RealVector 1) : objTangent model initialFixed.jet x=1-2*x 0 := by
  norm_num [objTangent,initialFixed,fixed,jet,model,v,coord,DICOPTQuasiconvex.f]
  ring

theorem tangent_equality (x y : RealVector 1) (i : Fin 1) :
    eqTangent model initialFixed.jet initialFixed.lambda i x y = y 0+2*x 0+1 := by
  norm_num [eqTangent,initialFixed,fixed,jet,model,v,coord,dot,DICOPTQuasiconvex.h,signReal]
  ring

def sourceHardMaster : Set (RealVector 1 × RealVector 1 × ℝ) := {z |
  model.Hard z.1 z.2.1 ∧ Binary z.2.1 ∧ objTangent model initialFixed.jet z.1 ≤ z.2.2 ∧
  (∀ i,eqTangent model initialFixed.jet initialFixed.lambda i z.1 z.2.1 ≤ 0) ∧
  ∀ i,ineqTangent model initialFixed.jet i z.1 z.2.1 ≤ 0}

def sourceHardObjective (z : RealVector 1 × RealVector 1 × ℝ) : ℝ := dot model.c z.2.1+z.2.2

def decodeHard (z : RealVector 1 × RealVector 1 × ℝ) : ℝ × ℝ × ℝ := (z.1 0,z.2.1 0,z.2.2)

theorem hard_iff (z : RealVector 1 × RealVector 1 × ℝ) :
    z ∈ sourceHardMaster ↔ decodeHard z ∈ DICOPTQuasiconvex.hardMaster := by
  simp only [sourceHardMaster,Set.mem_setOf_eq,tangent_objective,tangent_equality]
  simp [Data.Hard,Data.xBox,model,Set.mem_Icc,Pi.le_def,v,Binary,
    Fin.forall_fin_one,tangent_objective,tangent_equality,decodeHard,DICOPTQuasiconvex.hardMaster]

@[simp] theorem hard_objective_decode (z : RealVector 1 × RealVector 1 × ℝ) :
    sourceHardObjective z = DICOPTQuasiconvex.hardObjective (decodeHard z) := by
  simp [sourceHardObjective,model,dot,v,DICOPTQuasiconvex.hardObjective,decodeHard]

theorem source_hard_minimum :
    IsMinimizer sourceHardMaster sourceHardObjective (v (-1),v 1,3) := by
  refine ⟨(hard_iff _).mpr DICOPTQuasiconvex.hard_minimum.1,?_⟩
  intro z hz
  simpa only [hard_objective_decode,decodeHard,v] using
    DICOPTQuasiconvex.hard_minimum.2 (decodeHard z) ((hard_iff z).mp hz)

theorem source_second_hard_minimum :
    IsMinimizer sourceHardMaster sourceHardObjective (v (-(1/2)),v 0,2) := by
  refine ⟨(hard_iff _).mpr DICOPTQuasiconvex.second_hard_minimum.1,?_⟩
  intro z hz
  simpa only [hard_objective_decode,decodeHard,v] using
    DICOPTQuasiconvex.second_hard_minimum.2 (decodeHard z) ((hard_iff z).mp hz)

theorem source_gap : sourceHardObjective (v (-1),v 1,3)-model.objective (v 0) (v 0)=1/10 := by
  norm_num [sourceHardObjective,Data.objective,model,dot,v,DICOPTQuasiconvex.f]

/-- The actual derivative-linearized equality and active original box rows. -/
def sourceLinearizedCone (a : RealVector 1) : Set (RealVector 1) := {w |
  (∀ i,(jet a).Dh i w=0) ∧
  (∀ i,a i=model.xL i → 0 ≤ w i) ∧
  ∀ i,a i=model.xU i → w i ≤ 0}

def negativePolar (S : Set (RealVector 1)) : Set (RealVector 1 →L[ℝ] ℝ) :=
  {L | ∀ w ∈ S,L w ≤ 0}

theorem source_fiber_singleton {a b : ℝ} (ha : a ∈ Icc (-1 : ℝ) 0)
    (he : b+DICOPTQuasiconvex.h a=0) : model.fiber (v b)={v a} := by
  ext x
  constructor
  · intro hx
    have hx' := (feasible_iff x (v b)).mp hx
    have heq : x 0=a := DICOPTQuasiconvex.h_strictMono.injective (by dsimp [v] at hx'; linarith [hx'.2])
    exact Set.mem_singleton_iff.mpr (by rw [← v_coord x,heq])
  · rintro rfl
    exact (feasible_iff _ _).mpr ⟨ha,he⟩

theorem source_linearized_singleton (a : RealVector 1) : sourceLinearizedCone a={0} := by
  ext w
  constructor
  · rintro ⟨hw,_,_⟩
    have hh := hw 0
    simp only [jet,coord,ContinuousLinearMap.smul_apply,smul_eq_mul,ContinuousLinearMap.proj_apply] at hh
    have h0 : w 0=0 := (mul_eq_zero.mp hh).resolve_left (ne_of_gt (DICOPTQuasiconvex.h_deriv_positive _))
    exact Set.mem_singleton_iff.mpr (by rw [← v_coord w,h0]; rfl)
  · rintro rfl
    simp [sourceLinearizedCone]

theorem source_abadie {a b : ℝ} (ha : a ∈ Icc (-1 : ℝ) 0)
    (he : b+DICOPTQuasiconvex.h a=0) :
    posTangentConeAt (model.fiber (v b)) (v a)=sourceLinearizedCone (v a) := by
  rw [source_fiber_singleton ha he,DICOPTControlGeometry.singleton_posTangentCone,
    source_linearized_singleton]

theorem source_guignard {a b : ℝ} (ha : a ∈ Icc (-1 : ℝ) 0)
    (he : b+DICOPTQuasiconvex.h a=0) :
    negativePolar (posTangentConeAt (model.fiber (v b)) (v a)) =
      negativePolar (sourceLinearizedCone (v a)) := by
  rw [source_abadie ha he]


theorem source_joint_not_quasiconvex :
    ¬ QuasiconvexOn ℝ (model.xBox ×ˢ model.yBox) (fun z => model.eqRow 0 z.1 z.2) := by
  intro hq
  have ha : (v (-1),v 1) ∈ {z ∈ model.xBox ×ˢ model.yBox | model.eqRow 0 z.1 z.2 ≤ 0} := by
    norm_num [Data.xBox,Data.yBox,Data.eqRow,model,dot,v,DICOPTQuasiconvex.h,Set.mem_Icc,Pi.le_def]
  have hb : (v 0,v 0) ∈ {z ∈ model.xBox ×ˢ model.yBox | model.eqRow 0 z.1 z.2 ≤ 0} := by
    norm_num [Data.xBox,Data.yBox,Data.eqRow,model,dot,v,DICOPTQuasiconvex.h,Set.mem_Icc,Pi.le_def]
  have hh := hq 0 ha hb (a := (1/2 : ℝ)) (b := (1/2 : ℝ)) (by norm_num) (by norm_num) (by norm_num)
  norm_num [Data.eqRow,model,dot,v,DICOPTQuasiconvex.h] at hh

abbrev JointSpace := RealVector 1 × RealVector 1 × ℝ

def jx : JointSpace →L[ℝ] ℝ := coord.comp (ContinuousLinearMap.fst ℝ _ _)
def jy : JointSpace →L[ℝ] ℝ := coord.comp ((ContinuousLinearMap.fst ℝ _ _).comp (ContinuousLinearMap.snd ℝ _ _))
def ja : JointSpace →L[ℝ] ℝ := (ContinuousLinearMap.snd ℝ _ _).comp (ContinuousLinearMap.snd ℝ _ _)
def jointAnchor : JointSpace := (v (-1),v 1,3)
def jointEqD : JointSpace →L[ℝ] ℝ := (2 : ℝ) • jx+jy
def jointObjD : JointSpace →L[ℝ] ℝ := -((2 : ℝ) • jx)-ja

theorem joint_equality_deriv :
    HasFDerivAt (fun z : JointSpace => model.eqRow 0 z.1 z.2.1) jointEqD jointAnchor := by
  have hh := jy.hasFDerivAt.fun_add ((DICOPTQuasiconvex.h_deriv (-1)).comp_hasFDerivAt jointAnchor jx.hasFDerivAt)
  norm_num at hh
  simpa [Data.eqRow,model,dot,jx,jy,coord,v,jointEqD,add_comm,Function.comp_def] using hh

theorem joint_objective_row_deriv :
    HasFDerivAt (fun z : JointSpace => model.f z.1-z.2.2) jointObjD jointAnchor := by
  have hh := ((DICOPTQuasiconvex.f_deriv (-1)).comp_hasFDerivAt jointAnchor jx.hasFDerivAt).fun_sub ja.hasFDerivAt
  norm_num at hh
  simpa [model,jx,ja,coord,jointObjD,neg_smul,Function.comp_def] using hh

theorem joint_equality_surjective : Function.Surjective jointEqD := by
  intro t
  refine ⟨(v 0,v t,0),?_⟩
  simp [jointEqD,jx,jy,coord,v]

theorem joint_equality_independent : LinearIndependent ℝ (fun _ : Fin 1 => jointEqD) := by
  apply linearIndependent_unique_iff.mpr
  intro he
  obtain ⟨z,hz⟩ := joint_equality_surjective 1
  rw [he] at hz
  norm_num at hz

/-- Actual source epigraph MFCQ: derivatives, surjective equality row and strict
    direction for every active x/y bound and objective row. Other row families are empty. -/
structure JointEpigraphMFCQ : Prop where
  relaxedFeasible : (jointAnchor.1,jointAnchor.2.1) ∈ model.relaxed
  objectiveFeasible : model.f jointAnchor.1 ≤ jointAnchor.2.2
  equalityDerivative : HasFDerivAt (fun z : JointSpace => model.eqRow 0 z.1 z.2.1) jointEqD jointAnchor
  objectiveDerivative : HasFDerivAt (fun z : JointSpace => model.f z.1-z.2.2) jointObjD jointAnchor
  xLowerDerivative : ∀ i : Fin 1, HasFDerivAt (fun z : JointSpace => model.xL i-z.1 i) (-jx) jointAnchor
  xUpperDerivative : ∀ i : Fin 1, HasFDerivAt (fun z : JointSpace => z.1 i-model.xU i) jx jointAnchor
  yLowerDerivative : ∀ i : Fin 1, HasFDerivAt (fun z : JointSpace => 0-z.2.1 i) (-jy) jointAnchor
  yUpperDerivative : ∀ i : Fin 1, HasFDerivAt (fun z : JointSpace => z.2.1 i-1) jy jointAnchor
  equalitySurjective : Function.Surjective jointEqD
  equalityIndependent : LinearIndependent ℝ (fun _ : Fin 1 => jointEqD)
  strictDirection : ∃ w : JointSpace, jointEqD w=0 ∧
    (model.f jointAnchor.1=jointAnchor.2.2 → jointObjD w<0) ∧
    (∀ i,jointAnchor.1 i=model.xL i → -w.1 i<0) ∧
    (∀ i,jointAnchor.1 i=model.xU i → w.1 i<0) ∧
    (∀ i,jointAnchor.2.1 i=0 → -w.2.1 i<0) ∧
    ∀ i,jointAnchor.2.1 i=1 → w.2.1 i<0

theorem actual_joint_mfcq : JointEpigraphMFCQ where
  relaxedFeasible := (relaxed_iff _).mpr DICOPTQuasiconvex.relaxed_anchor_feasible
  objectiveFeasible := by norm_num [jointAnchor,model,v,DICOPTQuasiconvex.f]
  equalityDerivative := joint_equality_deriv
  objectiveDerivative := joint_objective_row_deriv
  xLowerDerivative := by
    intro i
    have hi := Fin.eq_zero i
    subst i
    simpa [jx,coord] using jx.hasFDerivAt.const_sub (model.xL 0)
  xUpperDerivative := by
    intro i
    have hi := Fin.eq_zero i
    subst i
    simpa [jx,coord] using jx.hasFDerivAt.sub_const (model.xU 0)
  yLowerDerivative := by
    intro i
    have hi := Fin.eq_zero i
    subst i
    simpa [jy,coord] using jy.hasFDerivAt.const_sub 0
  yUpperDerivative := by
    intro i
    have hi := Fin.eq_zero i
    subst i
    simpa [jy,coord] using jy.hasFDerivAt.sub_const 1
  equalitySurjective := joint_equality_surjective
  equalityIndependent := joint_equality_independent
  strictDirection := by
    refine ⟨(v 1,v (-2),0),?_⟩
    norm_num [jointEqD,jointObjD,jx,jy,ja,coord,jointAnchor,model,v,DICOPTQuasiconvex.f]

def initialWeights : Weights initialFixed where
  obj := 2
  eq := v 2
  ineq := 0
  obj_gt := by norm_num [initialFixed,fixed]
  eq_gt := by intro i; norm_num [initialFixed,fixed,v]
  ineq_gt := fun i => Fin.elim0 i

/-- All source/model/analytic obligations for the static quartic control. -/
structure QuarticSourceControl : Prop where
  derivatives : ∀ x, Nonempty (Jet model x)
  convexObjective : ConvexOn ℝ univ model.f
  quasiconvexEquality : QuasiconvexOn ℝ univ (model.h 0)
  initialFixedKKT : Nonempty (FixedKKT model (v (-1)) (v 1))
  otherFixedKKT : Nonempty (FixedKKT model (v 0) (v 0))
  jointKKT : Nonempty (JointKKT model (v (-1)) (v 1))
  integralInitializer : Binary (v 1)
  originalPoints : ∀ z,z ∈ model.original ↔ z=(v (-1),v 1) ∨ z=(v 0,v 0)
  originalMinimum : IsMinimizer model.original (fun z => model.objective z.1 z.2) (v 0,v 0)
  localMinimum : IsLocalMinOn (fun z => model.objective z.1 z.2) model.relaxed (v (-1),v 1)
  strictLocal : IsOpen sourceLocalNeighborhood ∧ (v (-1),v 1) ∈ sourceLocalNeighborhood ∧
    ∀ z ∈ sourceLocalNeighborhood ∩ model.relaxed,z≠(v (-1),v 1) →
      model.objective (v (-1)) (v 1)<model.objective z.1 z.2
  notRelaxedGlobal : ¬IsMinimizer model.relaxed (fun z => model.objective z.1 z.2) (v (-1),v 1)
  signedConvexityFails : ¬ SignedConvex model initialFixed
  jointQuasiconvexityFails : ¬QuasiconvexOn ℝ (model.xBox ×ˢ model.yBox) (fun z => model.eqRow 0 z.1 z.2)
  literalHardMaster : ∀ z,z ∈ sourceHardMaster ↔ decodeHard z ∈ DICOPTQuasiconvex.hardMaster
  hardMinimum : IsMinimizer sourceHardMaster sourceHardObjective (v (-1),v 1,3)
  secondHardMinimum : IsMinimizer sourceHardMaster sourceHardObjective (v (-(1/2)),v 0,2)
  objectiveValues : model.objective (v 0) (v 0)=19/10 ∧ sourceHardObjective (v (-1),v 1,3)=2
  hardGap : sourceHardObjective (v (-1),v 1,3)-model.objective (v 0) (v 0)=1/10
  firstAbadie : posTangentConeAt (model.fiber (v 1)) (v (-1))=sourceLinearizedCone (v (-1))
  secondAbadie : posTangentConeAt (model.fiber (v 0)) (v 0)=sourceLinearizedCone (v 0)
  firstGuignard : negativePolar (posTangentConeAt (model.fiber (v 1)) (v (-1)))=negativePolar (sourceLinearizedCone (v (-1)))
  secondGuignard : negativePolar (posTangentConeAt (model.fiber (v 0)) (v 0))=negativePolar (sourceLinearizedCone (v 0))
  initialMFCQ : JointEpigraphMFCQ
  proposition1StillHolds : Nonempty (HardKKT initialFixed (v (-1),initialFixed.alpha)) ∧
    IsMinimizer (hardFeasible initialFixed) (hardObjective initialFixed) (v (-1),initialFixed.alpha)
  proposition2StillHolds : Nonempty (APKKT initialFixed initialWeights (apAnchor initialFixed)) ∧
    IsMinimizer (apFeasible initialFixed) (apObjective initialFixed initialWeights) (apAnchor initialFixed)

/-- This is a static local-anchor lower-bound countercontrol. The integral initializer
    would stop before generating this master; no AP execution claim is made. -/
theorem quartic_source_control : QuarticSourceControl where
  derivatives := fun x => ⟨jet x⟩
  convexObjective := source_f_convex
  quasiconvexEquality := source_h_quasiconvex
  initialFixedKKT := ⟨initialFixed⟩
  otherFixedKKT := ⟨otherFixed⟩
  jointKKT := ⟨initialJoint⟩
  integralInitializer := by intro i; exact Or.inr rfl
  originalPoints := source_original_points
  originalMinimum := source_original_minimum
  localMinimum := source_local_minimum
  strictLocal := source_strict_local
  notRelaxedGlobal := source_not_relaxed_global
  signedConvexityFails := initial_signed_not_convex
  jointQuasiconvexityFails := source_joint_not_quasiconvex
  literalHardMaster := hard_iff
  hardMinimum := source_hard_minimum
  secondHardMinimum := source_second_hard_minimum
  objectiveValues := by norm_num [Data.objective,sourceHardObjective,model,dot,v,DICOPTQuasiconvex.f]
  hardGap := source_gap
  firstAbadie := source_abadie (by norm_num) (by norm_num [DICOPTQuasiconvex.h])
  secondAbadie := source_abadie (by norm_num) (by norm_num [DICOPTQuasiconvex.h])
  firstGuignard := source_guignard (by norm_num) (by norm_num [DICOPTQuasiconvex.h])
  secondGuignard := source_guignard (by norm_num) (by norm_num [DICOPTQuasiconvex.h])
  initialMFCQ := actual_joint_mfcq
  proposition1StillHolds := source_signed_hard_transfer initialFixed
  proposition2StillHolds := ⟨(source_separate_slack_transfer initialFixed initialWeights).1,
    (source_separate_slack_transfer initialFixed initialWeights).2.1⟩

end Chapter02.DICOPTQuarticAdapter
