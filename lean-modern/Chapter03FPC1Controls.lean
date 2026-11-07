module

public import Chapter03FPScalarControls

@[expose] public section

noncomputable section
open scoped BigOperators RealInnerProductSpace
open Chapter02 Chapter03.FP
namespace Chapter03.FPControls

def seed : P := pt 0 (1/2)
def s0 : State 1 1 := initialState seed
def e0 : Event 1 1 := ⟨iv 0,pt 0 0,none,some (pt 0 0,pt 0 0)⟩
def s1 : State 1 1 := append s0 e0
def e1 : Event 1 1 := ⟨iv 1,pt 0 1,some (1/4),some (pt 0 1,pt 0 0)⟩
def s2 : State 1 1 := append s1 e1

theorem master_rows {n m l r : ℕ} (d : Data n m l r) (s : State n m)
    (z : Point n m × ℝ) : z ∈ master d s ↔
    z.1 ∈ d.model.linearRegion ∧
    (∃ y ∈ IntegerBox d.model.lo d.model.hi, z.1.2 = intCast y) ∧
    (∀ a ∈ anchors d s, d.f a.point + d.Df a.point (z.1-a.point) ≤ z.2 ∧
      ∀ j ∈ a.selected, d.model.g j a.point + d.Dg j a.point (z.1-a.point) ≤ 0) ∧
    retainedNormals s z.1 ∧ noGoods s z.1 ∧ Allows (d.level s.incumbent) z.2 := by
  constructor
  · rintro ⟨⟨⟨⟨⟨_,hc⟩,hl⟩,hi⟩,hf⟩,hn,hng,ha⟩
    refine ⟨hl,hi,?_,hn,hng,ha⟩
    intro a ha
    obtain ⟨i,rfl⟩ := List.mem_iff_get.mp ha
    exact ⟨hf i,hc i⟩
  · rintro ⟨hl,hi,hrows,hn,hng,ha⟩
    refine ⟨⟨⟨⟨⟨Set.mem_univ _,?_⟩,hl⟩,hi⟩,?_⟩,hn,hng,ha⟩
    · intro i; exact (hrows _ (List.get_mem _ _)).2
    · intro i; exact (hrows _ (List.get_mem _ _)).1

theorem scalar_integer (bounded : Bool) (upper shift : ℝ) (p : P) :
    (∃ y ∈ IntegerBox (model bounded upper shift).lo (model bounded upper shift).hi,
      p.2 = intCast y) ↔ ∃ k : ℤ, 0 ≤ (k:ℝ) ∧ (k:ℝ) ≤ upper ∧ p.2 0 = k := by
  constructor
  · rintro ⟨y,hy,he⟩; exact ⟨y 0,(hy 0).1,(hy 0).2,congrFun he 0⟩
  · rintro ⟨k,hk,hu,he⟩
    refine ⟨iv k,(fun _ => ⟨hk,hu⟩),?_⟩
    funext j; fin_cases j; exact he

theorem scalar_neq (p : P) (k : ℤ) : p.2 ≠ intCast (iv k) ↔ p.2 0 ≠ k := by
  constructor
  · intro h he; apply h; funext j; fin_cases j; exact he
  · intro h he; exact h (congrFun he 0)

theorem master_s0 (bounded : Bool) (a b upper delta : ℝ) (z : P × ℝ) :
    z ∈ master (data bounded a b upper delta 0) s0 ↔
    (bounded = true → -1 ≤ z.1.1 0 ∧ z.1.1 0 ≤ 1) ∧
    (∃ k : ℤ, 0 ≤ (k:ℝ) ∧ (k:ℝ) ≤ upper ∧ z.1.2 0 = k) ∧ -a*z.1.1 0 ≤ z.2 := by
  rw [master_rows]
  change (z.1 ∈ (model bounded upper 0).linearRegion ∧
    (∃ y ∈ IntegerBox (model bounded upper 0).lo (model bounded upper 0).hi, _) ∧ _) ↔ _
  rw [linear_mem,scalar_integer]
  simp [anchors,s0,initialState,seed,data,model,Event.anchor,retainedNormals,noGoods,Data.level,
    Allows,xc,yc,pt,Fin.forall_fin_one]

theorem master_s1 (bounded : Bool) (a b upper delta : ℝ) (z : P × ℝ) :
    z ∈ master (data bounded a b upper delta 0) s1 ↔
    (bounded = true → -1 ≤ z.1.1 0 ∧ z.1.1 0 ≤ 1) ∧
    (∃ k : ℤ, 0 ≤ (k:ℝ) ∧ (k:ℝ) ≤ upper ∧ z.1.2 0 = k) ∧
    -a*z.1.1 0 ≤ z.2 ∧ -a*z.1.1 0 + b*(1/4-z.1.2 0) ≤ z.2 ∧
    z.1.2 0 ≠ 0 ∧ z.2 ≤ cutoffValue delta (b/4) := by
  rw [master_rows]
  change (z.1 ∈ (model bounded upper 0).linearRegion ∧
    (∃ y ∈ IntegerBox (model bounded upper 0).lo (model bounded upper 0).hi, _) ∧ _) ↔ _
  rw [linear_mem,scalar_integer]
  simp [anchors,s1,s0,append,initialState,seed,e0,data,model,Event.anchor,retainedNormals,
    noGoods,Data.level,Allows,xc,yc,pt,Fin.forall_fin_one,scalar_neq]
  ring_nf
  intro _ k _ _ _
  constructor
  · rintro ⟨⟨h0,h1⟩,hn,hc⟩; exact ⟨h0,by linarith,hn,hc⟩
  · rintro ⟨h0,h1,hn,hc⟩; exact ⟨⟨h0,by linarith⟩,hn,hc⟩

theorem master_s2 (bounded : Bool) (a b upper delta : ℝ) (z : P × ℝ) :
    z ∈ master (data bounded a b upper delta 0) s2 ↔
    (bounded = true → -1 ≤ z.1.1 0 ∧ z.1.1 0 ≤ 1) ∧
    (∃ k : ℤ, 0 ≤ (k:ℝ) ∧ (k:ℝ) ≤ upper ∧ z.1.2 0 = k) ∧
    -a*z.1.1 0 ≤ z.2 ∧ -a*z.1.1 0 + b*(1/4-z.1.2 0) ≤ z.2 ∧
    -a*z.1.1 0 + b*(z.1.2 0-3/4) ≤ z.2 ∧
    z.1.2 0 ≠ 0 ∧ z.1.2 0 ≠ 1 ∧ z.2 ≤ cutoffValue delta (b/4) := by
  rw [master_rows]
  change (z.1 ∈ (model bounded upper 0).linearRegion ∧
    (∃ y ∈ IntegerBox (model bounded upper 0).lo (model bounded upper 0).hi, _) ∧ _) ↔ _
  rw [linear_mem,scalar_integer]
  simp [anchors,s2,s1,s0,append,initialState,seed,e0,e1,data,model,Event.anchor,retainedNormals,
    noGoods,Data.level,Allows,xc,yc,pt,Fin.forall_fin_one,scalar_neq]
  ring_nf
  intro _ k _ _ _
  constructor
  · rintro ⟨⟨h0,h1,h2⟩,⟨hn0,hn1⟩,hc⟩; exact ⟨h0,by linarith,by linarith,hn0,hn1,hc⟩
  · rintro ⟨h0,h1,h2,hn0,hn1,hc⟩; exact ⟨⟨h0,by linarith,by linarith⟩,⟨hn0,hn1⟩,hc⟩

def c1 (delta : ℝ) : Data 1 1 1 2 := data true 1 1 1 delta 0
theorem c1_analytic (delta : ℝ) (hd : 0 ≤ delta) : Analytic (c1 delta) :=
  analytic true 1 1 1 delta (by norm_num) hd

theorem binary_value {k : ℤ} (h0 : 0 ≤ (k:ℝ)) (h1 : (k:ℝ) ≤ 1) : k=0 ∨ k=1 := by
  have h0' : 0 ≤ k := by exact_mod_cast h0
  have h1' : k ≤ 1 := by exact_mod_cast h1
  omega

theorem first_master (delta : ℝ) :
    IsMinimizer (master (c1 delta) s0) (masterCost s0) (pt 0 0,0) := by
  refine ⟨(master_s0 _ _ _ _ _ _).mpr ⟨by norm_num,⟨0,by norm_num,by norm_num,by norm_num [pt]⟩,by norm_num⟩,?_⟩
  intro z hz
  obtain ⟨_,⟨k,h0,h1,he⟩,_⟩ := (master_s0 true 1 1 1 delta z).mp hz
  rcases binary_value h0 h1 with rfl|rfl <;>
    norm_num [masterCost,l1_formula,State.reference,s0,initialState,seed,pt,he]

theorem seed_minimum (delta : ℝ) : IsMinimizer (c1 delta).relaxation (c1 delta).f seed :=
  relaxation_seed true 1 1 1 delta (by norm_num) (by norm_num)

theorem c1_projection0 (delta : ℝ) :
    IsMinimizer ((c1 delta).region none) (distance (iv 0)) (pt 0 0) := by
  refine ⟨⟨(relaxation_iff _ _ _ _ _ _).mpr ⟨rfl,by norm_num,by norm_num⟩,trivial⟩,?_⟩
  intro p hp
  simp only [distance_formula,iv_apply,pt_snd,Int.cast_zero,sub_self,zero_pow (by decide : 2 ≠ 0)]
  exact sq_nonneg _

theorem c1_reply0 (delta : ℝ) : EventReply (c1 delta) s0 (pt 0 0,0) e0 := by
  refine ⟨by funext j; norm_num [e0,pt,intCast,iv],rfl,c1_projection0 delta,?_⟩
  exact ⟨by norm_num [e0,distance_formula],
    by simpa [c1,e0] using fiber_minimum true 1 1 1 delta 0 (by norm_num) (by norm_num),rfl⟩

theorem c1_continue0 (delta : ℝ) : Continue (c1 delta) none s0 e0 :=
  ⟨(pt 0 0,0),first_master delta,by simp [BeforeCap],c1_reply0 delta⟩

theorem second_master_delta1 :
    IsMinimizer (master (c1 1) s1) (masterCost s1) (pt 1 1,-3/4) := by
  refine ⟨(master_s1 _ _ _ _ _ _).mpr ?_,?_⟩
  · refine ⟨by norm_num [pt],⟨1,by norm_num,by norm_num,by norm_num [pt]⟩,?_,?_,?_,?_⟩ <;>
      norm_num [pt,cutoffValue,max_def,abs_of_nonneg]
  · intro z hz
    obtain ⟨_,⟨k,h0,h1,he⟩,_,_,hn,_⟩ := (master_s1 true 1 1 1 1 z).mp hz
    rcases binary_value h0 h1 with rfl|rfl
    · exact False.elim (hn (by simpa using he))
    · simp [masterCost,l1_formula,State.reference,s1,s0,append,initialState,e0,Event.anchor,pt,he]

theorem c1_cutoff_empty : ¬ ((c1 1).region ((c1 1).level s1.incumbent)).Nonempty := by
  rintro ⟨p,hp,hc⟩
  obtain ⟨hx,_,_⟩ := (relaxation_iff true 1 1 1 1 p).mp hp
  have hh : (p.2 0-1/2)^2 ≤ -(3/4:ℝ) := by
    norm_num [c1,data,Data.level,cutoffValue,s1,s0,append,initialState,e0,pt,Allows,hx,
      max_def,abs_of_nonneg] at hc
    exact hc
  nlinarith [sq_nonneg (p.2 0-1/2)]

theorem stop_delta1 : Stop (c1 1) none s1 (.emptyProjection (iv 1)) :=
  .emptyProjection second_master_delta1 (by funext j; norm_num [pt,intCast,iv])
    (by simp [BeforeCap]) c1_cutoff_empty

theorem second_master_delta0 :
    IsMinimizer (master (c1 0) s1) (masterCost s1) (pt 0 1,1/4) := by
  refine ⟨(master_s1 _ _ _ _ _ _).mpr ?_,?_⟩
  · refine ⟨by norm_num [pt],⟨1,by norm_num,by norm_num,by norm_num [pt]⟩,?_,?_,?_,?_⟩ <;>
      norm_num [pt,cutoffValue]
  · intro z hz
    obtain ⟨_,⟨k,h0,h1,he⟩,_,_,hn,_⟩ := (master_s1 true 1 1 1 0 z).mp hz
    rcases binary_value h0 h1 with rfl|rfl
    · exact False.elim (hn (by simpa using he))
    · simp [masterCost,l1_formula,State.reference,s1,s0,append,initialState,e0,Event.anchor,pt,he]

theorem c1_projection1 :
    IsMinimizer ((c1 0).region ((c1 0).level s1.incumbent)) (distance (iv 1)) (pt 0 1) := by
  refine ⟨⟨(relaxation_iff _ _ _ _ _ _).mpr ⟨rfl,by norm_num,by norm_num⟩,?_⟩,?_⟩
  · norm_num [c1,data,Data.level,s1,s0,append,initialState,e0,pt,Allows,cutoffValue]
  · intro p hp
    norm_num only [distance_formula,iv_apply,pt_snd,Int.cast_one,sub_self,zero_pow]
    exact sq_nonneg _

theorem c1_reply1 : EventReply (c1 0) s1 (pt 0 1,1/4) e1 := by
  refine ⟨by funext j; norm_num [e1,pt,intCast,iv],?_,c1_projection1,?_⟩
  · norm_num [e1,c1,data,Data.level,s1,s0,append,initialState,e0,pt,cutoffValue]
  · refine ⟨by norm_num [e1,distance_formula],?_,?_⟩
    · simpa [c1,e1] using fiber_minimum true 1 1 1 0 1 (by norm_num) (by norm_num)
    · norm_num [e1,s1,s0,append,initialState,e0,BestChoice,c1,data,pt]

theorem c1_continue1 : Continue (c1 0) none s1 e1 :=
  ⟨(pt 0 1,1/4),second_master_delta0,by simp [BeforeCap],c1_reply1⟩

theorem c1_master2_empty (delta : ℝ) : ¬ (master (c1 delta) s2).Nonempty := by
  rintro ⟨z,hz⟩
  obtain ⟨_,⟨k,h0,h1,he⟩,_,_,_,hn0,hn1,_⟩ := (master_s2 true 1 1 1 delta z).mp hz
  rcases binary_value h0 h1 with rfl|rfl
  · exact hn0 (by simpa using he)
  · exact hn1 (by simpa using he)

theorem s01 : s0 ≠ s1 := by
  intro h; have he := congrArg (fun s => s.history.length) h
  simp [s0,s1,append,initialState] at he
theorem s02 : s0 ≠ s2 := by
  intro h; have he := congrArg (fun s => s.history.length) h
  simp [s0,s1,s2,append,initialState] at he
theorem s12 : s1 ≠ s2 := by
  intro h; have he := congrArg (fun s => s.history.length) h
  simp [s0,s1,s2,append,initialState] at he

def patch {n m l r : ℕ} {d : Data n m l r} {cap : Option ℕ}
    (atState : State n m) (dec : Decision d cap atState) (fallback : Selector d cap) :
    Selector d cap := by
  classical
  exact fun s => if h : s=atState then h.symm ▸ dec else fallback s

@[simp] theorem patch_same {n m l r : ℕ} {d : Data n m l r} {cap : Option ℕ}
    (s : State n m) (dec : Decision d cap s) (fallback : Selector d cap) :
    patch s dec fallback s = dec := by simp [patch]
theorem patch_other {n m l r : ℕ} {d : Data n m l r} {cap : Option ℕ}
    (s t : State n m) (dec : Decision d cap s) (fallback : Selector d cap) (h : t≠s) :
    patch s dec fallback t = fallback t := by simp [patch,h]

def choose1 : Selector (c1 1) none :=
  patch s0 (.next e0 (c1_continue0 1))
    (patch s1 (.stop (.emptyProjection (iv 1)) stop_delta1)
      (Classical.choice (selector_nonempty (c1 1) (c1_analytic 1 (by norm_num)) none)))

def choose0 : Selector (c1 0) none :=
  patch s0 (.next e0 (c1_continue0 0))
    (patch s1 (.next e1 c1_continue1)
      (patch s2 (.stop .emptyMaster (.emptyMaster (c1_master2_empty 0)))
        (Classical.choice (selector_nonempty (c1 0) (c1_analytic 0 (by norm_num)) none))))

def out1 : LoopOutput 1 1 := ⟨s1,.emptyProjection (iv 1),1,2,2,1⟩
def out0 : LoopOutput 1 1 := ⟨s2,.emptyMaster,2,2,3,2⟩

theorem run_delta1 (fuel : ℕ) : run (c1 1) choose1 (fuel+2) s0 = some out1 := by
  rw [run]
  simp only [choose1,patch_same]
  change (run (c1 1) choose1 (fuel+1) s1).map (LoopOutput.bump e0) = _
  rw [run]
  simp [choose1,patch,s01.symm,terminalOutput,terminalProjectionCount,LoopOutput.bump,
    polishCount,e0,out1]

theorem run_delta0 (fuel : ℕ) : run (c1 0) choose0 (fuel+3) s0 = some out0 := by
  rw [run]
  simp only [choose0,patch_same]
  change ((run (c1 0) choose0 (fuel+2) s1).map (LoopOutput.bump e0)) = _
  rw [run]
  simp only [choose0,patch_other _ _ _ _ s01.symm,patch_same]
  change ((run (c1 0) choose0 (fuel+1) s2).map (LoopOutput.bump e1)).map (LoopOutput.bump e0) = _
  rw [run]
  simp [choose0,patch,s02.symm,s12.symm,terminalOutput,terminalProjectionCount,LoopOutput.bump,
    polishCount,e0,e1,out0]

theorem old_incumbent_timestamp : s1.incumbent = some (pt 0 0) ∧
    s2.incumbent = some (pt 0 0) ∧ s1.lastSuccess = some 0 ∧ s2.lastSuccess = some 1 ∧
    (c1 0).f (pt 0 0) = (c1 0).f (pt 0 1) := by
  norm_num [s1,s2,s0,append,initialState,e0,e1,c1,data,pt]

theorem iv_eta (y : IntVector 1) : iv (y 0) = y := by
  funext j; fin_cases j; rfl

theorem box_binary (bounded : Bool) (a b delta shift : ℝ) :
    (data bounded a b 1 delta shift).box = {iv 0,iv 1} := by
  classical
  ext y
  simp only [Data.box,Set.Finite.mem_toFinset,IntegerBox,Set.mem_setOf_eq,data,model,
    Fin.forall_fin_one,Finset.mem_insert,Finset.mem_singleton]
  constructor
  · intro h
    rcases binary_value h.1 h.2 with he|he
    · left; rw [← iv_eta y,he]
    · right; rw [← iv_eta y,he]
  · rintro (rfl|rfl) <;> norm_num [iv]

theorem box_binary_card (bounded : Bool) (a b delta shift : ℝ) :
    (data bounded a b 1 delta shift).box.card = 2 := by
  classical
  rw [box_binary]
  have hne : iv 0 ≠ iv 1 := by intro he; have := congrFun he 0; norm_num [iv] at this
  simp [hne]

theorem fractional_seed (bounded : Bool) (a b upper delta shift : ℝ) :
    seed ∉ (data bounded a b upper delta shift).original := by
  intro hp
  obtain ⟨y,_,he⟩ := hp.2
  have hy : (y 0:ℝ) = 1/2 := by simpa [seed,pt] using (congrFun he 0).symm
  have hlo : 0 < y 0 := by exact_mod_cast (show (0:ℝ)<(y 0:ℝ) by rw [hy]; norm_num)
  have hhi : y 0 < 1 := by exact_mod_cast (show (y 0:ℝ)<1 by rw [hy]; norm_num)
  omega


end Chapter03.FPControls
