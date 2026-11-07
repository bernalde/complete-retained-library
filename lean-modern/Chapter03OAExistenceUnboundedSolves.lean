module

public import Chapter03OAExistenceUnboundedData

@[expose] public section

/-! Exact individual-slack restoration replies for both empty integer fibers.
Every minimizing reply is the same x=0 and both slacks equal 1/4. -/
noncomputable section
open scoped BigOperators
open Chapter02 Chapter03.OAKKT
namespace Chapter03.OAExec.UnboundedControl

def slack : RealVector 2 := fun _ => 1/4
def event (b : Fin 2) : Event spec :=
  ⟨target b,target_mem b,0,some slack⟩

theorem target_injective : Function.Injective target := by
  intro b c h
  apply Fin.ext
  have he := congrFun h 0
  change (b.val : ℤ) = (c.val : ℤ) at he
  exact_mod_cast he

theorem intCast_target_injective : Function.Injective (fun b => intCast (target b)) := by
  intro b c h
  apply Fin.ext
  have he := congrFun h 0
  change ((b.val : ℤ) : ℝ) = ((c.val : ℤ) : ℝ) at he
  exact_mod_cast he

theorem restoration_feasible (b : Fin 2) :
    weightedInsert (0 : RealVector 2) slack ∈ restSet model (intCast (target b)) := by
  rw [restSet_insert_iff]
  refine ⟨by intro i; exact Fin.elim0 i,?_,?_⟩
  · intro j
    fin_cases b <;> fin_cases j <;> norm_num [soft,model,row,sign,intCast,target,slack]
  · intro j
    norm_num [slack]

theorem restoration_lower (b : Fin 2) (x s : RealVector 2)
    (hq : weightedInsert x s ∈ restSet model (intCast (target b))) :
    (1/2 : ℝ) + 2*(x 0)^2 + 2*(x 1)^2 ≤ s 0+s 1 := by
  have h0 := ((restSet_insert_iff model (intCast (target b)) x s).mp hq).2.1 0
  have h1 := ((restSet_insert_iff model (intCast (target b)) x s).mp hq).2.1 1
  fin_cases b <;> norm_num [soft,model,row,sign,intCast,target] at h0 h1 <;> linarith

theorem restoration_minimum (b : Fin 2) :
    IsMinimizer (restSet model (intCast (target b))) restCost
      (weightedInsert (0 : RealVector 2) slack) := by
  refine ⟨restoration_feasible b,?_⟩
  intro q hq
  rw [← weightedInsert_project q] at hq ⊢
  have hlo := restoration_lower b (weightedX q) (weightedV q) hq
  simp only [restCost_insert,Fin.sum_univ_two]
  norm_num [slack]
  nlinarith [sq_nonneg (weightedX q 0),sq_nonneg (weightedX q 1)]

theorem restoration_unique (b : Fin 2) (x s : RealVector 2)
    (hm : IsMinimizer (restSet model (intCast (target b))) restCost (weightedInsert x s)) :
    x = 0 ∧ s = slack := by
  have hcost := hm.2 (weightedInsert (0 : RealVector 2) slack) (restoration_feasible b)
  simp only [restCost_insert,Fin.sum_univ_two] at hcost
  norm_num [slack] at hcost
  have hlo := restoration_lower b x s hm.1
  have hx0 : x 0 = 0 := by nlinarith [sq_nonneg (x 0),sq_nonneg (x 1)]
  have hx1 : x 1 = 0 := by nlinarith [sq_nonneg (x 0),sq_nonneg (x 1)]
  have hx : x = 0 := by ext i; fin_cases i <;> simp [hx0,hx1]
  have h0 := ((restSet_insert_iff model (intCast (target b)) x s).mp hm.1).2.1 0
  have h1 := ((restSet_insert_iff model (intCast (target b)) x s).mp hm.1).2.1 1
  have hs0 : s 0 = 1/4 := by
    fin_cases b <;> norm_num [soft,model,row,sign,intCast,target,hx] at h0 h1 <;> linarith
  have hs1 : s 1 = 1/4 := by
    fin_cases b <;> norm_num [soft,model,row,sign,intCast,target,hx] at h0 h1 <;> linarith
  refine ⟨hx,?_⟩
  ext i
  fin_cases i <;> simp [slack,hs0,hs1]

theorem event_valid (b : Fin 2) : EventValid spec (event b) :=
  assumptions.every_exact_restoration_event (target b) (target_mem b) 0 slack
    (fibers_empty (target b) (target_mem b)) (restoration_minimum b)

theorem valid_event_form {e : Event spec} (he : EventValid spec e) :
    ∃ b : Fin 2, e = event b := by
  rcases e with ⟨y,hy,x,s⟩
  obtain ⟨b,rfl⟩ : ∃ b : Fin 2, y = target b := by
    rcases target_cases y hy with h | h
    · exact ⟨0,h⟩
    · exact ⟨1,h⟩
  cases s with
  | none =>
    exact False.elim (fibers_empty (target b) hy ⟨x,he.2.1.1⟩)
  | some s =>
    obtain ⟨rfl,rfl⟩ := restoration_unique b x s he.2.2
    exact ⟨b,rfl⟩

theorem valid_event_restoration {e : Event spec} (he : EventValid spec e) :
    e.restoration = some slack := by
  obtain ⟨b,rfl⟩ := valid_event_form he
  rfl

theorem row_not_affine (j : Fin 2) : ¬ AffineRow (row j) := by
  rintro ⟨ax,ay,b,h⟩
  have h0 := h (pt 0 0 (1/2))
  have h1 := h (pt 0 1 (1/2))
  have hn := h (pt 0 (-1) (1/2))
  norm_num [row,pt,LinearForm,Fin.sum_univ_two,Fin.sum_univ_one] at h0 h1 hn
  linarith

theorem selected_event (b : Fin 2) : spec.selected (event b).anchor = Set.univ := by
  ext j
  simp only [Data.selected,Data.nonlinear,Set.mem_setOf_eq,Set.mem_univ,iff_true]
  refine ⟨row_not_affine j,?_⟩
  fin_cases b <;> fin_cases j <;>
    norm_num [spec,model,row,sign,Event.anchor,event,intCast,target]

theorem event_restorations (b : Fin 2) : eventRestorations (event b) = 1 := by
  simp [eventRestorations,event]

end Chapter03.OAExec.UnboundedControl

#print axioms Chapter03.OAExec.UnboundedControl.restoration_unique
#print axioms Chapter03.OAExec.UnboundedControl.valid_event_form
