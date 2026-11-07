module

public import Chapter10

@[expose] public section

noncomputable section
namespace Chapter10Examples
open Chapter10

def oneIncidence : Fin 1 → Fin 1 → Bool := fun _ _ => true
def oneCost : Fin 1 → ℝ := fun _ => 1

private noncomputable def __migrationExample_Chapter10Examples_L10_N001 : feasible oneIncidence (fun _ => true) := by
  simp [feasible, coverCount, oneIncidence]

private noncomputable def __migrationExample_Chapter10Examples_L13_N002 : ¬ feasible oneIncidence (fun _ => false) := by
  simp [feasible, coverCount, oneIncidence]

private noncomputable def __migrationExample_Chapter10Examples_L16_N003 : energyMin oneIncidence oneCost 2 (fun _ => true) := by
  intro y
  have hcases : y = (fun _ => false) ∨ y = (fun _ => true) := by
    cases hy : y 0
    · left; funext i; fin_cases i; exact hy
    · right; funext i; fin_cases i; exact hy
  rcases hcases with rfl | rfl <;>
    norm_num [energy, cost, penalty, coverCount, bit, oneIncidence, oneCost, Finset.filter_singleton]

private noncomputable def __migrationExample_Chapter10Examples_L25_N004 : routeMin oneIncidence oneCost (fun _ => true) := by
  constructor
  · simp [feasible, coverCount, oneIncidence]
  · intro y hy
    have hz := hy 0
    simp only [coverCount, Fin.sum_univ_one, oneIncidence, Bool.true_and] at hz
    have hbit : y 0 = true := by
      cases h : y 0 <;> simp [h] at hz ⊢
    simp only [cost, Fin.sum_univ_one, oneCost, hbit]
    norm_num [bit]

private noncomputable def __migrationExample_Chapter10Examples_L36_N005 : ¬ ∃ x : Bits 1, feasible (fun (_ : Fin 1) (_ : Fin 1) => false) x := by
  simp [feasible, coverCount]

private noncomputable def __migrationExample_Chapter10Examples_L39_N006 : feasible (fun (_ : Fin 0) (_ : Fin 0) => false) (fun _ => false) := by
  intro i
  exact Fin.elim0 i

private noncomputable def __migrationExample_Chapter10Examples_L43_N007 : energy oneIncidence oneCost 1 (fun _ => false) =
    energy oneIncidence oneCost 1 (fun _ => true) := by
  norm_num [energy, cost, penalty, coverCount, bit, oneIncidence, oneCost, Finset.filter_singleton]

end Chapter10Examples
