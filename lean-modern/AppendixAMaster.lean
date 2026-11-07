module

public import AppendixAEdges

@[expose] public section

noncomputable section
open scoped BigOperators
namespace AppendixATheory

def incidentBit {n m : ℕ} (E : Finset (Fin n × Fin n)) (A : Alpha n m)
    (j : Fin m) (a : Fin n) (x : Fin n × Bool) : Bool :=
  decide ((if x.2 then (x.1,a) else (a,x.1)) ∈ E) && A x.1 j

def incidentSum {n m : ℕ} (E : Finset (Fin n × Fin n)) (A : Alpha n m)
    (j : Fin m) (a : Fin n) : ℝ :=
  ∑ x : Fin n × Bool, Chapter10.bit (incidentBit E A j a x)

theorem bit_nonneg (b : Bool) : (0 : ℝ) ≤ Chapter10.bit b := by
  cases b <;> norm_num [Chapter10.bit]

theorem incidentSum_nonneg {n m : ℕ} (E : Finset (Fin n × Fin n))
    (A : Alpha n m) (j : Fin m) (a : Fin n) : 0 ≤ incidentSum E A j a := by
  exact Finset.sum_nonneg (fun x _ => bit_nonneg _)

theorem incidentSum_ge_one_iff {n m : ℕ} (E : Finset (Fin n × Fin n))
    (A : Alpha n m) (j : Fin m) (a : Fin n) :
    1 ≤ incidentSum E A j a ↔ ∃ b ∈ fiber A j, AppendixA.adjacent E a b := by
  rw [incidentSum, bit_sum_ge_one_iff]
  constructor
  · rintro ⟨⟨b,o⟩,_,hb⟩
    simp only [incidentBit, Bool.and_eq_true, decide_eq_true_eq] at hb
    refine ⟨b, (mem_fiber A b j).mpr hb.2, ?_⟩
    cases o
    · exact Or.inl hb.1
    · exact Or.inr hb.1
  · rintro ⟨b,hb,hadj⟩
    have hflag := (mem_fiber A b j).mp hb
    rcases hadj with hab | hba
    · exact ⟨(b,false), Finset.mem_univ _, by simp [incidentBit,hab,hflag]⟩
    · exact ⟨(b,true), Finset.mem_univ _, by simp [incidentBit,hba,hflag]⟩

theorem incidentSum_literal {n m : ℕ} (E : Finset (Fin n × Fin n))
    (A : Alpha n m) (j : Fin m) (a : Fin n) :
    incidentSum E A j a =
      (∑ b : Fin n, if (a,b) ∈ E then Chapter10.bit (A b j) else 0) +
      (∑ b : Fin n, if (b,a) ∈ E then Chapter10.bit (A b j) else 0) := by
  simp only [incidentSum, Fintype.sum_prod_type, Fintype.sum_bool]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro b hb
  by_cases hab : (a,b) ∈ E <;> by_cases hba : (b,a) ∈ E <;>
    cases hflag : A b j <;> simp [incidentBit, hab, hba, hflag, Chapter10.bit]

def WRows {n m : ℕ} (E : Finset (Fin n × Fin n)) (A : Alpha n m)
    (w : Fin m → Bool) : Prop :=
  ∀ j, ((fiber A j).card : ℝ) - (n : ℝ) * Chapter10.bit (w j) ≤ 1 ∧
    ∀ a, (n : ℝ) * (1 - Chapter10.bit (A a j)) + incidentSum E A j a ≥
      Chapter10.bit (w j)

theorem wRows_neighborRows {n m : ℕ} (E : Finset (Fin n × Fin n))
    (A : Alpha n m) (w : Fin m → Bool) (h : WRows E A w) : NeighborRows E A := by
  intro j hsize a ha
  have hsizeR : (1 : ℝ) < ((fiber A j).card : ℝ) := by exact_mod_cast hsize
  have hw : w j = true := by
    cases heq : w j
    · have hs := (h j).1
      norm_num [heq, Chapter10.bit] at hs
      linarith
    · rfl
  have hn := (h j).2 a
  have hflag := (mem_fiber A a j).mp ha
  simp only [hflag,hw,Chapter10.bit,ite_true,sub_self,mul_zero,zero_add] at hn
  exact (incidentSum_ge_one_iff E A j a).mp hn

def sizeFlag {n m : ℕ} (A : Alpha n m) (j : Fin m) : Bool :=
  decide (1 < (fiber A j).card)

theorem neighborRows_wRows {n m : ℕ} (E : Finset (Fin n × Fin n))
    (A : Alpha n m) (h : NeighborRows E A) : WRows E A (sizeFlag A) := by
  intro j
  have hcard : (fiber A j).card ≤ n := by
    simpa using Finset.card_le_univ (fiber A j)
  have hcardR : ((fiber A j).card : ℝ) ≤ (n : ℝ) := by exact_mod_cast hcard
  by_cases hsize : 1 < (fiber A j).card
  · have hw : sizeFlag A j = true := by simp [sizeFlag,hsize]
    refine ⟨?_, ?_⟩
    · simp only [hw,Chapter10.bit,ite_true,mul_one]
      linarith
    · intro a
      by_cases ha : A a j = true
      · have hn := (incidentSum_ge_one_iff E A j a).mpr
          (h j hsize a ((mem_fiber A a j).mpr ha))
        simpa [hw,ha,Chapter10.bit] using hn
      · have hn := incidentSum_nonneg E A j a
        have hn1 : (1 : ℝ) ≤ (n : ℝ) := by
          have hp := a.isLt
          have : 1 ≤ n := by omega
          exact_mod_cast this
        simp [hw,Chapter10.bit,ha]
        linarith
  · have hw : sizeFlag A j = false := by simp [sizeFlag,hsize]
    have hs : (fiber A j).card ≤ 1 := by omega
    have hsR : ((fiber A j).card : ℝ) ≤ 1 := by exact_mod_cast hs
    refine ⟨by simpa [hw,Chapter10.bit] using hsR, ?_⟩
    intro a
    have hn := incidentSum_nonneg E A j a
    have hn0 : (0 : ℝ) ≤ (n : ℝ) := by positivity
    cases ha : A a j <;> simp [hw,ha,Chapter10.bit] <;> linarith

theorem w_projection {n m : ℕ} (E : Finset (Fin n × Fin n)) (A : Alpha n m) :
    (∃ w, WRows E A w) ↔ NeighborRows E A :=
  ⟨fun ⟨w,h⟩ => wRows_neighborRows E A w h,
    fun h => ⟨sizeFlag A,neighborRows_wRows E A h⟩⟩

theorem w_exact_size_indicator {n m : ℕ} (E : Finset (Fin n × Fin n))
    (A : Alpha n m) (w : Fin m → Bool) (hloop : LoopFree E)
    (hne : ∀ j, (fiber A j).Nonempty) (h : WRows E A w) (j : Fin m) :
    w j = true ↔ 1 < (fiber A j).card := by
  constructor
  · intro hw
    by_contra hs
    have hc : (fiber A j).card ≤ 1 := by omega
    obtain ⟨a,ha⟩ := hne j
    have hflag := (mem_fiber A a j).mp ha
    have hn := (h j).2 a
    simp only [hw,hflag,Chapter10.bit,ite_true,sub_self,mul_zero,zero_add] at hn
    obtain ⟨b,hb,hab⟩ := (incidentSum_ge_one_iff E A j a).mp hn
    have heq : a = b := Finset.card_le_one.mp hc a ha b hb
    exact hloop a (by simpa [← heq] using hab)
  · intro hs
    cases hw : w j
    · have hh := (h j).1
      norm_num [hw,Chapter10.bit] at hh
      have hsR : (1 : ℝ) < ((fiber A j).card : ℝ) := by exact_mod_cast hs
      linarith
    · rfl

def RepairedMasterRows {n m : ℕ} (E : Finset (Fin n × Fin n))
    (L : Finset (Fin m × Fin m)) (k : ℕ) (A : Alpha n m)
    (Z : EdgeAux n m) (w : Fin m → Bool) : Prop :=
  RowBounds k A ∧ SelectedEdgeRows E L A Z ∧ WRows E A w

theorem repaired_master_projection {n m : ℕ} (E : Finset (Fin n × Fin n))
    (L : Finset (Fin m × Fin m)) (k : ℕ) (A : Alpha n m) :
    (∃ Z w, RepairedMasterRows E L k A Z w) ↔ RelaxedMaster E L k A := by
  constructor
  · rintro ⟨Z,w,hr,hz,hw⟩
    exact ⟨hr,(selected_edge_projection E L A).mp ⟨Z,hz⟩,
      (w_projection E A).mp ⟨w,hw⟩⟩
  · rintro ⟨hr,he,hn⟩
    obtain ⟨Z,hz⟩ := (selected_edge_projection E L A).mpr he
    obtain ⟨w,hw⟩ := (w_projection E A).mpr hn
    exact ⟨Z,w,hr,hz,hw⟩

theorem embedding_master_extension {n m : ℕ} (E : Finset (Fin n × Fin n))
    (L : Finset (Fin m × Fin m)) (k : ℕ) (A : Alpha n m)
    (h : Embedding E L k A) : ∃ Z w, RepairedMasterRows E L k A Z w :=
  (repaired_master_projection E L k A).mpr (embedding_relaxedMaster E L k A h)

end AppendixATheory

#print axioms AppendixATheory.incidentSum_literal
#print axioms AppendixATheory.w_projection
#print axioms AppendixATheory.w_exact_size_indicator
#print axioms AppendixATheory.repaired_master_projection
#print axioms AppendixATheory.embedding_master_extension
