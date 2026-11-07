module

public import Chapter02FBBTOperator

@[expose] public section

/-! Continuity of the actual simultaneous affine raw endpoint map, for each
fixed finite matrix and initial endpoint record. Sign tests and zero tests depend
only on that fixed matrix. Seeded extrema include their seed even in dimension
zero. No continuity assertion is made for the public empty-state test. -/
noncomputable section
open Classical
open scoped BigOperators
namespace Chapter02FBBT

private theorem lower_continuous {ι : Type*} (i : ι) :
    Continuous (fun q : Bounds ι => q.1 i) :=
  (continuous_apply i).comp continuous_fst

private theorem upper_continuous {ι : Type*} (i : ι) :
    Continuous (fun q : Bounds ι => q.2 i) :=
  (continuous_apply i).comp continuous_snd

theorem productLo_continuous {n m : ℕ} (A : Matrix n m) (i : Fin m) (j : Fin n) :
    Continuous (fun q => productLo A q i j) := by
  unfold productLo Chapter02.affineProductLo
  split_ifs
  · exact continuous_const.mul (lower_continuous _)
  · exact continuous_const.mul (upper_continuous _)

theorem productHi_continuous {n m : ℕ} (A : Matrix n m) (i : Fin m) (j : Fin n) :
    Continuous (fun q => productHi A q i j) := by
  unfold productHi Chapter02.affineProductHi
  split_ifs
  · exact continuous_const.mul (upper_continuous _)
  · exact continuous_const.mul (lower_continuous _)

theorem imageLo_continuous {n m : ℕ} (A : Matrix n m) (i : Fin m) :
    Continuous (fun q => imageLo A q i) := by
  exact continuous_finset_sum _ (fun j _ => productLo_continuous A i j)

theorem imageHi_continuous {n m : ℕ} (A : Matrix n m) (i : Fin m) :
    Continuous (fun q => imageHi A q i) := by
  exact continuous_finset_sum _ (fun j _ => productHi_continuous A i j)

theorem restLo_continuous {n m : ℕ} (A : Matrix n m) (i : Fin m) (j : Fin n) :
    Continuous (fun q => restLo A q i j) := by
  exact continuous_finset_sum _ (fun k _ => productLo_continuous A i k)

theorem restHi_continuous {n m : ℕ} (A : Matrix n m) (i : Fin m) (j : Fin n) :
    Continuous (fun q => restHi A q i j) := by
  exact continuous_finset_sum _ (fun k _ => productHi_continuous A i k)

theorem inverseLo_continuous {n m : ℕ} (A : Matrix n m) (i : Fin m) (j : Fin n) :
    Continuous (fun q => inverseLo A q i j) := by
  unfold inverseLo
  split_ifs
  · exact lower_continuous _
  · exact ((lower_continuous _).sub (restHi_continuous A i j)).div_const _
  · exact ((upper_continuous _).sub (restLo_continuous A i j)).div_const _

theorem inverseHi_continuous {n m : ℕ} (A : Matrix n m) (i : Fin m) (j : Fin n) :
    Continuous (fun q => inverseHi A q i j) := by
  unfold inverseHi
  split_ifs
  · exact upper_continuous _
  · exact ((upper_continuous _).sub (restLo_continuous A i j)).div_const _
  · exact ((lower_continuous _).sub (restHi_continuous A i j)).div_const _

theorem seededMax_continuous {X : Type*} [TopologicalSpace X] {m : ℕ}
    (seed : X → ℝ) (v : Fin m → X → ℝ)
    (hs : Continuous seed) (hv : ∀ i, Continuous (v i)) :
    Continuous (fun x => seededMax (seed x) (fun i => v i x)) := by
  unfold seededMax
  apply Continuous.finset_sup'_apply
  intro o _
  cases o with
  | none => exact hs
  | some i => exact hv i

theorem seededMin_continuous {X : Type*} [TopologicalSpace X] {m : ℕ}
    (seed : X → ℝ) (v : Fin m → X → ℝ)
    (hs : Continuous seed) (hv : ∀ i, Continuous (v i)) :
    Continuous (fun x => seededMin (seed x) (fun i => v i x)) := by
  unfold seededMin
  apply Continuous.finset_inf'_apply
  intro o _
  cases o with
  | none => exact hs
  | some i => exact hv i

theorem upward_continuous {n m : ℕ} (A : Matrix n m) : Continuous (upward A) := by
  apply Continuous.prodMk
  · apply continuous_pi
    intro c
    cases c with
    | inl j => exact lower_continuous _
    | inr i => exact (lower_continuous _).max (imageLo_continuous A i)
  · apply continuous_pi
    intro c
    cases c with
    | inl j => exact upper_continuous _
    | inr i => exact (upper_continuous _).min (imageHi_continuous A i)

theorem downward_continuous {n m : ℕ} (A : Matrix n m) : Continuous (downward A) := by
  apply Continuous.prodMk
  · apply continuous_pi
    intro c
    cases c with
    | inl j =>
      exact seededMax_continuous _ _ (lower_continuous _)
        (fun i => inverseLo_continuous A i j)
    | inr i => exact lower_continuous _
  · apply continuous_pi
    intro c
    cases c with
    | inl j =>
      exact seededMin_continuous _ _ (upper_continuous _)
        (fun i => inverseHi_continuous A i j)
    | inr i => exact upper_continuous _

theorem clip_fixed_continuous {ι : Type*} (q0 : Bounds ι) :
    Continuous (fun q => clip q q0) := by
  exact (continuous_pi (fun i => (lower_continuous i).max continuous_const)).prodMk
    (continuous_pi (fun i => (upper_continuous i).min continuous_const))

theorem rawF_continuous {n m : ℕ} (A : Matrix n m) (q0 : JointBounds n m) :
    Continuous (rawF A q0) := by
  exact (downward_continuous A).comp ((upward_continuous A).comp (clip_fixed_continuous q0))

end Chapter02FBBT
