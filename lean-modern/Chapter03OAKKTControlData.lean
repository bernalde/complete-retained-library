module

public import Chapter03OAKKTControlBase

@[expose] public section

noncomputable section
open Chapter02 Chapter02.DICOPT Chapter02DICOPTExamples
open scoped BigOperators
namespace Chapter03.OAKKT.Controls

theorem integer_binary (y : V) :
    (∃z : IntVector 1,z∈IntegerBox (scalar 0) (scalar 1) ∧
      y=fun i => (z i : ℝ)) ↔ Binary y := by
  constructor
  · rintro ⟨z,hz,rfl⟩ i
    have hz0 : (0:ℝ)≤(z i:ℝ) := by simpa [scalar] using (hz i).1
    have hz1 : (z i:ℝ)≤(1:ℝ) := by simpa [scalar] using (hz i).2
    have h0 : (0:ℤ)≤z i := by exact_mod_cast hz0
    have h1 : z i≤(1:ℤ) := by exact_mod_cast hz1
    have he : z i=0 ∨ z i=1 := by omega
    rcases he with he|he
    · left; simp [he]
    · right; simp [he]
  · intro hy
    rcases hy 0 with he|he
    · refine ⟨fun _ => 0,?_,?_⟩
      · intro i; norm_num [scalar]
      · ext i; fin_cases i; simpa using he
    · refine ⟨fun _ => 1,?_,?_⟩
      · intro i; norm_num [scalar]
      · ext i; fin_cases i; simpa using he

theorem final_original_identity : finalModel.feasibleOn Set.univ=
    Chapter02DICOPTSupplemental.positiveData.original := by
  ext p
  rw [source_feasible_iff]
  simp only [Set.mem_univ,true_and]
  change ((∀j : Fin 1,positiveG p≤0) ∧ p∈finalModel.linearRegion ∧
    (∃z : IntVector 1,z∈IntegerBox (scalar 0) (scalar 1) ∧
      p.2=fun i => (z i : ℝ))) ↔ _
  rw [integer_binary,final_hard]
  simp [Data.original,Chapter02DICOPTSupplemental.positive_feasible,positiveG,
    and_assoc,and_left_comm,and_comm]

theorem thesis_original_identity : thesisModel.feasibleOn Set.univ=
    Chapter02DICOPTSupplemental.positiveData.original := by
  ext p
  rw [source_feasible_iff]
  simp only [Set.mem_univ,true_and]
  change ((∀j,thesisModel.g j p≤0) ∧ p∈thesisModel.linearRegion ∧
    (∃z : IntVector 1,z∈IntegerBox (scalar 0) (scalar 1) ∧
      p.2=fun i => (z i : ℝ))) ↔ _
  rw [integer_binary,thesis_rows]
  simp only [thesis_hard,true_and]
  constructor
  · rintro ⟨⟨hg,hl,hu,_,_⟩,hy⟩
    exact ⟨(Chapter02DICOPTSupplemental.positive_feasible _ _).mpr ⟨hl,hu,hg⟩,hy⟩
  · rintro ⟨hp,hy⟩
    obtain ⟨hl,hu,hg⟩ := (Chapter02DICOPTSupplemental.positive_feasible _ _).mp hp
    refine ⟨⟨hg,hl,hu,?_,?_⟩,hy⟩ <;> rcases hy 0 with h|h <;> simp [h]

theorem final_original_minimum :
    IsMinimizer (finalModel.feasibleOn Set.univ) positiveF (pt (1/2) 1) := by
  rw [final_original_identity]
  rw [show positiveF=pointObjective Chapter02DICOPTSupplemental.positiveData from
    funext positive_objective_identity]
  simpa only [pt] using
    Chapter02DICOPTSupplemental.positive_original_minimum

theorem thesis_original_minimum :
    IsMinimizer (thesisModel.feasibleOn Set.univ) positiveF (pt (1/2) 1) := by
  rw [thesis_original_identity]
  rw [show positiveF=pointObjective Chapter02DICOPTSupplemental.positiveData from
    funext positive_objective_identity]
  simpa only [pt] using
    Chapter02DICOPTSupplemental.positive_original_minimum

theorem final_relaxation (p : P) : p∈finalModel.relaxationOn Set.univ ↔
    (1/2:ℝ)≤p.1 0 ∧ p.1 0≤1 ∧ (p.1 0)^2≤p.2 0 ∧ 0≤p.2 0 ∧ p.2 0≤1 := by
  change ((p∈Set.univ ∧ (∀j : Fin 1,positiveG p≤0)) ∧
    p∈finalModel.linearRegion ∧
    (∀i,finalModel.lo i≤p.2 i ∧ p.2 i≤finalModel.hi i)) ↔ _
  rw [final_hard]
  simp [finalModel,positiveG,Fin.forall_fin_one,scalar,and_assoc] <;> tauto

theorem thesis_relaxation (p : P) : p∈thesisModel.relaxationOn Set.univ ↔
    (1/2:ℝ)≤p.1 0 ∧ p.1 0≤1 ∧ (p.1 0)^2≤p.2 0 ∧ 0≤p.2 0 ∧ p.2 0≤1 := by
  change ((p∈Set.univ ∧ (∀j,thesisModel.g j p≤0)) ∧
    p∈thesisModel.linearRegion ∧
    (∀i,thesisModel.lo i≤p.2 i ∧ p.2 i≤thesisModel.hi i)) ↔ _
  rw [thesis_rows]
  simp only [thesis_hard,Set.mem_univ,true_and]
  simp [thesisModel,scalar,Fin.forall_fin_one,and_assoc] <;> tauto

theorem final_relaxed_seed :
    IsMinimizer (finalModel.relaxationOn Set.univ) positiveF (pt (1/2) (1/4)) := by
  refine ⟨(final_relaxation _).mpr (by norm_num [pt,scalar]),?_⟩
  intro q hq
  obtain ⟨hl,hu,hg,hy0,hy1⟩ := (final_relaxation q).mp hq
  norm_num [positiveF,pt,scalar]
  nlinarith [sq_nonneg (q.1 0-1/2)]

theorem thesis_relaxed_seed :
    IsMinimizer (thesisModel.relaxationOn Set.univ) positiveF (pt (1/2) (1/4)) := by
  refine ⟨(thesis_relaxation _).mpr (by norm_num [pt,scalar]),?_⟩
  intro q hq
  exact final_relaxed_seed.2 q ((final_relaxation q).mpr ((thesis_relaxation q).mp hq))

def thesisSlack : RealVector 5 := ![1/4,0,0,0,0]
def thesisLambda : RealVector 5 := ![1,1,0,0,0]
def thesisNu : RealVector 5 := ![0,0,1,1,1]

theorem final_restoration_bound (x : V) (s : RealVector 1)
    (hl : (1/2:ℝ)≤x 0) (hg : ∀j,finalModel.g j (x,scalar 0)≤s j) :
    (1/4:ℝ)≤∑j,s j := by
  have hh := hg 0
  norm_num [finalModel,positiveG,scalar,Fin.sum_univ_one] at hh ⊢
  nlinarith [sq_nonneg (x 0-1/2)]

theorem thesis_restoration_bound (x : V) (s : RealVector 5)
    (hg : ∀j,thesisModel.g j (x,scalar 0)≤s j) (hs : ∀j,0≤s j) :
    (1/4:ℝ)≤∑j,s j := by
  have h0 := hg 0
  have h1 := hg 1
  norm_num [thesisModel,positiveG,scalar] at h0 h1
  norm_num [Fin.sum_univ_succ]
  change (1/4:ℝ)≤s 0+(s 1+(s 2+(s 3+s 4)))
  nlinarith [sq_nonneg (x 0-1/2),hs 2,hs 3,hs 4]

theorem thesis_slack_feasible : (∀j,0≤thesisSlack j) ∧
    (∀j,thesisModel.g j (pt (1/2) 0)≤thesisSlack j) := by
  constructor <;> intro j <;> fin_cases j <;>
    norm_num [thesisSlack,thesisModel,positiveG,pt,scalar]

theorem thesis_scalar_kkt :
    (∀j,0≤thesisLambda j) ∧ (∀j,0≤thesisNu j) ∧
    (∀j,1-thesisLambda j-thesisNu j=0) ∧
    (∀j,thesisLambda j*(thesisModel.g j (pt (1/2) 0)-thesisSlack j)=0) ∧
    (∀j,thesisNu j*thesisSlack j=0) ∧
    (∑j,thesisLambda j)=2 ∧ (∑j,thesisSlack j)=(1/4:ℝ) := by
  norm_num [thesisLambda,thesisNu,thesisSlack,thesisModel,positiveG,pt,scalar,
    Fin.forall_fin_succ,Fin.sum_univ_succ]


end Chapter03.OAKKT.Controls
