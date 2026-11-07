module

public import Chapter03OAKKTMaps
public import Chapter03OAKKTControlHistory

@[expose] public section

noncomputable section
open Chapter02 Chapter02DICOPTExamples
namespace Chapter03.OAKKT.Controls

def thesisIntegerBounds : IntegerBoundRows thesisModel where
  lower := fun _ => 3
  upper := fun _ => 4
  lower_eq i p := by fin_cases i; exact thesis_integer_lower_identity p
  upper_eq i p := by fin_cases i; exact thesis_integer_upper_identity p

def activeIntegerBounds : IntegerBoundRows activeModel where
  lower := fun _ => 1
  upper := fun _ => 2
  lower_eq i p := by fin_cases i; exact active_integer_lower_identity p
  upper_eq i p := by fin_cases i; exact active_integer_upper_identity p

theorem thesis_source_original_identity :
    sourceOriginal thesisModel=thesisModel.feasibleOn Set.univ := by
  ext p
  exact thesisIntegerBounds.original_iff p

theorem thesis_source_master_identity (b : ℝ) :
    sourceMaster thesisModel positiveF (thesisFamily b) (positiveHistoryDf b)=
      Chapter06.EpigraphMaster thesisModel positiveF (thesisFamily b)
        (positiveHistoryDf b) Set.univ := by
  ext z
  exact thesisIntegerBounds.master_iff positiveF (thesisFamily b) (positiveHistoryDf b)
    (thesisHistory b).seed (thesisHistory b).initial_all
    ((thesisHistory b).g_derivative (thesisHistory b).seed) z

theorem active_source_master_identity :
    sourceMaster activeModel activeF activeFamily activeHistoryDf=
      Chapter06.EpigraphMaster activeModel activeF activeFamily activeHistoryDf Set.univ := by
  ext z
  exact activeIntegerBounds.master_iff activeF activeFamily activeHistoryDf
    activeHistory.seed activeHistory.initial_all (activeHistory.g_derivative activeHistory.seed) z

/-- Exactly the physical interval; these two finite sides are externally hard. -/
def finalBounds : Bounds 1 where
  lower := fun _ => .finite (1/2)
  upper := fun _ => .finite 1

def finalHardEncoding : HardBoundEncoding finalBounds finalModel where
  valid := by intro i; constructor <;> simp [finalBounds]
  side := ![Sum.inl 0,Sum.inr 0]
  injective := by
    intro i j h
    fin_cases i <;> fin_cases j <;> simpa using h
  lower_cover := by
    intro i a h
    fin_cases i
    exact ⟨0,rfl⟩
  upper_cover := by
    intro i a h
    fin_cases i
    exact ⟨1,rfl⟩
  row_spec := by
    intro j
    fin_cases j
    · refine ⟨1/2,rfl,?_⟩
      intro p
      exact final_lower_identity p
    · refine ⟨1,rfl,?_⟩
      intro p
      exact final_upper_identity p

theorem final_exact_hard_region (x y : V) :
    x∈finalBounds.region ↔ (x,y)∈finalModel.linearRegion :=
  finalHardEncoding.region_iff x y

theorem final_actual_normals (v : V) :
    fiberLinearRow finalModel 0 v= -v 0 ∧ fiberLinearRow finalModel 1 v=v 0 := by
  exact ⟨finalHardEncoding.lower_normal 0 0 rfl v,
    finalHardEncoding.upper_normal 1 0 rfl v⟩

end Chapter03.OAKKT.Controls
