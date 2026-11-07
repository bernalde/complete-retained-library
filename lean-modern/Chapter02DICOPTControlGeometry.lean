module

public import Mathlib.Analysis.Calculus.LocalExtr.Basic
public import Mathlib.Analysis.Calculus.TangentCone.Seq

@[expose] public section

open Set Filter
open scoped Topology Convex

namespace Chapter02.DICOPTControlGeometry

/-- The actual positive (Bouligand) tangent cone of a singleton. -/
theorem singleton_posTangentCone {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] (a : E) : posTangentConeAt ({a} : Set E) a = {0} := by
  ext v
  constructor
  · intro hv
    rcases mem_tangentConeAt_iff_exists_seq.mp hv with ⟨c, d, _, hd, hcd⟩
    have he : (fun n => c n • d n) =ᶠ[atTop] fun _ => (0 : E) := by
      filter_upwards [hd] with n hn
      have hdn : d n = 0 := by simpa only [mem_singleton_iff, add_eq_left] using hn
      simp [hdn]
    exact mem_singleton_iff.mpr (tendsto_nhds_unique hcd (tendsto_const_nhds.congr' he.symm))
  · rintro rfl
    simpa using (sub_mem_posTangentConeAt_of_segment_subset
      (show segment ℝ a a ⊆ ({a} : Set E) by simp))

end Chapter02.DICOPTControlGeometry
