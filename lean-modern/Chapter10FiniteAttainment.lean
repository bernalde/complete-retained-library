module

public import Chapter10FixedBits
public import Chapter09Slots

@[expose] public section

/-! Reuse of accepted finite attainment, with domain membership and actual
nonemptiness retained. No executable optimizer or physical oracle is supplied. -/
noncomputable section
namespace Chapter10.Algebra

theorem finite_domain_attainment {α : Type*} [Fintype α]
    (D : Set α) (hD : D.Nonempty) (f : α → ℝ) : ∃ x, IsMinOn D f x := by
  classical
  let s := Finset.univ.filter (fun x => x ∈ D)
  have hs : s.Nonempty := by
    obtain ⟨x, hx⟩ := hD
    exact ⟨x, Finset.mem_filter.mpr ⟨Finset.mem_univ x, hx⟩⟩
  obtain ⟨x, hx, hm⟩ := Chapter09.Source.maxOn_attained s hs (fun x => -f x)
  refine ⟨x, (Finset.mem_filter.mp hx).2, ?_⟩
  intro y hy
  have h := Chapter09.Source.le_maxOn s hs (fun x => -f x) y
    (Finset.mem_filter.mpr ⟨Finset.mem_univ y, hy⟩)
  rw [← hm] at h
  exact neg_le_neg_iff.mp h

theorem real_binary_domain_attainment {ι : Type*} [Fintype ι]
    (D : Set (ι → ℝ)) (hbin : ∀ x ∈ D, Binary x) (hD : D.Nonempty)
    (f : (ι → ℝ) → ℝ) : ∃ x, IsMinOn D f x := by
  classical
  let decode : (ι → Bool) → ι → ℝ := fun b i => Chapter10.bit (b i)
  have he : ∀ x ∈ D, decode (encode x) = x := by
    intro x hx
    funext i
    exact bit_encode (hbin x hx) i
  let B : Set (ι → Bool) := {b | decode b ∈ D}
  have hB : B.Nonempty := by
    obtain ⟨x, hx⟩ := hD
    exact ⟨encode x, by change decode (encode x) ∈ D; rw [he x hx]; exact hx⟩
  obtain ⟨b, hb, hm⟩ := finite_domain_attainment B hB (fun b => f (decode b))
  refine ⟨decode b, hb, ?_⟩
  intro y hy
  have hmem : encode y ∈ B := by change decode (encode y) ∈ D; rw [he y hy]; exact hy
  simpa only [he y hy] using hm (encode y) hmem

theorem fixed_domain_attainment {U F : Type*} [Fintype U] [Fintype F]
    (a : F → ℝ) (hD : (fixedDomain (U := U) a).Nonempty)
    (f : (U ⊕ F → ℝ) → ℝ) : ∃ x, IsMinOn (fixedDomain a) f x := by
  exact real_binary_domain_attainment (fixedDomain a) (fun _ hx => hx.1) hD f

theorem consistent_fixed_domain_nonempty {U F : Type*} (a : F → ℝ) (ha : Binary a) :
    (fixedDomain (U := U) a).Nonempty :=
  ⟨extend a (fun _ => 0), extend_mem_fixedDomain a ha _ (fun _ => Or.inl rfl)⟩

end Chapter10.Algebra

#print axioms Chapter10.Algebra.finite_domain_attainment
#print axioms Chapter10.Algebra.real_binary_domain_attainment
