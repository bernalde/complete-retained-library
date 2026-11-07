module

public import AppendixAAssignment

@[expose] public section

/-! Supporting logical restriction and cap transport. These statements do not
delete physical hardware or identify any historical graph generator. They earn
no separate source-claim credit. This draft requires the author's pinned build. -/
namespace AppendixATheory

theorem BranchModel.logical_restrict {n m m' k : ℕ}
    {E : Finset (Fin n × Fin n)}
    {L : Finset (Fin m × Fin m)} {L' : Finset (Fin m' × Fin m')}
    {F : Fin m → Finset (Fin n)} (h : BranchModel E L k F)
    (f : Fin m' → Fin m) (hf : Function.Injective f)
    (hL : ∀ j l, AppendixA.adjacent L' j l →
      AppendixA.adjacent L (f j) (f l)) :
    BranchModel E L' k (F ∘ f) := by
  refine ⟨fun j => h.1 (f j), ?_, ?_⟩
  · intro j l hne
    exact h.2.1 (f j) (f l) (fun he => hne (hf he))
  · intro j l hjl
    exact h.2.2 (f j) (f l) (hL j l hjl)

theorem BranchModel.cap_mono {n m k k' : ℕ}
    {E : Finset (Fin n × Fin n)} {L : Finset (Fin m × Fin m)}
    {F : Fin m → Finset (Fin n)} (h : BranchModel E L k F)
    (hk : k ≤ k') : BranchModel E L k' F := by
  exact ⟨fun j => ⟨(h.1 j).1, (h.1 j).2.1.trans hk, (h.1 j).2.2⟩,
    h.2.1, h.2.2⟩

theorem BranchModel.exists_restricted_embedding {n m m' k : ℕ}
    {E : Finset (Fin n × Fin n)}
    {L : Finset (Fin m × Fin m)} {L' : Finset (Fin m' × Fin m')}
    {F : Fin m → Finset (Fin n)} (h : BranchModel E L k F)
    (f : Fin m' → Fin m) (hf : Function.Injective f)
    (hL : ∀ j l, AppendixA.adjacent L' j l →
      AppendixA.adjacent L (f j) (f l)) :
    ∃ A : Alpha n m', fiber A = F ∘ f ∧ Embedding E L' k A := by
  exact (branchModel_alpha_projection E L' k (F ∘ f)).mpr
    (h.logical_restrict f hf hL)

theorem Embedding.exists_restricted {n m m' k : ℕ}
    {E : Finset (Fin n × Fin n)}
    {L : Finset (Fin m × Fin m)} {L' : Finset (Fin m' × Fin m')}
    {A : Alpha n m} (h : Embedding E L k A)
    (f : Fin m' → Fin m) (hf : Function.Injective f)
    (hL : ∀ j l, AppendixA.adjacent L' j l →
      AppendixA.adjacent L (f j) (f l)) :
    ∃ B : Alpha n m', fiber B = fiber A ∘ f ∧ Embedding E L' k B := by
  exact ((embedding_iff_branchModel E L k A).mp h).exists_restricted_embedding
    f hf hL

end AppendixATheory
