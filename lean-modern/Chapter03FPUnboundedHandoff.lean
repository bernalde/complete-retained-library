module

public import Chapter03FPUnboundedReturns

@[expose] public section

noncomputable section
open Chapter02 Chapter03.FP
namespace Chapter03.FPUnbounded
variable {n m l : ℕ}

theorem append_has_incumbent {s : State n m} {e : Event n m}
    (hi : s.incumbent ≠ none) : (append s e).incumbent ≠ none := by
  cases he : e.success with
  | none => simpa [append,he] using hi
  | some pu => simp [append,he]

/-- At zero tolerance every admissible uncapped continuation after success
exhausts every finite fuel. This follows from the actual retained incumbent,
not merely from one favorable repeated trace. -/
theorem zero_postsuccess_run_none (d : Data n m l) (h : Analytic d)
    (hd : d.delta = 0) (choose : Selector d none) (fuel : ℕ)
    (s : State n m) (hs : Invariant d s) (hi : s.incumbent ≠ none) :
    run d choose fuel s = none := by
  induction fuel generalizing s with
  | zero => rfl
  | succ fuel ih =>
    cases hc : choose s with
    | stop reason ht =>
      obtain ⟨u,hu⟩ := Option.ne_none_iff_exists'.mp hi
      exact False.elim (stop_without_cap d ht (zero_incumbent_only_cap d h hd hs hu ht))
    | next e he =>
      obtain ⟨z,hz,_,hr⟩ := he
      have hn := ih (append s e) (append_invariant d h hs hz.1 hr) (append_has_incumbent hi)
      simp [run,hc,hn]

theorem reachable_handoff_embedding (d : Data n m l) (h : Analytic d)
    {cap : Option ℕ} {seed : Point n m} (hseed : seed ∈ d.relaxation)
    {k q : ℕ} {s : State n m} (hc : Chain d cap (initialState seed) k q s) :
    (∀ p ∈ d.original, belowIncumbent d s p → (p,d.f p) ∈ handoff d s) ∧
    (∀ u, s.incumbent = some u → (u,d.f u) ∈ handoff d s) := by
  have hs := chain_invariant d h (initial_invariant d hseed) hc
  exact ⟨fun _ hp hb => handoff_contains_below d h hs hp hb,
    fun _ hu => handoff_contains_incumbent d h hs hu⟩

end Chapter03.FPUnbounded
