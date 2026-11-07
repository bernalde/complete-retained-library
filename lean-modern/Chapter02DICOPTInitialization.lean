module

public import Chapter02DICOPTDriver

@[expose] public section

/-! Full source initialization and explicit regularity assumptions. These
assumptions furnish genuine KKT/sign-convex certificates, never desired minima.
Joint sufficiency and correctness of both early returns are proved separately. -/
noncomputable section
namespace Chapter02.DICOPT
variable {n m e l r : ℕ}

def canonicalWeights {d : Data n m e l r} {x : RealVector n} {y : RealVector m}
    (k : FixedKKT d x y) : Weights k where
  obj := |k.sigma| + 1
  eq := fun i => |k.lambda i| + 1
  ineq := fun i => |k.mu i| + 1
  obj_gt := by linarith
  eq_gt := fun _ => by linarith
  ineq_gt := fun _ => by linarith

/-- Honest fixed-binary certificate availability. A CQ may justify this
hypothesis, but fixed-fiber CQ does not supply the distinct joint hypothesis. -/
def FiberRegularity (d : Data n m e l r) : Prop :=
  ∀ b : BVector m, (d.fiber (realBinary b)).Nonempty →
    ∃ x, ∃ k : FixedKKT d x (realBinary b), SignedConvex d k

/-- Availability of a FULL joint relaxed certificate with x and y box normals.
No field asserts that the supplied point is a global minimum. -/
def JointRegularity (d : Data n m e l r) : Prop :=
  d.relaxed.Nonempty → ∃ x y, ∃ k : JointKKT d x y,
    SignedConvex d k.toFixedKKT

theorem reply_exists (d : Data n m e l r) (hreg : FiberRegularity d)
    (b : BVector m) : ∃ reply : FiberReply d, reply.binary = b := by
  classical
  by_cases he : (d.fiber (realBinary b)).Nonempty
  · obtain ⟨x,k,hc⟩ := hreg b he
    let a : Anchor d := ⟨x,realBinary b,k,hc,canonicalWeights k⟩
    refine ⟨⟨b,some a,?_,?_⟩,rfl⟩
    · intro a' ha
      have : a = a' := Option.some.inj ha
      subst a'
      rfl
    · simp
  · exact ⟨⟨b,none,by simp,fun _ => he⟩,rfl⟩

structure RelaxedAnchor (d : Data n m e l r) where
  x : RealVector n
  y : RealVector m
  kkt : JointKKT d x y
  convex : SignedConvex d kkt.toFixedKKT
  weights : Weights kkt.toFixedKKT

def RelaxedAnchor.toAnchor {d : Data n m e l r} (a : RelaxedAnchor d) : Anchor d :=
  ⟨a.x,a.y,a.kkt.toFixedKKT,a.convex,a.weights⟩

/-- One initial relaxed solve/emptiness inspection. An integral reply is only
admitted with full joint KKT and signed convexity, not fixed-y KKT alone. -/
inductive Initialization (d : Data n m e l r)
  | empty (certificate : ¬ d.relaxed.Nonempty)
  | integral (a : RelaxedAnchor d) (binary : Binary a.y)
  | fractional (a : RelaxedAnchor d) (nonbinary : ¬ Binary a.y)

theorem initialization_exists (d : Data n m e l r) (hreg : JointRegularity d) :
    Nonempty (Initialization d) := by
  classical
  by_cases he : d.relaxed.Nonempty
  · obtain ⟨x,y,k,hc⟩ := hreg he
    let a : RelaxedAnchor d := ⟨x,y,k,hc,canonicalWeights k.toFixedKKT⟩
    by_cases hb : Binary y
    · exact ⟨.integral a hb⟩
    · exact ⟨.fractional a hb⟩
  · exact ⟨.empty he⟩

structure Output (n m : ℕ) where
  result : Result n m
  binarySolves : ℕ
  masterDecisions : ℕ

/-- Actual full procedure: empty or certified integral initializer returns
immediately; a fractional initializer starts the retained-history recursion.
There is exactly one initialization inspection, counted separately from these
master decisions. The fuel bound includes the terminal master inspection. -/
def procedure (d : Data n m e l r) (initial : Initialization d)
    (choose : Selector d) : Option (Output n m) :=
  match initial with
  | .empty _ => some ⟨.infeasible,0,0⟩
  | .integral a _ => some ⟨.solution (a.x,a.y),0,0⟩
  | .fractional a _ =>
      (run d choose (Fintype.card (BVector m)+1) (initialState a.toAnchor)
        (initial_invariant a.toAnchor)).map (fun out => ⟨out.1,out.2,out.2+1⟩)

theorem procedure_returns (d : Data n m e l r) (initial : Initialization d)
    (choose : Selector d) : ∃ output,
    procedure d initial choose = some output ∧
    output.binarySolves ≤ Fintype.card (BVector m) ∧
    output.masterDecisions ≤ Fintype.card (BVector m)+1 := by
  cases initial with
  | empty h => exact ⟨⟨.infeasible,0,0⟩,rfl,Nat.zero_le _,Nat.zero_le _⟩
  | integral a h => exact ⟨⟨.solution (a.x,a.y),0,0⟩,rfl,Nat.zero_le _,Nat.zero_le _⟩
  | fractional a h =>
    obtain ⟨result,k,hrun,_,hk,hd⟩ := driver_finite_return d choose a.toAnchor
    exact ⟨⟨result,k,k+1⟩,by rw [procedure,hrun]; rfl,hk,hd⟩

theorem binary_configuration_count : Fintype.card (BVector m) = 2 ^ m := by
  simp [BVector]

end Chapter02.DICOPT
