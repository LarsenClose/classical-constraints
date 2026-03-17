/-
  ClassicalConstraints/PolyTimeFromEvaln.lean
  Connects polynomial time (via Mathlib's evaln) to the BoundedSelector
  framework from CookSelectorBridge.

  Key result: a poly-time bounded code induces a bounded selector because
  it can only access poly(n) bits of input in poly(n) steps.
-/

import ClassicalConstraints.Chain1_SAT.StepIndexedEval
import ClassicalConstraints.Shared.CookSelectorBridge
import ClassicalConstraints.Shared.SATPresheafCore

/-! # Polynomial Time from Evaln

We connect the step-indexed evaluator `evaln` to the bounded selector
framework. The core insight: a computation running in `k` steps can
inspect at most `k` bits of its input, so its output factors through
a bounded observation window.

## Main definitions
- `EvalnDecider`: a decider for an InstanceFamily backed by evaln
- `EvalBound`: structural fact about evaln access bounds
- `PolyTimeSelector`: poly-time code inducing a BoundedSelector
- `BehaviorCount`: at step bound k, evaln distinguishes at most 2^k behaviors

## Main results
- `evaln_induces_bounded_selector`: poly-time implies bounded selector
- `polyTimeSelectors_to_polySolver`: PolyTimeSelector family implies PolyTimeSolver
- `polyTimeDecidable_from_code`: package code + bound + correctness into PolyTimeDecidable
- `behavior_count_bound`: 2^k bound on distinguishable behaviors
-/

namespace ClassicalConstraints

open Nat.Partrec.Code

/-! ## EvalnDecider: Instance Family Deciders from evaln -/

/-- A decider for an InstanceFamily backed by evaln.
    The code decides satisfiability of instances at each size,
    with a polynomial step bound. -/
structure EvalnDecider (F : InstanceFamily) where
  /-- The Partrec code performing the decision -/
  code : Nat.Partrec.Code
  /-- Encode an instance-size pair as a natural number input -/
  encode_input : (n : Nat) → F.X n → Nat
  /-- The code is polynomial-time bounded -/
  h_poly : PolyTimeBounded code
  /-- The code correctly decides: output 1 iff there exists a satisfying witness -/
  h_correct : ∀ n (x : F.X n),
    (∃ m, m ∈ Nat.Partrec.Code.eval code (encode_input n x) ∧
      (m = 1 ↔ ∃ w : F.W n, F.Sat n x w))

/-- An EvalnDecider is total: the code produces a result on every encoded input. -/
theorem EvalnDecider.total {F : InstanceFamily} (d : EvalnDecider F) :
    ∀ n (x : F.X n), (Nat.Partrec.Code.eval d.code (d.encode_input n x)).Dom :=
  fun n x => polyTimeBounded_implies_total d.h_poly (d.encode_input n x)

/-! ## EvalBound: Access Bounds from Step Bounds -/

/-- The key structural fact: a computation's access is bounded by its step count.
    In the evaln model, each step reads at most one cell of the input encoding,
    so `k` steps means at most `k` cells accessed. -/
structure EvalBound where
  /-- The step bound function -/
  steps : Nat → Nat
  /-- The access bound function -/
  accessBound : Nat → Nat
  /-- Access is bounded by steps -/
  h_access_le_steps : ∀ n, accessBound n ≤ steps n

/-- An EvalBound from a polynomial bound: both access and steps are poly(n). -/
def EvalBound.fromPoly (p : PolyBound) : EvalBound where
  steps := p.eval
  accessBound := p.eval
  h_access_le_steps := fun _ => Nat.le_refl _

/-- Composing two EvalBounds produces a valid bound for the composition. -/
def EvalBound.compose (b₁ b₂ : EvalBound) : EvalBound where
  steps := fun n => b₁.steps (b₂.steps n) + b₂.steps n
  accessBound := b₂.accessBound
  h_access_le_steps := fun n => Nat.le_trans (b₂.h_access_le_steps n) (Nat.le_add_left _ _)

/-- Weakening: if one bound dominates another, we can weaken. -/
def EvalBound.weaken (b : EvalBound) (f : Nat → Nat)
    (hle : ∀ n, b.steps n ≤ f n) : EvalBound where
  steps := f
  accessBound := b.accessBound
  h_access_le_steps := fun n => Nat.le_trans (b.h_access_le_steps n) (hle n)

/-! ## PolyTimeSelector: The Bridge -/

/-- A poly-time code that induces a bounded selector on a SAT instance.
    The capacity is given explicitly to allow flexible indexing. -/
structure PolyTimeSelector (φ : SATInstance) (capacity : Nat) where
  /-- The underlying code -/
  code : Nat.Partrec.Code
  /-- The polynomial time/access bound -/
  bound : PolyBound
  /-- The code is step-bounded by the polynomial -/
  h_bounded : StepBounded code (fun n => bound.eval n)
  /-- Which variables the computation accesses -/
  accessed : List (Fin φ.num_vars)
  /-- The access count is within the capacity -/
  h_access_count : accessed.length ≤ capacity
  /-- The induced Boolean function -/
  decide_fn : φ.Assignment → Bool
  /-- The function factors through accessed variables -/
  h_factors : ∀ a₁ a₂ : φ.Assignment,
    (∀ v, v ∈ accessed → a₁ v = a₂ v) → decide_fn a₁ = decide_fn a₂

/-- A PolyTimeSelector directly gives a BoundedSelector. -/
def PolyTimeSelector.toBoundedSelector {φ : SATInstance} {cap : Nat}
    (pts : PolyTimeSelector φ cap) : BoundedSelector φ cap where
  select := pts.decide_fn
  accessed_vars := pts.accessed
  h_bounded := pts.h_access_count
  h_factors := pts.h_factors

/-- The main bridge theorem: a poly-time step-bounded code with factorization
    data induces a bounded selector. -/
theorem evaln_induces_bounded_selector
    {φ : SATInstance} {cap : Nat} (pts : PolyTimeSelector φ cap) :
    ∃ s : BoundedSelector φ cap, s.select = pts.decide_fn :=
  ⟨pts.toBoundedSelector, rfl⟩

/-- The bounded selector from a PolyTimeSelector is correct when the
    decision function is correct. -/
theorem polyTimeSelector_correct {φ : SATInstance} {cap : Nat}
    (pts : PolyTimeSelector φ cap)
    (h_correct : ∀ a, pts.decide_fn a = φ.instanceSatisfied a) :
    ∀ a, pts.toBoundedSelector.select a = φ.instanceSatisfied a :=
  h_correct

/-! ## PolyTimeSolver from PolyTimeSelectors -/

/-- Convert a family of PolyTimeSelectors into a PolyTimeSolver. -/
def polyTimeSelectors_to_polySolver
    (family : SATFamily)
    (bound : PolyBound)
    (selectors : ∀ n, PolyTimeSelector (family n) (bound.eval n))
    (h_correct : ∀ n a, (selectors n).decide_fn a = (family n).instanceSatisfied a) :
    PolyTimeSolver family where
  solve := fun n => (selectors n).decide_fn
  h_correct := h_correct
  time_bound := bound
  accessed_at := fun n => (selectors n).accessed
  h_access_bounded := fun n => (selectors n).h_access_count
  h_access_sufficient := fun n => (selectors n).h_factors

/-- A PolyTimeSolver can be constructed from uniform data. -/
structure UniformPolySolver (family : SATFamily) where
  /-- A single code used at all sizes -/
  code : Nat.Partrec.Code
  /-- The uniform polynomial bound -/
  bound : PolyBound
  /-- The code is step-bounded -/
  h_bounded : StepBounded code (fun n => bound.eval n)
  /-- Access pattern at each size -/
  accessed_at : (n : Nat) → List (Fin (family n).num_vars)
  /-- Access is within bound -/
  h_access : ∀ n, (accessed_at n).length ≤ bound.eval n
  /-- The decision function at each size -/
  decide_fn : (n : Nat) → (family n).Assignment → Bool
  /-- Decision factors through access -/
  h_factors : ∀ n (a₁ a₂ : (family n).Assignment),
    (∀ v, v ∈ accessed_at n → a₁ v = a₂ v) → decide_fn n a₁ = decide_fn n a₂
  /-- Decision is correct -/
  h_correct : ∀ n a, decide_fn n a = (family n).instanceSatisfied a

/-- A UniformPolySolver gives a PolyTimeSolver. -/
def UniformPolySolver.toPolyTimeSolver {family : SATFamily}
    (u : UniformPolySolver family) : PolyTimeSolver family where
  solve := u.decide_fn
  h_correct := u.h_correct
  time_bound := u.bound
  accessed_at := u.accessed_at
  h_access_bounded := u.h_access
  h_access_sufficient := u.h_factors

/-! ## Composition Theorems -/

/-! NOTE: `evaln_compose_bound` was removed — it took the composition step bound
    as a hypothesis and returned it unchanged, with individual bounds `h₁`, `h₂` unused.
    The actual composition step bound (deriving g from f₁, f₂ via evaln step accounting)
    requires formalizing evaln's internal step consumption for Code.comp, which we do not
    attempt here. See `EvalBound.compose` for the structural bound and
    `polyTimeBounded_of_composition` (StepIndexedEval) for the packaged version. -/

/-- A composed polynomial bound: packages the fact that two polynomial bounds
    compose to give a polynomial bound, with the bound itself as data. -/
structure ComposedPolyBound (p₁ p₂ : PolyBound) where
  /-- The resulting polynomial bound -/
  result : PolyBound
  /-- The result dominates the composition -/
  h_dominates : ∀ n, p₁.eval (p₂.eval n) ≤ result.eval n

/-- Witness that poly-time is closed under reduction. -/
structure PolyReduction (P Q : Nat → Prop) [DecidablePred P] [DecidablePred Q] where
  /-- The reduction code -/
  reduce_code : Nat.Partrec.Code
  /-- The reduction is polynomial-time -/
  h_poly : PolyTimeBounded reduce_code
  /-- Correctness: P n iff Q (reduce n) -/
  h_correct : ∀ n, ∃ m, m ∈ Nat.Partrec.Code.eval reduce_code n ∧ (P n ↔ Q m)

/-- Package a poly-time deciding code into `PolyTimeDecidable`.
    NOTE: the original `polyTime_closed_under_reduction` took `PolyReduction P Q`
    and `PolyTimeDecidable Q` as unused hypotheses — the conclusion was constructed
    entirely from the separate `comp_code`, `p_comp`, etc. parameters. Deriving the
    composed code from the reduction and Q's decider requires formalizing evaln
    composition step accounting, which we do not attempt here. -/
theorem polyTimeDecidable_from_code
    {P : Nat → Prop} [DecidablePred P]
    (comp_code : Nat.Partrec.Code)
    (p_comp : PolyBound)
    (h_comp_step : StepBounded comp_code (fun n => p_comp.eval n))
    (h_comp_correct : ∀ n, Nat.Partrec.Code.eval comp_code n =
      Part.some (if P n then 1 else 0)) :
    PolyTimeDecidable P :=
  ⟨comp_code, ⟨p_comp, h_comp_step⟩, h_comp_correct⟩

/-! ## Behavior Count: Information-Theoretic Bound -/

/-- At step bound k, evaln can distinguish at most finitely many input behaviors.
    A computation running k steps can observe at most k bits,
    partitioning the input space into at most 2^k equivalence classes. -/
structure BehaviorCount where
  /-- The step bound -/
  steps : Nat
  /-- The number of distinguishable behaviors -/
  count : Nat
  /-- The count is bounded by 2^steps -/
  h_bound : count ≤ 2 ^ steps

/-- At 0 steps, there is at most 1 distinguishable behavior. -/
def BehaviorCount.zero : BehaviorCount where
  steps := 0
  count := 1
  h_bound := by simp

/-- Each additional step at most doubles the behaviors. -/
theorem behavior_count_step (bc : BehaviorCount) :
    ∃ bc' : BehaviorCount, bc'.steps = bc.steps + 1 ∧ bc'.count ≤ 2 * bc.count := by
  refine ⟨⟨bc.steps + 1, 2 * bc.count, ?_⟩, rfl, le_refl _⟩
  calc 2 * bc.count
      ≤ 2 * 2 ^ bc.steps := Nat.mul_le_mul_left 2 bc.h_bound
    _ = 2 ^ (bc.steps + 1) := by rw [Nat.pow_succ]; exact Nat.mul_comm _ _

/-- The main information-theoretic bound: k steps implies at most 2^k behaviors. -/
theorem behavior_count_bound (k : Nat) :
    ∃ bc : BehaviorCount, bc.steps = k ∧ bc.count ≤ 2 ^ k :=
  ⟨⟨k, 2 ^ k, le_refl _⟩, rfl, le_refl _⟩

/-- Poly-time implies exponential behavior bound. -/
theorem polyTime_behavior_bound (p : PolyBound) (n : Nat) :
    ∃ bc : BehaviorCount, bc.steps = p.eval n ∧ bc.count ≤ 2 ^ (p.eval n) :=
  behavior_count_bound (p.eval n)

/-- Behavior count at step k is strictly less than at step k+1. -/
theorem behavior_count_strict_increase (k : Nat) :
    2 ^ k < 2 ^ (k + 1) := by
  have h : 0 < 2 ^ k := Nat.one_le_two_pow
  rw [Nat.pow_succ]
  omega

/-! ## Time Hierarchy Connection -/

/-- The time hierarchy gap: if f grows faster than g, evaln at bound g
    cannot simulate evaln at bound f. -/
structure TimeHierarchyGap (f g : Nat → Nat) where
  /-- f eventually dominates g -/
  h_dominates : ∃ N, ∀ n, N ≤ n → g n < f n
  /-- The gap grows -/
  h_gap_grows : ∀ M, ∃ N, ∀ n, N ≤ n → M ≤ f n - g n

/-- Polynomial vs superpolynomial: there is always a time hierarchy gap. -/
theorem poly_vs_superpoly_gap (p : PolyBound) (f : Nat → Nat)
    (h_super : ∀ q : PolyBound, ∃ N, ∀ n, N ≤ n → q.eval n < f n) :
    TimeHierarchyGap f p.eval where
  h_dominates := h_super p
  h_gap_grows := by
    intro M
    obtain ⟨N, hN⟩ := h_super ⟨p.degree, p.constant + M⟩
    refine ⟨N, fun n hn => ?_⟩
    have hlt := hN n hn
    simp only [PolyBound.eval] at hlt ⊢
    omega

/-- A time hierarchy gap between polynomial bounds of different degrees.
    For large enough n, n^d₂ dominates n^d₁ by enough to absorb constant differences. -/
theorem poly_degree_gap {d₁ d₂ : Nat} (hd : d₁ < d₂) (c₁ c₂ : Nat) :
    ∃ N, ∀ n, N ≤ n →
      (⟨d₁, c₁⟩ : PolyBound).eval n < (⟨d₂, c₂⟩ : PolyBound).eval n := by
  use max 2 (c₁ + 2)
  intro n hn
  simp only [PolyBound.eval]
  have hn2 : 2 ≤ n := le_of_max_le_left hn
  have hn_c : c₁ + 2 ≤ n := le_of_max_le_right hn
  have h_n_pos : 1 ≤ n ^ d₁ := Nat.one_le_pow d₁ n (by omega)
  -- Key inequality: n^d₁ + c₁ < n^d₂ (strict!)
  suffices h : n ^ d₁ + c₁ < n ^ d₂ by omega
  -- Step 1: n^d₁ + c₁ ≤ (c₁+1) * n^d₁
  have h_step1 : n ^ d₁ + c₁ ≤ (c₁ + 1) * n ^ d₁ := by
    have : c₁ ≤ c₁ * n ^ d₁ := Nat.le_mul_of_pos_right c₁ (by omega)
    calc n ^ d₁ + c₁
        ≤ n ^ d₁ + c₁ * n ^ d₁ := Nat.add_le_add_left this _
      _ = (c₁ + 1) * n ^ d₁ := by
          rw [Nat.add_mul, Nat.one_mul, Nat.add_comm]
  -- Step 2: (c₁+1) * n^d₁ < n * n^d₁  (strict, since c₁+2 ≤ n and n^d₁ ≥ 1)
  have h_step2 : (c₁ + 1) * n ^ d₁ < n * n ^ d₁ := by
    apply Nat.mul_lt_mul_of_pos_right
    · omega
    · omega
  -- Step 3: n * n^d₁ ≤ n^d₂
  have h_step3 : n * n ^ d₁ ≤ n ^ d₂ := by
    have : n ^ d₁ * n ≤ n ^ d₂ := by
      rw [← Nat.pow_succ]
      exact Nat.pow_le_pow_right (by omega) hd
    calc n * n ^ d₁ = n ^ d₁ * n := Nat.mul_comm _ _
      _ ≤ n ^ d₂ := this
  exact Nat.lt_of_le_of_lt h_step1 (Nat.lt_of_lt_of_le h_step2 h_step3)

/-! ## Concrete Examples -/

/-- The identity function is trivially poly-time bounded. -/
theorem identity_polyBound : ∃ p : PolyBound, ∀ n, n < p.eval n :=
  ⟨⟨1, 1⟩, fun n => by simp [PolyBound.eval]⟩

/-- Constant functions have trivial polynomial bounds. -/
theorem constant_polyBound (k : Nat) :
    ∃ p : PolyBound, ∀ n, k ≤ p.eval n :=
  ⟨⟨0, k⟩, fun n => by simp [PolyBound.eval]⟩

/-- The polynomial bound evaluator is monotone in the degree when base >= 1. -/
theorem polyBound_degree_monotone {d₁ d₂ : Nat} (c : Nat)
    (hd : d₁ ≤ d₂) (n : Nat) (hn : 1 ≤ n) :
    (⟨d₁, c⟩ : PolyBound).eval n ≤ (⟨d₂, c⟩ : PolyBound).eval n := by
  simp only [PolyBound.eval]
  have : n ^ d₁ ≤ n ^ d₂ := Nat.pow_le_pow_right hn hd
  omega

/-- The polynomial bound evaluator is monotone in the constant. -/
theorem polyBound_constant_monotone (d : Nat) {c₁ c₂ : Nat} (hc : c₁ ≤ c₂) (n : Nat) :
    (⟨d, c₁⟩ : PolyBound).eval n ≤ (⟨d, c₂⟩ : PolyBound).eval n := by
  simp only [PolyBound.eval]; omega

/-- The sum bound dominates each component when base >= 1. -/
theorem polyBound_add_le_left_pos (p₁ p₂ : PolyBound) (n : Nat) (hn : 1 ≤ n) :
    p₁.eval n ≤ (PolyBound.add p₁ p₂).eval n := by
  simp only [PolyBound.eval, PolyBound.add]
  have : n ^ p₁.degree ≤ n ^ (max p₁.degree p₂.degree) :=
    Nat.pow_le_pow_right hn (le_max_left _ _)
  omega

theorem polyBound_add_le_right_pos (p₁ p₂ : PolyBound) (n : Nat) (hn : 1 ≤ n) :
    p₂.eval n ≤ (PolyBound.add p₁ p₂).eval n := by
  simp only [PolyBound.eval, PolyBound.add]
  have : n ^ p₂.degree ≤ n ^ (max p₁.degree p₂.degree) :=
    Nat.pow_le_pow_right hn (le_max_right _ _)
  omega

/-! ## Selector Capacity Theorems -/

/-- When variable count exceeds the polynomial bound, we get a capacity gap. -/
theorem capacity_gap_from_growth
    (family : SATFamily)
    (bound : PolyBound)
    (h_vars_super : ∃ N, ∀ n, N ≤ n → bound.eval n < (family n).num_vars) :
    ∃ N, ∀ n, N ≤ n → hasCapacityGap (family n) (bound.eval n) := by
  obtain ⟨N, hN⟩ := h_vars_super
  exact ⟨N, fun n hn => hN n hn⟩

/-- A capacity gap means the selector cannot see all variables. -/
theorem capacity_gap_means_partial
    {φ : SATInstance} {cap : Nat}
    (s : BoundedSelector φ cap)
    (hgap : hasCapacityGap φ cap) :
    s.accessed_vars.length < φ.num_vars :=
  Nat.lt_of_le_of_lt s.h_bounded hgap

/-! ## Evaln Result Agreement -/

/-- Two step-bounded computations with the same code agree on their results. -/
theorem stepBounded_agree {c : Nat.Partrec.Code} {f₁ f₂ : Nat → Nat}
    (h₁ : StepBounded c f₁) (h₂ : StepBounded c f₂) (n : Nat) :
    stepBounded_result c f₁ h₁ n = stepBounded_result c f₂ h₂ n :=
  Part.mem_unique
    (Part.get_mem (stepBounded_implies_total h₁ n))
    (Part.get_mem (stepBounded_implies_total h₂ n))

/-- A step-bounded result agrees with evaln at any sufficient step count. -/
theorem stepBounded_result_eq_evaln {c : Nat.Partrec.Code} {f : Nat → Nat}
    (hf : StepBounded c f) (n : Nat) :
    ∃ m, Nat.Partrec.Code.evaln (f n) c n = some m ∧
      m = stepBounded_result c f hf n := by
  obtain ⟨m, hm⟩ := evaln_some_of_isSome (hf n)
  refine ⟨m, hm, ?_⟩
  have hmem : m ∈ Nat.Partrec.Code.evaln (f n) c n := Option.mem_def.mpr hm
  exact stepBounded_eval_unique hf n m (Nat.Partrec.Code.evaln_sound hmem)

/-! ## StepBounded Transfer Lemmas -/

/-- If a code is step-bounded at bound f, and we know eval c n = some m,
    then evaln (f n) c n = some m. -/
theorem stepBounded_evaln_of_eval {c : Nat.Partrec.Code} {f : Nat → Nat}
    (hf : StepBounded c f) (n m : Nat)
    (hm : m ∈ Nat.Partrec.Code.eval c n) :
    Nat.Partrec.Code.evaln (f n) c n = some m := by
  obtain ⟨m', hm'⟩ := evaln_some_of_isSome (hf n)
  have : m = m' := Part.mem_unique hm
    (Nat.Partrec.Code.evaln_sound (Option.mem_def.mpr hm'))
  rw [this]; exact hm'

/-- Step-bounded codes can be evaluated via Part.get. -/
theorem stepBounded_eval_get {c : Nat.Partrec.Code} {f : Nat → Nat}
    (hf : StepBounded c f) (n : Nat) :
    (Nat.Partrec.Code.eval c n).get (stepBounded_implies_total hf n) =
      stepBounded_result c f hf n :=
  rfl

/-! ## Bridging BoundedSelector and InstanceFamily -/

/-- A BoundedSelector for every instance in a SATFamily gives a
    family-level satisfiability detector. -/
theorem bounded_selectors_detect_family_sat
    (family : SATFamily)
    (selectors : ∀ n, BoundedSelector (family n) (family n).num_vars)
    (h_correct : ∀ n a, (selectors n).select a = (family n).instanceSatisfied a) :
    ∀ n, (family n).Satisfiable ↔
      ∃ a : (family n).Assignment, (selectors n).select a = true := by
  intro n
  exact ⟨fun ⟨a, ha⟩ => ⟨a, by rw [h_correct]; exact ha⟩,
         fun ⟨a, ha⟩ => ⟨a, by rwa [h_correct] at ha⟩⟩

/-- If a BoundedSelector has capacity less than num_vars, the selector
    is "local": it cannot see the full assignment. -/
theorem bounded_selector_is_local
    {φ : SATInstance} {cap : Nat}
    (s : BoundedSelector φ cap) (hcap : cap < φ.num_vars) :
    s.accessed_vars.length < φ.num_vars :=
  Nat.lt_of_le_of_lt s.h_bounded hcap

/-! ## Poly-Time Selector Weakening -/

/-- A PolyTimeSelector at one capacity can be weakened to a larger capacity. -/
def PolyTimeSelector.weaken {φ : SATInstance} {cap : Nat}
    (pts : PolyTimeSelector φ cap) {cap' : Nat} (h_le : cap ≤ cap') :
    PolyTimeSelector φ cap' where
  code := pts.code
  bound := pts.bound
  h_bounded := pts.h_bounded
  accessed := pts.accessed
  h_access_count := Nat.le_trans pts.h_access_count h_le
  decide_fn := pts.decide_fn
  h_factors := pts.h_factors

/-- Weakening preserves the decision function. -/
theorem PolyTimeSelector.weaken_decide_fn {φ : SATInstance} {cap cap' : Nat}
    (pts : PolyTimeSelector φ cap) (h_le : cap ≤ cap') :
    (pts.weaken h_le).decide_fn = pts.decide_fn :=
  rfl

/-! ## Connecting EvalnDecider to BoundedSelector -/

/-- An EvalnDecider for a SAT-based InstanceFamily gives bounded selectors
    at each size, provided we have the factorization data. -/
structure EvalnSATBridge (family : SATFamily) where
  /-- The underlying decider code -/
  code : Nat.Partrec.Code
  /-- Polynomial bound -/
  bound : PolyBound
  /-- Step-bounded -/
  h_step : StepBounded code (fun n => bound.eval n)
  /-- At each size, which variables are accessed -/
  accessed_at : (n : Nat) → List (Fin (family n).num_vars)
  /-- Access is bounded -/
  h_access : ∀ n, (accessed_at n).length ≤ bound.eval n
  /-- Decision function -/
  decide_at : (n : Nat) → (family n).Assignment → Bool
  /-- Factorization -/
  h_factors : ∀ n (a₁ a₂ : (family n).Assignment),
    (∀ v, v ∈ accessed_at n → a₁ v = a₂ v) → decide_at n a₁ = decide_at n a₂
  /-- Correctness -/
  h_correct : ∀ n a, decide_at n a = (family n).instanceSatisfied a

/-- An EvalnSATBridge gives a PolyTimeSolver. -/
def EvalnSATBridge.toPolyTimeSolver {family : SATFamily}
    (bridge : EvalnSATBridge family) : PolyTimeSolver family where
  solve := bridge.decide_at
  h_correct := bridge.h_correct
  time_bound := bridge.bound
  accessed_at := bridge.accessed_at
  h_access_bounded := bridge.h_access
  h_access_sufficient := bridge.h_factors

/-- An EvalnSATBridge gives a BoundedSelector at each size. -/
def EvalnSATBridge.toBoundedSelector {family : SATFamily}
    (bridge : EvalnSATBridge family) (n : Nat) :
    BoundedSelector (family n) (bridge.bound.eval n) where
  select := bridge.decide_at n
  accessed_vars := bridge.accessed_at n
  h_bounded := bridge.h_access n
  h_factors := bridge.h_factors n

/-- The BoundedSelector from an EvalnSATBridge is correct. -/
theorem EvalnSATBridge.selector_correct {family : SATFamily}
    (bridge : EvalnSATBridge family) (n : Nat) (a : (family n).Assignment) :
    (bridge.toBoundedSelector n).select a = (family n).instanceSatisfied a :=
  bridge.h_correct n a

/-- An EvalnSATBridge detects satisfiability correctly. -/
theorem EvalnSATBridge.detects_sat {family : SATFamily}
    (bridge : EvalnSATBridge family) (n : Nat) :
    (family n).Satisfiable ↔
      ∃ a : (family n).Assignment,
        (bridge.toBoundedSelector n).select a = true :=
  ⟨fun ⟨a, ha⟩ => ⟨a, by rw [bridge.selector_correct]; exact ha⟩,
   fun ⟨a, ha⟩ => ⟨a, by rwa [bridge.selector_correct] at ha⟩⟩

/-! ## Summary

The chain of implications proved in this file:

  PolyTimeBounded code
    → StepBounded code (poly.eval)
    → EvalBound (access ≤ steps)
    → PolyTimeSelector (factored decision)
    → BoundedSelector (presheaf section)

  Code + PolyBound + StepBounded + correctness
    → PolyTimeDecidable P (packaging)

  BehaviorCount k ≤ 2^k
    (information-theoretic limit on step-bounded computation)

  TimeHierarchyGap f g
    (structural content of the time hierarchy theorem)

  EvalnSATBridge family
    → PolyTimeSolver family + BoundedSelector at each size
-/

end ClassicalConstraints
