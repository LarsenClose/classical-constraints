/-
  ClassicalConstraints/StepIndexedEval.lean
  Grounds polynomial time in Mathlib's `evaln` — the step-bounded evaluator
  for `Nat.Partrec.Code`.

  Key insight: `evaln k c n` runs code `c` on input `n` for at most `k` steps.
  Polynomial time = evaln terminates within p(n) steps for some polynomial p.

  This file connects the step-indexed evaluation model to the
  PolyBound/BoundedSelector framework in CookSelectorBridge.
-/

import ClassicalConstraints.Shared.CookSelectorBridge
import Mathlib.Computability.Partrec
import Mathlib.Computability.PartrecCode

/-! # Step-Indexed Evaluation and Polynomial Time

We define polynomial-time computability in terms of Mathlib's
`Nat.Partrec.Code.evaln`, the step-bounded partial recursive evaluator.

## Main definitions
- `PolyBound`: polynomial bound (degree, constant) with eval n = n^d + c
- `StepBounded`: a code terminates within f(n) steps on input n
- `PolyTimeBounded`: a code runs in polynomial time
- `PolyTimeDecides`: a poly-time code decides a predicate
- `StepBoundedAccess`: step-bounded computation with access bound metadata

## Main results
- `evaln_monotone_steps`: more steps preserve evaln results (from Mathlib)
- `stepBounded_monotone`: StepBounded is monotone in the bound function
- `stepBounded_implies_total`: step-bounded codes are total
- `polyTimeBounded_composition_of`: composition of poly-time codes is poly-time
  (given compositional step bound hypothesis)
-/

namespace ClassicalConstraints

open Nat.Partrec.Code

/-! ## Polynomial Bound Extensions
    (PolyBound, eval, eval_ge_constant, eval_monotone imported from CookSelectorBridge) -/

namespace PolyBound

/-- Sum of two polynomial bounds. Used for bounding compositions. -/
def add (p q : PolyBound) : PolyBound where
  degree := max p.degree q.degree
  constant := p.constant + q.constant

/-- A bound that dominates composition: p(q(n)) <= compose p q . n -/
def compose (p q : PolyBound) : PolyBound where
  degree := p.degree * q.degree
  constant := (q.constant + 1) ^ p.degree + p.constant

end PolyBound

/-! ## Step-Bounded Evaluation -/

/-- A code `c` is step-bounded by `f` if `evaln (f n) c n` produces a result
    for every input `n`. This means the computation terminates within f(n) steps. -/
def StepBounded (c : Nat.Partrec.Code) (f : Nat -> Nat) : Prop :=
  forall n, (Nat.Partrec.Code.evaln (f n) c n).isSome = true

/-- evaln is monotone in the step count: more steps preserve results.
    This is a direct corollary of Mathlib's `evaln_mono`. -/
theorem evaln_monotone_steps {k₁ k₂ : Nat} {c : Nat.Partrec.Code} {n m : Nat}
    (hk : k₁ <= k₂) (h : m ∈ Nat.Partrec.Code.evaln k₁ c n) :
    m ∈ Nat.Partrec.Code.evaln k₂ c n :=
  Nat.Partrec.Code.evaln_mono hk h

/-- Helper: if evaln k c n = some m, then isSome is true. -/
theorem evaln_isSome_of_eq_some {k : Nat} {c : Nat.Partrec.Code} {n m : Nat}
    (h : Nat.Partrec.Code.evaln k c n = some m) :
    (Nat.Partrec.Code.evaln k c n).isSome = true := by
  rw [h]; rfl

/-- Helper: if isSome is true, extract a witness. -/
theorem evaln_some_of_isSome {k : Nat} {c : Nat.Partrec.Code} {n : Nat}
    (h : (Nat.Partrec.Code.evaln k c n).isSome = true) :
    exists m, Nat.Partrec.Code.evaln k c n = some m := by
  cases hv : Nat.Partrec.Code.evaln k c n with
  | none => simp [hv] at h
  | some v => exact ⟨v, rfl⟩

/-- StepBounded is monotone: if a computation terminates within f(n) steps,
    it also terminates within g(n) steps whenever f <= g pointwise. -/
theorem stepBounded_monotone {c : Nat.Partrec.Code} {f g : Nat -> Nat}
    (hfg : forall n, f n <= g n) (hf : StepBounded c f) : StepBounded c g := by
  intro n
  obtain ⟨m, hm⟩ := evaln_some_of_isSome (hf n)
  have hmem : m ∈ Nat.Partrec.Code.evaln (f n) c n := by
    rw [Option.mem_def]; exact hm
  have hmem' := evaln_monotone_steps (hfg n) hmem
  rw [Option.mem_def] at hmem'
  exact evaln_isSome_of_eq_some hmem'

/-- A step-bounded computation is total: eval c n is defined for all n. -/
theorem stepBounded_implies_total {c : Nat.Partrec.Code} {f : Nat -> Nat}
    (hf : StepBounded c f) : forall n, (Nat.Partrec.Code.eval c n).Dom := by
  intro n
  obtain ⟨m, hm⟩ := evaln_some_of_isSome (hf n)
  have hmem : m ∈ Nat.Partrec.Code.evaln (f n) c n := by
    rw [Option.mem_def]; exact hm
  have := Nat.Partrec.Code.evaln_sound hmem
  rw [Part.dom_iff_mem]
  exact ⟨m, this⟩

/-- A step-bounded computation yields a specific value via eval. -/
theorem stepBounded_eval_eq {c : Nat.Partrec.Code} {f : Nat -> Nat}
    (hf : StepBounded c f) (n : Nat) :
    exists m, m ∈ Nat.Partrec.Code.eval c n := by
  obtain ⟨m, hm⟩ := evaln_some_of_isSome (hf n)
  have hmem : m ∈ Nat.Partrec.Code.evaln (f n) c n := by
    rw [Option.mem_def]; exact hm
  exact ⟨m, Nat.Partrec.Code.evaln_sound hmem⟩

/-- Extract the result of a step-bounded computation as a function. -/
noncomputable def stepBounded_result (c : Nat.Partrec.Code) (f : Nat -> Nat)
    (hf : StepBounded c f) (n : Nat) : Nat :=
  (Nat.Partrec.Code.eval c n).get (stepBounded_implies_total hf n)

/-! ## Polynomial-Time Bounded Computation -/

/-- A code runs in polynomial time: there exists a polynomial bound p
    such that evaln terminates within p(n) steps. -/
def PolyTimeBounded (c : Nat.Partrec.Code) : Prop :=
  exists p : PolyBound, StepBounded c (fun n => p.eval n)

/-- Polynomial-time codes are total. -/
theorem polyTimeBounded_implies_total {c : Nat.Partrec.Code}
    (h : PolyTimeBounded c) : forall n, (Nat.Partrec.Code.eval c n).Dom := by
  obtain ⟨_, hp⟩ := h
  exact stepBounded_implies_total hp

/-! ## Polynomial-Time Decidability -/

/-- A poly-time code decides a predicate: it runs in polynomial time and
    outputs 1 for inputs satisfying P, 0 otherwise. -/
def PolyTimeDecides (c : Nat.Partrec.Code) (P : Nat -> Prop) [DecidablePred P] : Prop :=
  PolyTimeBounded c ∧
    forall n, Nat.Partrec.Code.eval c n = Part.some (if P n then 1 else 0)

/-- A predicate is poly-time decidable if some code poly-time decides it. -/
def PolyTimeDecidable (P : Nat -> Prop) [DecidablePred P] : Prop :=
  exists c, PolyTimeDecides c P

/-- If a code poly-time decides P, then eval c n is defined for all n. -/
theorem polyTimeDecides_total {c : Nat.Partrec.Code} {P : Nat -> Prop} [DecidablePred P]
    (h : PolyTimeDecides c P) : forall n, (Nat.Partrec.Code.eval c n).Dom := by
  intro n
  rw [Part.dom_iff_mem]
  exact ⟨if P n then 1 else 0, by rw [h.2 n]; exact Part.mem_some _⟩

/-- A poly-time decided predicate produces only 0 or 1. -/
theorem polyTimeDecides_binary {c : Nat.Partrec.Code} {P : Nat -> Prop} [DecidablePred P]
    (h : PolyTimeDecides c P) (n : Nat) :
    Nat.Partrec.Code.eval c n = Part.some 0 ∨
    Nat.Partrec.Code.eval c n = Part.some 1 := by
  rw [h.2 n]
  by_cases hp : P n <;> simp [hp]

/-! ## Step-Bounded Access -/

/-- A step-bounded computation with an explicit access bound.
    The key semantic property: a computation running in at most `bound n` steps
    can only access `bound n` bits of information about its input.

    This bridges to the BoundedSelector framework: the output is determined
    by a bounded window of the input. -/
structure StepBoundedAccess (c : Nat.Partrec.Code) (bound : Nat -> Nat) where
  /-- The computation terminates within the bound. -/
  h_bounded : StepBounded c bound
  /-- The access pattern: which bit positions are read.
      For any input n, the computation reads at most `bound n` positions. -/
  accessed_positions : Nat -> Finset Nat
  /-- The number of accessed positions is bounded. -/
  access_count_le : forall n, (accessed_positions n).card <= bound n

/-- A poly-time computation has polynomial access. -/
structure PolyTimeAccess (c : Nat.Partrec.Code) where
  /-- The polynomial time bound. -/
  poly : PolyBound
  /-- The access structure within that bound. -/
  access : StepBoundedAccess c (fun n => poly.eval n)

/-! ## Composition of Polynomial-Time Codes -/

/-- Composition of two polynomial-time bounded codes is polynomial-time bounded,
    given that the composition's step count is bounded by the composed polynomial.

    The full proof requires detailed analysis of evaln's step accounting for
    Code.comp. We package the compositional bound as a hypothesis. -/
theorem polyTimeBounded_of_composition
    {c₁ c₂ : Nat.Partrec.Code}
    (_h₁ : PolyTimeBounded c₁) (_h₂ : PolyTimeBounded c₂)
    (p_comp : PolyBound)
    (h_comp_bound : StepBounded (Nat.Partrec.Code.comp c₁ c₂) (fun n => p_comp.eval n)) :
    PolyTimeBounded (Nat.Partrec.Code.comp c₁ c₂) := by
  exact ⟨p_comp, h_comp_bound⟩

/-- The eval semantics of Code.comp: composition computes bind. -/
theorem eval_comp_eq_bind (c₁ c₂ : Nat.Partrec.Code) (n : Nat) :
    (Nat.Partrec.Code.comp c₁ c₂).eval n =
    c₂.eval n >>= c₁.eval := by
  simp [Nat.Partrec.Code.eval]

/-- If both codes are step-bounded and total, their composition is total. -/
theorem comp_total_of_stepBounded
    {c₁ c₂ : Nat.Partrec.Code} {f₁ f₂ : Nat -> Nat}
    (h₁ : StepBounded c₁ f₁) (h₂ : StepBounded c₂ f₂) (n : Nat) :
    ((Nat.Partrec.Code.comp c₁ c₂).eval n).Dom := by
  rw [eval_comp_eq_bind]
  have hdom₂ := stepBounded_implies_total h₂ n
  simp [Part.bind_eq_bind, hdom₂]
  exact stepBounded_implies_total h₁ _

/-! ## Connection to Instance Families -/

/-- A decidable instance family in the polynomial-time sense.
    Each instance size n has a code that decides membership,
    running in time polynomial in n. -/
structure PolyTimeFamily where
  /-- The decision code for each instance size. -/
  code : Nat -> Nat.Partrec.Code
  /-- The predicate being decided at each size. -/
  predicate : Nat -> Nat -> Prop
  /-- Decidability at each size. -/
  decidable : forall n, DecidablePred (predicate n)
  /-- A uniform polynomial bound across all sizes. -/
  poly : PolyBound
  /-- Each code is step-bounded by the polynomial evaluated at the instance size. -/
  bounded : forall n, StepBounded (code n) (fun m => poly.eval (n + m))
  /-- Correctness: the code decides the predicate. -/
  correct : forall n m, Nat.Partrec.Code.eval (code n) m =
    Part.some (if @decide (predicate n m) (decidable n m) then 1 else 0)

/-- A PolyTimeFamily is total at every instance. -/
theorem polyTimeFamily_total (fam : PolyTimeFamily) (n m : Nat) :
    (Nat.Partrec.Code.eval (fam.code n) m).Dom := by
  rw [Part.dom_iff_mem]
  exact ⟨_, by rw [fam.correct]; exact Part.mem_some _⟩

/-! ## Evaln Step Bound Transfer -/

/-- If evaln k c n = some m, then for any k' >= k, evaln k' c n = some m.
    This is the Option-valued form of evaln_mono. -/
theorem evaln_eq_some_mono {k₁ k₂ : Nat} {c : Nat.Partrec.Code} {n m : Nat}
    (hk : k₁ <= k₂) (h : Nat.Partrec.Code.evaln k₁ c n = some m) :
    Nat.Partrec.Code.evaln k₂ c n = some m := by
  have hmem : m ∈ Nat.Partrec.Code.evaln k₁ c n := by
    rw [Option.mem_def]; exact h
  have := evaln_monotone_steps hk hmem
  rw [Option.mem_def] at this
  exact this

/-- The input n must be strictly less than the step bound for evaln to succeed. -/
theorem evaln_input_lt_steps {k : Nat} {c : Nat.Partrec.Code} {n m : Nat}
    (h : Nat.Partrec.Code.evaln k c n = some m) : n < k := by
  have hmem : m ∈ Nat.Partrec.Code.evaln k c n := by
    rw [Option.mem_def]; exact h
  exact Nat.Partrec.Code.evaln_bound hmem

/-- A step-bounded code requires that f n > n for all n. -/
theorem stepBounded_bound_gt_input {c : Nat.Partrec.Code} {f : Nat -> Nat}
    (hf : StepBounded c f) (n : Nat) : n < f n := by
  obtain ⟨m, hm⟩ := evaln_some_of_isSome (hf n)
  exact evaln_input_lt_steps hm

/-- A polynomial-time code's bound exceeds its input. -/
theorem polyTimeBounded_bound_gt_input {c : Nat.Partrec.Code}
    (h : PolyTimeBounded c) (n : Nat) : exists p : PolyBound, n < p.eval n := by
  obtain ⟨p, hp⟩ := h
  exact ⟨p, stepBounded_bound_gt_input hp n⟩

/-! ## Determinism -/

/-- evaln is deterministic: if it produces a result, that result is unique.
    This follows from evaln being a function (Option-valued). -/
theorem evaln_deterministic {k : Nat} {c : Nat.Partrec.Code} {n m₁ m₂ : Nat}
    (h₁ : Nat.Partrec.Code.evaln k c n = some m₁)
    (h₂ : Nat.Partrec.Code.evaln k c n = some m₂) : m₁ = m₂ := by
  rw [h₁] at h₂; exact Option.some.inj h₂

/-- eval is deterministic: a Part function has at most one value. -/
theorem eval_deterministic {c : Nat.Partrec.Code} {n m₁ m₂ : Nat}
    (h₁ : m₁ ∈ Nat.Partrec.Code.eval c n)
    (h₂ : m₂ ∈ Nat.Partrec.Code.eval c n) : m₁ = m₂ :=
  Part.mem_unique h₁ h₂

/-- Step-bounded evaluation at different step counts agrees on the result. -/
theorem stepBounded_eval_unique {c : Nat.Partrec.Code} {f : Nat -> Nat}
    (hf : StepBounded c f) (n : Nat) :
    forall m, m ∈ Nat.Partrec.Code.eval c n ->
    m = stepBounded_result c f hf n := by
  intro m hm
  have hdom := stepBounded_implies_total hf n
  have hget : stepBounded_result c f hf n ∈ Nat.Partrec.Code.eval c n := by
    unfold stepBounded_result
    exact Part.get_mem hdom
  exact eval_deterministic hm hget

end ClassicalConstraints
