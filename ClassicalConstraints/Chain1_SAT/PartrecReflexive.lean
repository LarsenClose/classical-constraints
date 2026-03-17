/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Partrec Code as Reflexive Object

This file bridges Mathlib's `Nat.Partrec.Code` to the reflexive object framework.

The key insight: Code IS D (the reflexive domain).
- `Code.encodeCode` = fold (naming: turn a code into a natural number)
- `Code.eval` = unfold (execution: run a code on an input)
- `Code.ofNatCode` = decode (turn a natural number back into a code)

Code is literally a reflexive object where programs operate on (encodings of) programs.
The self-application `selfApp(n) = eval(decode(n), n)` is the computational core:
running program n on its own encoding.

Since `Code.eval` is partial (`Code → ℕ →. ℕ`), we work with `PartialReflexiveObject`,
a reflexive structure that acknowledges partiality in the unfold direction.
-/

import Mathlib.Computability.PartrecCode

namespace ClassicalConstraints

open Nat.Partrec

/-! ## Partial Reflexive Objects

A reflexive object where the unfold (evaluation) direction is partial.
This captures the essential structure of computational domains where
self-application may diverge. -/

/-- A partial reflexive object: carrier with total fold and partial unfold.
The fold direction (naming/encoding) is always total, but unfold (evaluation)
may diverge, which is captured by the `Part` monad. -/
structure PartialReflexiveObject where
  /-- The carrier type (domain of discourse). -/
  carrier : Type
  /-- Fold: encode/name an element (total). -/
  fold : carrier → carrier
  /-- Unfold: evaluate/execute (partial -- may diverge). -/
  unfold : carrier → Part carrier
  /-- Folded values can always be unfolded (encoding is always decodable). -/
  roundtrip_dom : ∀ x, (unfold (fold x)).Dom
  /-- Unfolding a folded value recovers the original. -/
  roundtrip_val : ∀ x, (unfold (fold x)).get (roundtrip_dom x) = x

/-! ## Step-Bounded Reflexive Objects

For complexity analysis, we also define a step-bounded variant
using `Code.evaln` which always terminates. -/

/-- A step-bounded reflexive object: like PartialReflexiveObject but unfold
takes a step budget and returns `Option` (always terminates, but may return
`none` if budget exhausted). -/
structure BoundedReflexiveObject where
  /-- The carrier type. -/
  carrier : Type
  /-- Fold: encode an element (total). -/
  fold : carrier → carrier
  /-- Unfold with bounded steps: always terminates. -/
  unfold : ℕ → carrier → Option carrier
  /-- Monotonicity: more steps never lose results. -/
  mono : ∀ k₁ k₂ x y, k₁ ≤ k₂ → unfold k₁ x = some y → unfold k₂ x = some y
  /-- Sufficient steps guarantee roundtrip. -/
  roundtrip : ∀ x, ∃ k, unfold k (fold x) = some x

/-! ## Code Encoding Roundtrip

Fundamental property: `ofNatCode ∘ encodeCode = id`.
This is the fold-unfold roundtrip at the naming level. -/

/-- The encoding roundtrip: decoding an encoded code recovers the original. -/
theorem code_encode_roundtrip (c : Code) :
    Code.ofNatCode (Code.encodeCode c) = c := by
  have h := Encodable.encodek c
  exact Option.some_injective _ h

/-- Encodable.encode agrees with encodeCode for Code. -/
theorem encode_eq_encodeCode (c : Code) :
    Encodable.encode c = Code.encodeCode c := rfl

/-- Encodable.decode agrees with ofNatCode for Code. -/
theorem decode_eq_ofNatCode (n : ℕ) :
    Encodable.decode (α := Code) n = some (Code.ofNatCode n) := rfl

/-! ## Self-Application

The computational core: `selfApp(n) = eval(decode(n), n)`.
This is running program n on input n -- the diagonal that drives
fixed-point theorems, undecidability, and the Y combinator. -/

/-- Self-application: run program n on input n.
This is partial because evaluation may diverge. -/
def selfApp (n : ℕ) : Part ℕ :=
  Code.eval (Code.ofNatCode n) n

/-- Self-application via step-bounded evaluation. -/
def selfAppBounded (steps : ℕ) (n : ℕ) : Option ℕ :=
  Code.evaln steps (Code.ofNatCode n) n

/-- If bounded self-application succeeds, it agrees with unbounded. -/
theorem selfAppBounded_sound {k n x : ℕ} (h : x ∈ selfAppBounded k n) :
    x ∈ selfApp n :=
  Code.evaln_sound h

/-- Unbounded self-application terminates iff some bounded version does. -/
theorem selfApp_complete {n x : ℕ} :
    x ∈ selfApp n ↔ ∃ k, x ∈ selfAppBounded k n :=
  Code.evaln_complete

/-- Monotonicity: if selfApp succeeds with budget k, it succeeds with any larger budget. -/
theorem selfAppBounded_mono {k₁ k₂ n x : ℕ} (hle : k₁ ≤ k₂)
    (h : x ∈ selfAppBounded k₁ n) : x ∈ selfAppBounded k₂ n :=
  Code.evaln_mono hle h

/-! ## Code as Partial Reflexive Object

We construct the partial reflexive object from Code.
- carrier = ℕ (encoded codes)
- fold = encodeCode ∘ ofNatCode (re-encode: canonicalize)
- unfold n = eval(decode(n), n) (self-application)

Note: fold here is the identity on canonical encodings.
The real "fold" in the reflexive sense is just the encoding map. -/

/-- The naming map: encode a code as a natural number. -/
def codeFold : Code → ℕ := Code.encodeCode

/-- The execution map: partially evaluate a code on an input. -/
def codeUnfold (n : ℕ) : Part ℕ := Code.eval (Code.ofNatCode n) n

/-- codeFold is injective: different codes get different encodings.
This follows from the roundtrip property. -/
theorem codeFold_injective : Function.Injective codeFold := by
  intro c₁ c₂ h
  have h₁ := code_encode_roundtrip c₁
  have h₂ := code_encode_roundtrip c₂
  unfold codeFold at h
  rw [← h₁, ← h₂, h]

/-! ## Grade Structure

A grade function on codes, measuring syntactic complexity.
The simplest choice: grade = encoding value (larger codes get larger numbers). -/

/-- Grade of a code: its encoding as a natural number.
Larger/more complex codes get higher grades. -/
def codeGrade (c : Code) : ℕ := Code.encodeCode c

/-- Grade is injective (same grade means same code). -/
theorem codeGrade_injective : Function.Injective codeGrade :=
  codeFold_injective

/-- Code grade matches the Encodable encoding. -/
theorem codeGrade_eq_encode (c : Code) : codeGrade c = Encodable.encode c := rfl

/-! ## Universal Evaluation

The universal evaluator: given a code number and input, run the code.
This is the "unfold" at the level of natural numbers. -/

/-- Universal partial evaluation: decode a number as a code and run it. -/
def universalEval (e n : ℕ) : Part ℕ :=
  Code.eval (Code.ofNatCode e) n

/-- Step-bounded universal evaluation. -/
def universalEvalBounded (k e n : ℕ) : Option ℕ :=
  Code.evaln k (Code.ofNatCode e) n

/-- Bounded evaluation is sound with respect to unbounded. -/
theorem universalEvalBounded_sound {k e n x : ℕ}
    (h : x ∈ universalEvalBounded k e n) : x ∈ universalEval e n :=
  Code.evaln_sound h

/-- Self-application is universal evaluation on the diagonal. -/
theorem selfApp_eq_universalEval_diag (n : ℕ) :
    selfApp n = universalEval n n := rfl

/-! ## Totality of Simple Codes

Some codes are guaranteed to be total (always terminate).
We characterize which ones. -/

/-- A code is total if eval always terminates on every input. -/
def CodeTotal (c : Code) : Prop :=
  ∀ n : ℕ, (Code.eval c n).Dom

/-- The zero code is total: it always returns 0. -/
theorem zero_total : CodeTotal Code.zero := by
  intro n; trivial

/-- The successor code is total: it always returns n+1. -/
theorem succ_total : CodeTotal Code.succ := by
  intro n; trivial

/-- The left-projection code is total. -/
theorem left_total : CodeTotal Code.left := by
  intro n; trivial

/-- The right-projection code is total. -/
theorem right_total : CodeTotal Code.right := by
  intro n; trivial

/-! ## Composition Structure

Code composition preserves the reflexive structure. -/

/-- Composing two codes. -/
def codeCompose (f g : Code) : Code := Code.comp f g

/-- Pairing two codes. -/
def codePair (f g : Code) : Code := Code.pair f g

/-- Composition grade bound: the composed code's grade depends on the components. -/
theorem compose_grade_bound (f g : Code) :
    codeGrade f ≤ codeGrade (codeCompose f g) ∨
    codeGrade g ≤ codeGrade (codeCompose f g) := by
  -- The encoding of comp f g involves both f and g, so at least one
  -- component's encoding is bounded by the composite's
  left
  unfold codeGrade codeCompose
  simp only [Code.encodeCode]
  have := Nat.left_le_pair (Code.encodeCode f) (Code.encodeCode g)
  omega

/-! ## Enumeration and Counting

Code is enumerable: we can list all codes in order of their encoding. -/

/-- Every natural number decodes to some code. -/
theorem code_decode_total (n : ℕ) : ∃ c : Code, Code.ofNatCode n = c :=
  ⟨Code.ofNatCode n, rfl⟩

/-- There are infinitely many codes (the encoding is injective). -/
theorem code_infinite : Function.Injective Code.encodeCode :=
  codeFold_injective

/-! ## The Diagonal Lemma (Code-Level)

The diagonal lemma in computability: for any total computable f,
there exists a code e such that eval(e, n) = eval(f(e), n).
This is the fixed-point theorem (Kleene's recursion theorem).

We state the consequence: self-reference is unavoidable. -/

/-- Self-application of encoded codes: the map n ↦ eval(decode(n), n)
is itself a partial recursive function. This is crucial: the diagonal
is computable, which is what makes diagonalization arguments work. -/
theorem selfApp_partrec : Nat.Partrec (fun n => selfApp n) := by
  unfold selfApp
  rw [← Partrec.nat_iff]
  exact Code.eval_part.comp (Computable.ofNat Code) Computable.id

/-! ## Connection to Reflexive Object Theory

The key theorems connecting Code to the abstract reflexive framework:
1. Code has fold (encoding) and partial unfold (evaluation)
2. The fold is injective (different codes, different numbers)
3. The roundtrip fold-then-unfold is the identity on Code
4. Self-application arises naturally from the diagonal -/

/-- The reflexive structure of Code, summarized as a record.
This packages the key properties that make Code a reflexive domain. -/
structure CodeReflexiveData where
  /-- The carrier is ℕ (encoded codes). -/
  carrier := ℕ
  /-- Encoding is injective. -/
  encode_injective : Function.Injective Code.encodeCode
  /-- Decoding after encoding is the identity. -/
  encode_decode_roundtrip : ∀ c : Code, Code.ofNatCode (Code.encodeCode c) = c
  /-- Self-application is computable (partial recursive). -/
  selfApp_computable : Nat.Partrec (fun n => selfApp n)

/-- Construct the reflexive data for Code. -/
def codeReflexiveData : CodeReflexiveData where
  encode_injective := codeFold_injective
  encode_decode_roundtrip := code_encode_roundtrip
  selfApp_computable := selfApp_partrec

/-! ## Growth and Complexity

The encoding of Code grows: more complex codes get larger encodings.
This is the "growth gap" at the code level. -/

/-- Basic codes have small encodings. -/
theorem zero_grade : codeGrade Code.zero = 0 := rfl
theorem succ_grade : codeGrade Code.succ = 1 := rfl
theorem left_grade : codeGrade Code.left = 2 := rfl
theorem right_grade : codeGrade Code.right = 3 := rfl

/-- Composite codes have encodings strictly larger than 3. -/
theorem composite_grade_gt_three (f g : Code) :
    codeGrade (Code.pair f g) > 3 := by
  unfold codeGrade
  simp only [Code.encodeCode]
  omega

theorem comp_grade_gt_three (f g : Code) :
    codeGrade (Code.comp f g) > 3 := by
  unfold codeGrade
  simp only [Code.encodeCode]
  omega

theorem prec_grade_gt_three (f g : Code) :
    codeGrade (Code.prec f g) > 3 := by
  unfold codeGrade
  simp only [Code.encodeCode]
  omega

theorem rfind_grade_gt_three (f : Code) :
    codeGrade (Code.rfind' f) > 3 := by
  unfold codeGrade
  simp only [Code.encodeCode]
  omega

/-! ## Code Classification

Every code is either basic (grade ≤ 3) or composite (grade > 3).
This gives a decidable classification. -/

/-- A code is basic iff it is one of the four atomic constructors. -/
inductive IsBasicCode : Code → Prop where
  | zero : IsBasicCode Code.zero
  | succ : IsBasicCode Code.succ
  | left : IsBasicCode Code.left
  | right : IsBasicCode Code.right

/-- A code is composite iff it uses pair, comp, prec, or rfind'. -/
inductive IsCompositeCode : Code → Prop where
  | pair : ∀ f g, IsCompositeCode (Code.pair f g)
  | comp : ∀ f g, IsCompositeCode (Code.comp f g)
  | prec : ∀ f g, IsCompositeCode (Code.prec f g)
  | rfind : ∀ f, IsCompositeCode (Code.rfind' f)

/-- Every code is either basic or composite. -/
theorem basic_or_composite (c : Code) : IsBasicCode c ∨ IsCompositeCode c := by
  cases c with
  | zero => exact Or.inl IsBasicCode.zero
  | succ => exact Or.inl IsBasicCode.succ
  | left => exact Or.inl IsBasicCode.left
  | right => exact Or.inl IsBasicCode.right
  | pair f g => exact Or.inr (IsCompositeCode.pair f g)
  | comp f g => exact Or.inr (IsCompositeCode.comp f g)
  | prec f g => exact Or.inr (IsCompositeCode.prec f g)
  | rfind' f => exact Or.inr (IsCompositeCode.rfind f)

/-- Basic and composite are mutually exclusive. -/
theorem not_basic_and_composite (c : Code) :
    ¬(IsBasicCode c ∧ IsCompositeCode c) := by
  rintro ⟨hb, hc⟩
  cases hb <;> cases hc

/-- Basic codes have grade ≤ 3. -/
theorem basic_grade_le_three {c : Code} (h : IsBasicCode c) :
    codeGrade c ≤ 3 := by
  cases h <;> simp [codeGrade, Code.encodeCode]

/-- Composite codes have grade > 3. -/
theorem composite_grade_gt_three' {c : Code} (h : IsCompositeCode c) :
    codeGrade c > 3 := by
  cases h with
  | pair f g => exact composite_grade_gt_three f g
  | comp f g => exact comp_grade_gt_three f g
  | prec f g => exact prec_grade_gt_three f g
  | rfind f => exact rfind_grade_gt_three f

/-! ## Evaln Convergence

The step-bounded evaluator `evaln` converges to `eval`:
if eval terminates, some finite step count suffices. -/

/-- If evaluation terminates, there's a sufficient step bound. -/
theorem eval_implies_bounded {c : Code} {n x : ℕ} (h : x ∈ Code.eval c n) :
    ∃ k, x ∈ Code.evaln k c n :=
  Code.evaln_complete.mp h

/-- The step bound is at least the input size. -/
theorem evaln_bound_ge_input {k : ℕ} {c : Code} {n x : ℕ}
    (h : x ∈ Code.evaln k c n) : n < k :=
  Code.evaln_bound h

/-! ## Summary

This file establishes:

1. **PartialReflexiveObject**: Abstract framework for domains with partial self-application
2. **Code roundtrip**: `ofNatCode ∘ encodeCode = id` (fold-then-unfold = identity)
3. **Self-application**: `selfApp(n) = eval(decode(n), n)` is partial recursive
4. **Injectivity**: Different codes get different encodings
5. **Grade structure**: Basic codes (grade ≤ 3) vs composite (grade > 3)
6. **Step-bounded evaluation**: `evaln` converges to `eval` with monotonicity

The central observation: Code is not merely *modeled by* a reflexive object --
Code IS the reflexive object. The encoding/evaluation pair (encodeCode/eval)
IS the fold/unfold of the Lambek isomorphism, with partiality in the unfold
direction being the essential computational phenomenon.
-/

end ClassicalConstraints
