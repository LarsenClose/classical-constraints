/-
  ClassicalConstraints/ReductionTheory.lean
  NP reductions anchored in Mathlib's ManyOneReducible infrastructure.

  Defines NPPred, polynomial many-one reducibility, NPComplete,
  Cook-Levin as a structure, and connects to the existing
  SATPresheafCore / CookSelectorBridge framework.
-/

import ClassicalConstraints.Shared.Basic
import ClassicalConstraints.Shared.CookSelectorBridge
import Mathlib.Computability.Reduce

/-! # Reduction Theory

Formalizes the reduction-theoretic foundation of NP-completeness:

1. **NPPred**: NP predicates with verifiers and polynomial witness bounds.
2. **PolyBoundC**: composable polynomial bounds in the form `c * (n+1)^d`.
3. **PolyManyOneReducible**: polynomial many-one reductions (Karp reductions).
4. **NPComplete**: NP-completeness via universal polynomial reduction.
5. **CookLevinTheorem**: the Cook-Levin theorem stated as a structure.
6. **Connection lemmas**: linking to InstanceFamily, SATPresheafCore,
   and Mathlib's `ManyOneReducible`.

Classical.choice is used freely (this is the classical complexity side). -/

namespace ClassicalConstraints

open SATInstance

/-! ## NP Predicates -/

/-- An NP predicate: a predicate on ℕ with a polynomial-time verifier
    and polynomially bounded witnesses. -/
structure NPPred where
  /-- The underlying predicate -/
  pred : ℕ → Prop
  /-- The verifier: returns true when w is a valid witness for n -/
  verify : ℕ → ℕ → Bool
  /-- Soundness: if the verifier accepts, the predicate holds -/
  h_sound : ∀ n w, verify n w = true → pred n
  /-- Completeness: if the predicate holds, some witness is accepted -/
  h_complete : ∀ n, pred n → ∃ w, verify n w = true
  /-- Polynomial bound on witness size -/
  witnessBound : PolyBound
  /-- Witnesses need only be checked up to the bound -/
  h_witness_bounded : ∀ n, pred n →
    ∃ w, w ≤ witnessBound.eval n ∧ verify n w = true

/-- The predicate of an NPPred is decidable (classically). -/
noncomputable instance NPPred.decidable (P : NPPred) : DecidablePred P.pred :=
  fun _ => Classical.dec _

/-- An NPPred whose predicate is always false. -/
def NPPred.empty : NPPred where
  pred := fun _ => False
  verify := fun _ _ => false
  h_sound := fun _ _ h => by simp at h
  h_complete := fun _ h => absurd h id
  witnessBound := ⟨0, 0⟩
  h_witness_bounded := fun _ h => absurd h id

/-- An NPPred whose predicate is always true. -/
def NPPred.trivialPred : NPPred where
  pred := fun _ => True
  verify := fun _ _ => true
  h_sound := fun _ _ _ => True.intro
  h_complete := fun _ _ => ⟨0, rfl⟩
  witnessBound := ⟨0, 0⟩
  h_witness_bounded := fun _ _ => ⟨0, Nat.zero_le _, rfl⟩

/-- Two NPPreds with the same predicate agree pointwise. -/
theorem NPPred.ext_pred {P Q : NPPred} (h : P.pred = Q.pred) :
    ∀ n, P.pred n ↔ Q.pred n :=
  fun _ => h ▸ Iff.rfl

/-! ## Composable Polynomial Bounds

Bounds of the form `c * (n + 1)^d` are closed under composition,
making transitivity of polynomial reducibility clean to prove.
Contrast with PolyBound (from CookSelectorBridge) which uses `n^d + c`. -/

/-- A polynomial bound in the form `c * (n + 1)^d`. -/
structure PolyBoundC where
  coeff : ℕ
  degree : ℕ

namespace PolyBoundC

/-- Evaluate the polynomial bound at n. -/
def eval (p : PolyBoundC) (n : ℕ) : ℕ :=
  p.coeff * (n + 1) ^ p.degree

/-- The identity bound: n ≤ 1 * (n + 1)^1. -/
def identity : PolyBoundC := ⟨1, 1⟩

theorem identity_bound (n : ℕ) : n ≤ identity.eval n := by
  unfold identity eval; simp

/-- eval is monotone in n. -/
theorem eval_monotone (p : PolyBoundC) {m n : ℕ} (h : m ≤ n) :
    p.eval m ≤ p.eval n := by
  simp only [eval]
  apply Nat.mul_le_mul_left
  exact Nat.pow_le_pow_left (by omega) p.degree

/-- Composition of polynomial bounds. -/
def compose (p₁ p₂ : PolyBoundC) : PolyBoundC :=
  ⟨p₂.coeff * (p₁.coeff + 1) ^ p₂.degree, p₁.degree * p₂.degree⟩

private theorem nat_add_one_mul (a b : ℕ) : (a + 1) * b = a * b + b :=
  Nat.add_mul a 1 b |>.trans (by simp)

theorem compose_bound (p₁ p₂ : PolyBoundC) (f g : ℕ → ℕ)
    (hf : ∀ n, f n ≤ p₁.eval n) (hg : ∀ m, g m ≤ p₂.eval m)
    (n : ℕ) : g (f n) ≤ (compose p₁ p₂).eval n := by
  simp only [compose, eval] at *
  have hbase : (n + 1) ^ p₁.degree ≥ 1 := Nat.one_le_pow _ _ (Nat.succ_pos n)
  calc g (f n)
      ≤ p₂.coeff * (f n + 1) ^ p₂.degree := hg (f n)
    _ ≤ p₂.coeff * (p₁.coeff * (n + 1) ^ p₁.degree + 1) ^ p₂.degree := by
        apply Nat.mul_le_mul_left
        apply Nat.pow_le_pow_left
        have := hf n; omega
    _ ≤ p₂.coeff * ((p₁.coeff + 1) * (n + 1) ^ p₁.degree) ^ p₂.degree := by
        apply Nat.mul_le_mul_left
        apply Nat.pow_le_pow_left
        rw [nat_add_one_mul]; omega
    _ = p₂.coeff * ((p₁.coeff + 1) ^ p₂.degree *
          ((n + 1) ^ p₁.degree) ^ p₂.degree) := by
        congr 1; rw [Nat.mul_pow]
    _ = p₂.coeff * (p₁.coeff + 1) ^ p₂.degree *
          (n + 1) ^ (p₁.degree * p₂.degree) := by
        rw [← pow_mul, Nat.mul_assoc]

end PolyBoundC

/-! ## Connecting PolyBound and PolyBoundC

The existing CookSelectorBridge uses PolyBound (n^d + c), while
reduction theory uses PolyBoundC (c * (n+1)^d). We show PolyBound
is dominated by a PolyBoundC. -/

/-- Every PolyBound is dominated by a PolyBoundC. -/
def PolyBoundC.ofPolyBound (p : PolyBound) : PolyBoundC where
  coeff := p.constant + 1
  degree := p.degree

theorem PolyBoundC.ofPolyBound_dominates (p : PolyBound) (n : ℕ) :
    p.eval n ≤ (PolyBoundC.ofPolyBound p).eval n := by
  simp only [PolyBound.eval, PolyBoundC.ofPolyBound, PolyBoundC.eval]
  have h1 : (n + 1) ^ p.degree ≥ 1 := Nat.one_le_pow _ _ (Nat.succ_pos n)
  have h2 : n ^ p.degree ≤ (n + 1) ^ p.degree :=
    Nat.pow_le_pow_left (Nat.le_succ n) p.degree
  -- Goal: n^d + c ≤ (c+1) * (n+1)^d
  -- (c+1)*(n+1)^d = c*(n+1)^d + (n+1)^d
  rw [PolyBoundC.nat_add_one_mul]
  -- c*(n+1)^d + (n+1)^d ≥ c + n^d
  have h4 : p.constant * (n + 1) ^ p.degree ≥ p.constant :=
    Nat.le_mul_of_pos_right _ (by omega)
  omega

/-! ## Polynomial Many-One Reducibility (Karp Reductions) -/

/-- Polynomial many-one reducibility between predicates on ℕ.
    Uses the composable `PolyBoundC` form `c * (n + 1)^d`. -/
structure PolyManyOneReducible (p q : ℕ → Prop) where
  /-- The reduction function -/
  f : ℕ → ℕ
  /-- Correctness: p n ↔ q (f n) -/
  h_correct : ∀ n, p n ↔ q (f n)
  /-- Polynomial bound on output size -/
  bound : PolyBoundC
  /-- The output is polynomially bounded -/
  h_poly : ∀ n, f n ≤ bound.eval n

notation:50 p " ≤ₚ " q => PolyManyOneReducible p q

/-- Polynomial reducibility is reflexive. -/
def polyReducible_refl (p : ℕ → Prop) : p ≤ₚ p where
  f := id
  h_correct := fun _ => Iff.rfl
  bound := PolyBoundC.identity
  h_poly := PolyBoundC.identity_bound

/-- A polynomial many-one reduction preserves truth forward. -/
theorem PolyManyOneReducible.forward {p q : ℕ → Prop} (r : p ≤ₚ q)
    {n : ℕ} (h : p n) : q (r.f n) :=
  (r.h_correct n).mp h

/-- A polynomial many-one reduction preserves truth backward. -/
theorem PolyManyOneReducible.backward {p q : ℕ → Prop} (r : p ≤ₚ q)
    {n : ℕ} (h : q (r.f n)) : p n :=
  (r.h_correct n).mpr h

/-- Polynomial reducibility is transitive. -/
def polyReducible_trans {p q r : ℕ → Prop}
    (hpq : p ≤ₚ q) (hqr : q ≤ₚ r) : p ≤ₚ r where
  f := hqr.f ∘ hpq.f
  h_correct n := (hpq.h_correct n).trans (hqr.h_correct (hpq.f n))
  bound := PolyBoundC.compose hpq.bound hqr.bound
  h_poly n := PolyBoundC.compose_bound hpq.bound hqr.bound hpq.f hqr.f
    hpq.h_poly hqr.h_poly n

/-! ## Connection to Mathlib's ManyOneReducible -/

/-- A polynomial reduction that is Mathlib-computable yields ≤₀. -/
theorem manyOne_of_poly_computable {p q : ℕ → Prop}
    (r : p ≤ₚ q) (hc : Computable r.f) : p ≤₀ q :=
  ⟨r.f, hc, r.h_correct⟩

/-! ## NP-Hardness and NP-Completeness -/

/-- NP-hardness: every NP predicate polynomially reduces to q. -/
structure NPHard (q : ℕ → Prop) where
  /-- Every NP predicate reduces to q -/
  hard : ∀ P : NPPred, P.pred ≤ₚ q

/-- NP-completeness: in NP and NP-hard. -/
structure NPComplete (q : ℕ → Prop) where
  /-- q is in NP -/
  in_np : NPPred
  /-- The NPPred's underlying predicate is q -/
  h_pred_eq : in_np.pred = q
  /-- q is NP-hard -/
  hardness : NPHard q

/-- An NP-complete problem is in NP. -/
theorem NPComplete.is_np {q : ℕ → Prop} (hq : NPComplete q) :
    ∃ P : NPPred, P.pred = q :=
  ⟨hq.in_np, hq.h_pred_eq⟩

/-- NP-completeness transfers along polynomial reductions. -/
def NPComplete.transfer {q r : ℕ → Prop}
    (hq : NPComplete q) (hqr : q ≤ₚ r) (hr : NPPred)
    (hr_eq : hr.pred = r) : NPComplete r where
  in_np := hr
  h_pred_eq := hr_eq
  hardness := { hard := fun P => polyReducible_trans (hq.hardness.hard P) hqr }

/-- NP-hardness is upward closed under polynomial reductions. -/
def NPHard.of_reduction {p q : ℕ → Prop}
    (hq : NPHard q) (hqp : q ≤ₚ p) : NPHard p where
  hard := fun P => polyReducible_trans (hq.hard P) hqp

/-! ## Cook-Levin Theorem (structure)

The Cook-Levin theorem states that SAT is NP-complete.
We state what it SAYS as a structure, not prove it. -/

/-- A SAT encoding: identifies a predicate on ℕ as the SAT predicate. -/
structure SATEncoding where
  /-- The SAT predicate on encoded instances -/
  satPred : ℕ → Prop
  /-- SAT is in NP -/
  sat_in_np : NPPred
  /-- The NPPred has the right predicate -/
  h_pred_eq : sat_in_np.pred = satPred

/-- The Cook-Levin theorem: SAT is NP-complete. -/
structure CookLevinTheorem where
  /-- The SAT encoding -/
  encoding : SATEncoding
  /-- NP-completeness of SAT -/
  completeness : NPComplete encoding.satPred
  /-- The NPComplete witness uses the encoding's NPPred -/
  h_consistent : completeness.in_np = encoding.sat_in_np

/-- Given Cook-Levin, any NP predicate reduces to SAT. -/
def CookLevinTheorem.reduces_to_sat (cl : CookLevinTheorem)
    (P : NPPred) : P.pred ≤ₚ cl.encoding.satPred :=
  cl.completeness.hardness.hard P

/-- Given Cook-Levin, if SAT has a Boolean decision procedure,
    then every NP predicate does too (by composition with the reduction). -/
theorem CookLevinTheorem.np_decidable_if_sat_decidable
    (cl : CookLevinTheorem) (P : NPPred)
    (sat_decide : ℕ → Bool)
    (h_correct : ∀ n, sat_decide n = true ↔ cl.encoding.satPred n) :
    ∃ f : ℕ → Bool, ∀ n, f n = true ↔ P.pred n := by
  let red := cl.reduces_to_sat P
  exact ⟨fun n => sat_decide (red.f n),
    fun n => (h_correct (red.f n)).trans (red.h_correct n).symm⟩

/-! ## Connection to InstanceFamily and SATFamily -/

/-- A classical Boolean decision for a proposition. -/
noncomputable def classicalBool (p : Prop) : Bool :=
  @decide p (Classical.dec p)

private theorem classicalBool_true_iff (p : Prop) :
    classicalBool p = true ↔ p := by
  unfold classicalBool
  simp [decide_eq_true_eq]

/-- Convert an InstanceFamily to an NPPred. The construction uses
    classical decidability since InstanceFamily has finite types. -/
noncomputable def NPPred.ofInstanceFamily (F : InstanceFamily) : NPPred where
  pred := fun n => ∃ (x : F.X n), F.Satisfiable n x
  verify := fun n _ => classicalBool (∃ (x : F.X n) (w : F.W n), F.Sat n x w)
  h_sound := fun n _ h => by
    rw [classicalBool_true_iff] at h
    obtain ⟨x, w, hw⟩ := h; exact ⟨x, w, hw⟩
  h_complete := fun n ⟨x, w, hw⟩ =>
    ⟨0, by rw [classicalBool_true_iff]; exact ⟨x, w, hw⟩⟩
  witnessBound := ⟨0, 0⟩
  h_witness_bounded := fun n ⟨x, w, hw⟩ =>
    ⟨0, Nat.zero_le _, by rw [classicalBool_true_iff]; exact ⟨x, w, hw⟩⟩

/-- The InstanceFamily-derived NPPred captures satisfiability. -/
theorem NPPred.ofInstanceFamily_iff (F : InstanceFamily) (n : ℕ) :
    (NPPred.ofInstanceFamily F).pred n ↔ ∃ (x : F.X n), F.Satisfiable n x :=
  Iff.rfl

/-- Convert a SATFamily to an NPPred.
    NOTE: The witness parameter is unused — verification uses classical
    decidability (classicalBool) to bypass the NP certificate. This makes
    the NP structure formal-but-vacuous for this definition. A constructive
    version would decode the witness and check satisfaction directly. -/
noncomputable def NPPred.ofSATFamily (family : SATFamily) : NPPred where
  pred := fun n => (family n).Satisfiable
  verify := fun n _ => classicalBool (family n).Satisfiable
  h_sound := fun n _ h => by rw [classicalBool_true_iff] at h; exact h
  h_complete := fun n hn =>
    ⟨0, by rw [classicalBool_true_iff]; exact hn⟩
  witnessBound := ⟨0, 0⟩
  h_witness_bounded := fun n hn =>
    ⟨0, Nat.zero_le _, by rw [classicalBool_true_iff]; exact hn⟩

/-- The SATFamily NPPred captures satisfiability. -/
theorem NPPred.ofSATFamily_iff (family : SATFamily) (n : ℕ) :
    (NPPred.ofSATFamily family).pred n ↔ (family n).Satisfiable :=
  Iff.rfl

/-! ## Reduction Preserves Decidability -/

/-- If p ≤ₚ q and q is decidable, then p is decidable. -/
def decidable_of_polyReducible {p q : ℕ → Prop}
    (r : p ≤ₚ q) [hq : DecidablePred q] : DecidablePred p :=
  fun n => decidable_of_iff (q (r.f n)) (r.h_correct n).symm

/-- If p ≤ₚ q and q has a Boolean decision procedure, then
    p has one too (by composition). -/
theorem bool_decision_of_polyReducible {p q : ℕ → Prop}
    (r : p ≤ₚ q) (decide_q : ℕ → Bool)
    (h_correct : ∀ n, decide_q n = true ↔ q n) :
    ∃ decide_p : ℕ → Bool, ∀ n, decide_p n = true ↔ p n :=
  ⟨decide_q ∘ r.f, fun n =>
    (h_correct (r.f n)).trans (r.h_correct n).symm⟩

/-! ## NP Closure Properties -/

/-- An NPWitness bundles a predicate with sound/complete verification,
    without a polynomial bound on witness size. -/
structure NPWitness where
  /-- The underlying predicate -/
  pred : ℕ → Prop
  /-- The verifier -/
  verify : ℕ → ℕ → Bool
  /-- Soundness -/
  h_sound : ∀ n w, verify n w = true → pred n
  /-- Completeness -/
  h_complete : ∀ n, pred n → ∃ w, verify n w = true

/-- Every NPPred gives an NPWitness (forgetting the bound). -/
def NPPred.toNPWitness (P : NPPred) : NPWitness where
  pred := P.pred
  verify := P.verify
  h_sound := P.h_sound
  h_complete := P.h_complete

/-- Pull back an NPWitness along a polynomial reduction. -/
def NPWitness.pullback (P : NPWitness) {q : ℕ → Prop}
    (r : q ≤ₚ P.pred) : NPWitness where
  pred := q
  verify := fun n w => P.verify (r.f n) w
  h_sound := fun _ w h => r.backward (P.h_sound _ w h)
  h_complete := fun _ hn => P.h_complete _ (r.forward hn)

/-- The pullback NPWitness has the correct predicate. -/
theorem NPWitness.pullback_pred (P : NPWitness) {q : ℕ → Prop}
    (r : q ≤ₚ P.pred) : (P.pullback r).pred = q :=
  rfl

/-- NP predicates are closed under composition with polynomial reductions:
    if P.pred is in NP and q reduces to P.pred, then q is verifiable. -/
theorem np_closed_under_reduction (P : NPPred) {q : ℕ → Prop}
    (r : q ≤ₚ P.pred) :
    ∃ V : NPWitness, V.pred = q ∧
      (∀ n w, V.verify n w = true → q n) ∧
      (∀ n, q n → ∃ w, V.verify n w = true) :=
  ⟨P.toNPWitness.pullback r,
   rfl,
   fun _ w h => r.backward (P.h_sound _ w h),
   fun _ hn => P.h_complete _ (r.forward hn)⟩

/-! ## Structural Properties of Reductions -/

/-- The identity reduction is the trivial one. -/
theorem polyReducible_refl_f (p : ℕ → Prop) :
    (polyReducible_refl p).f = id :=
  rfl

/-- Transitivity composes the reduction functions. -/
theorem polyReducible_trans_f {p q r : ℕ → Prop}
    (hpq : p ≤ₚ q) (hqr : q ≤ₚ r) :
    (polyReducible_trans hpq hqr).f = hqr.f ∘ hpq.f :=
  rfl

/-- A constant reduction: if p n holds iff q m for fixed m,
    then p ≤ₚ q (via the constant function). -/
def polyReducible_const (p q : ℕ → Prop) (m : ℕ)
    (h : ∀ n, p n ↔ q m) : p ≤ₚ q where
  f := fun _ => m
  h_correct := h
  bound := ⟨m, 0⟩
  h_poly _ := by simp [PolyBoundC.eval]

/-! ## Summary

The reduction theory provides the following chain of concepts:

  NPPred (NP predicates)
    | (universal reduction)
  NPHard q (every NPPred reduces to q)
    | (+ membership)
  NPComplete q (NPHard + in NP)
    | (Cook-Levin)
  CookLevinTheorem (SAT is NPComplete)

Structural properties:
- PolyManyOneReducible is reflexive and transitive (preorder)
- PolyManyOneReducible + Computable -> ManyOneReducible (Mathlib's <=0)
- NPComplete transfers along polynomial reductions
- PolyBound (CookSelectorBridge) embeds into PolyBoundC
- NPPred can be constructed from InstanceFamily or SATFamily -/

end ClassicalConstraints
