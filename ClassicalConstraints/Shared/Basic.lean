/-
  ClassicalConstraints/Basic.lean
  Instance families, solution bundles, decidability.

  This file defines the base objects from the classical P=NP definition.
  No complexity theory yet — just the combinatorial structure of
  "instances have witnesses that can be checked."
-/

import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.Card
import Mathlib.Order.Filter.Basic

/-! # Instance Families

An instance family is a size-indexed collection of instances,
witnesses, and a decidable satisfaction predicate.

This is the combinatorial core of NP:
for each size n, there are instances φ and witnesses w,
and checking Sat n φ w is decidable and efficient. -/

/-- A family of decision problems indexed by input size. -/
structure InstanceFamily where
  /-- Instance type at size n -/
  X : Nat → Type
  /-- Witness type at size n -/
  W : Nat → Type
  /-- Satisfaction predicate: does witness w satisfy instance φ at size n? -/
  Sat : (n : Nat) → X n → W n → Prop
  /-- Satisfaction is decidable (this IS verification — the eq3 side) -/
  h_dec : ∀ n (x : X n) (w : W n), Decidable (Sat n x w)
  /-- Instances are finite at each size -/
  h_fin_X : ∀ n, Fintype (X n)
  /-- Witnesses are finite at each size -/
  h_fin_W : ∀ n, Fintype (W n)

namespace InstanceFamily

/-- The solution fiber over an instance: all valid witnesses. -/
def Sol (F : InstanceFamily) (n : Nat) (φ : F.X n) : Type :=
  { w : F.W n // F.Sat n φ w }

/-- An instance is satisfiable if it has at least one witness. -/
def Satisfiable (F : InstanceFamily) (n : Nat) (φ : F.X n) : Prop :=
  ∃ w : F.W n, F.Sat n φ w

/-- The satisfiable instances at size n. -/
def SatInstances (F : InstanceFamily) (n : Nat) : Type :=
  { φ : F.X n // F.Satisfiable n φ }

end InstanceFamily
