/-
  ClassicalConstraints/SelectionFunction.lean
  Selection function framework: solver as channel.

  Every polynomial-time solver defines a selection function that
  factors through an observable basis. The selection function IS
  the solver's identity as a channel: what it can see (extract)
  determines what it can do (reconstruct).

  This file connects the descent framework to the channel/selection
  viewpoint and documents the seven-projection table relating
  the quotient structure to other mathematical frameworks.
-/

import ClassicalConstraints.Chain1_SAT.Descent
import Mathlib.Data.Fintype.Basic

/-! # Selection Functions

A selection function is a solver viewed as a communication channel:
- Forward channel (extract): instance → observable profile
- Backward channel (reconstruct): profile → witness
- Soundness: the round-trip produces valid witnesses

This is equivalent to DescentWitness: the factorization through
a basis IS the channel decomposition. -/

/-- A selection function for an instance family at size n.
    Profile is the intermediate representation — what the solver
    "sees" about an instance. The solver's identity as a channel
    is determined by extract; reconstruct is the decoder. -/
structure SelectionFunction (F : InstanceFamily) (n : Nat)
    (Profile : Type) where
  /-- Forward channel: instance to observable profile -/
  extract : F.X n → Profile
  /-- Backward channel: profile to witness -/
  reconstruct : Profile → F.W n
  /-- Soundness: round-trip produces valid witnesses for satisfiable instances -/
  h_sound : ∀ (φ : F.X n), F.Satisfiable n φ →
    F.Sat n φ (reconstruct (extract φ))

/-! ## Channel Capacity

The channel capacity of a selection function is bounded by the
cardinality of the profile space. A finite profile space means
the channel can distinguish at most |Profile| equivalence classes
of instances. -/

/-- Satisfiable is decidable (local instance for this file). -/
noncomputable instance instDecSatisfiable (F : InstanceFamily) (n : Nat) (φ : F.X n) :
    Decidable (F.Satisfiable n φ) :=
  have : Fintype (F.W n) := F.h_fin_W n
  have : ∀ w, Decidable (F.Sat n φ w) := F.h_dec n φ
  Fintype.decidableExistsFintype

/-- SatInstances is finite (local instance for this file). -/
noncomputable instance instFintypeSatInstances' (F : InstanceFamily) (n : Nat) :
    Fintype (F.SatInstances n) :=
  have : Fintype (F.X n) := F.h_fin_X n
  have : ∀ φ, Decidable (F.Satisfiable n φ) := instDecSatisfiable F n
  Subtype.fintype _

/-- The channel capacity of a selection function with finite profile space:
    the number of distinct profiles actually used by satisfiable instances.
    This bounds how many distinct witness strategies the channel can express. -/
noncomputable def channelCapacity (F : InstanceFamily) (n : Nat)
    {Profile : Type} [DecidableEq Profile]
    (sf : SelectionFunction F n Profile) : Nat :=
  let satInsts := Finset.univ (α := F.SatInstances n)
  (satInsts.image (fun φ => sf.extract φ.val)).card

/-- Channel capacity is bounded by the cardinality of the profile space. -/
theorem channelCapacity_le_card (F : InstanceFamily) (n : Nat)
    {Profile : Type} [Fintype Profile] [DecidableEq Profile]
    (sf : SelectionFunction F n Profile) :
    channelCapacity F n sf ≤ Fintype.card Profile := by
  unfold channelCapacity
  have h : (Finset.univ.image (fun φ => sf.extract (φ : F.SatInstances n).val)) ⊆
      Finset.univ (α := Profile) := fun _ _ => Finset.mem_univ _
  exact (Finset.card_le_card h).trans (le_of_eq Finset.card_univ)

/-! ## Selection Equivalence

Two selection functions are equivalent if they induce the same
partition of instances — i.e., they use the same extract (up to
isomorphism of profile spaces). The decoder can differ; what
matters is what the channel can SEE. -/

/-- Two selection functions over the same profile space are equivalent
    if they have the same extraction map. The decoder may differ,
    but the channel identity (what the solver sees) is the same. -/
def SelectionEquivalent {F : InstanceFamily} {n : Nat}
    {Profile : Type}
    (sf₁ sf₂ : SelectionFunction F n Profile) : Prop :=
  sf₁.extract = sf₂.extract

/-- Selection equivalence is an equivalence relation. -/
theorem selectionEquivalent_equiv (F : InstanceFamily) (n : Nat)
    (Profile : Type) :
    Equivalence (@SelectionEquivalent F n Profile) where
  refl := fun _ => rfl
  symm := fun h => h.symm
  trans := fun h₁ h₂ => h₁.trans h₂

/-! ## Solver as Selection Function

Every solver is trivially a selection function with Profile = X n
(the identity extraction). The interesting constraint is when
the profile must be SMALL — bounded by observable grade. -/

/-- Every solver defines a selection function with the identity
    extraction (Profile = X n). This is the trivial channel that
    sees everything. -/
def solver_is_selection (F : InstanceFamily) (n : Nat)
    (s : Solver F n) : SelectionFunction F n (F.X n) where
  extract := id
  reconstruct := s.select
  h_sound := s.h_sound

/-- Conversely, every selection function defines a solver by
    composing extract with reconstruct. -/
def selection_is_solver (F : InstanceFamily) (n : Nat)
    {Profile : Type}
    (sf : SelectionFunction F n Profile) : Solver F n where
  select := fun φ => sf.reconstruct (sf.extract φ)
  h_sound := sf.h_sound

/-- The round-trip: solver → selection → solver recovers a solver
    with the same behavior. -/
theorem solver_selection_roundtrip (F : InstanceFamily) (n : Nat)
    (s : Solver F n) :
    (selection_is_solver F n (solver_is_selection F n s)).select = s.select :=
  rfl

/-! ## Descent ↔ Bounded Selection

A DescentWitness at grade g is exactly a SelectionFunction whose
profile space is the basis observation space (Fin width → Nat),
which has cardinality bounded by the grade-g observable range.

This is the core equivalence: descent = bounded-bandwidth channel. -/

/-- A descent witness defines a selection function whose profile space
    is the basis observation space. -/
def descentWitness_to_selection (F : InstanceFamily)
    [alg : GradedObservableAlgebra F] {g n : Nat}
    (dw : DescentWitness F g n) :
    SelectionFunction F n (Fin dw.basis.width → Nat) where
  extract := dw.basis.observe
  reconstruct := dw.decode
  h_sound := dw.h_sound

/-- A selection function with profile = (Fin w → Nat) and a grade-g
    basis whose observation matches extract gives a descent witness. -/
def selection_to_descentWitness (F : InstanceFamily)
    [alg : GradedObservableAlgebra F] {g n : Nat}
    (B : ObservableBasis F g n)
    (sf : SelectionFunction F n (Fin B.width → Nat))
    (h_extract : sf.extract = B.observe) :
    DescentWitness F g n where
  basis := B
  decode := sf.reconstruct
  h_sound := by
    intro φ hsat
    have := sf.h_sound φ hsat
    rw [h_extract] at this
    exact this

/-- Core equivalence: DescentWitness g n exists iff there exists
    an ObservableBasis at grade g and a SelectionFunction whose
    extraction matches the basis observation. -/
theorem descent_iff_bounded_selection (F : InstanceFamily)
    [alg : GradedObservableAlgebra F] (g n : Nat) :
    Nonempty (DescentWitness F g n) ↔
    ∃ (B : ObservableBasis F g n),
      ∃ (sf : SelectionFunction F n (Fin B.width → Nat)),
        sf.extract = B.observe := by
  constructor
  · rintro ⟨dw⟩
    exact ⟨dw.basis, descentWitness_to_selection F dw, rfl⟩
  · rintro ⟨B, sf, h_ext⟩
    exact ⟨selection_to_descentWitness F B sf h_ext⟩

/-! ## Seven-Projection Table

The quotient/descent structure appears in seven mathematical
frameworks. Each row is a different "projection" of the same
underlying phenomenon: the solution bundle and its sections.

| Framework     | Forward (eq3 side)          | Backward (eq4 side)           |
|---------------|----------------------------|-------------------------------|
| Reflexive     | fold . unfold = id         | unfold . fold = selfApp       |
| Complexity    | poly verification          | poly witness-finding          |
| Crypto        | poly encryption            | poly decryption               |
| Info theory   | Shannon capacity           | computational mutual info     |
| Quotient      | section exists             | section descends              |
| Logical       | not-not-exists w           | exists w findable             |
| Linear logic  | ! free (structural)        | ! costs (resource-tracked)    |

Each row has the SAME structure:
- The forward direction is "easy" / structural / always available.
- The backward direction is "hard" / computational / conditionally available.
- The gap between them IS the complexity-theoretic content.

We formalize this as a record documenting which projections
a given instance family + basis pair exhibits. -/

/-- A projection pair: a forward property (always or cheaply available)
    and a backward property (conditionally available, expensive). -/
structure ProjectionPair (F : InstanceFamily) (n : Nat) where
  /-- The forward property holds (e.g., verification is efficient) -/
  forward : Prop
  /-- The backward property holds (e.g., witness-finding is efficient) -/
  backward : Prop
  /-- Forward is necessary for backward -/
  h_necessary : backward → forward

/-- The quotient projection: section existence vs section descent.
    Forward: a solver exists (section of solution bundle).
    Backward: the solver descends through a grade-g basis. -/
def quotientProjection (F : InstanceFamily)
    [alg : GradedObservableAlgebra F] (g n : Nat)
    (_h_solvable : Nonempty (Solver F n)) : ProjectionPair F n where
  forward := Nonempty (Solver F n)
  backward := Nonempty (DescentWitness F g n)
  h_necessary := fun ⟨dw⟩ => ⟨{
    select := fun φ => dw.decode (dw.basis.observe φ)
    h_sound := dw.h_sound
  }⟩

/-- The logical projection: double-negation existence vs constructive existence.
    Forward: for each satisfiable instance, it is not the case that no witness works.
    Backward: we can actually produce a witness (a solver exists). -/
def logicalProjection (F : InstanceFamily) (n : Nat) :
    ProjectionPair F n where
  forward := ∀ (φ : F.X n), F.Satisfiable n φ →
    ¬¬ (∃ w, F.Sat n φ w)
  backward := Nonempty (Solver F n)
  h_necessary := fun ⟨s⟩ => fun φ hsat hnn =>
    hnn ⟨s.select φ, s.h_sound φ hsat⟩

/-- The channel projection: having any selection function vs having one
    that factors through a grade-g basis. Forward: a selection function
    exists (trivially, with Profile = X n). Backward: one exists whose
    extraction is a grade-g basis observation. -/
def channelProjection (F : InstanceFamily)
    [alg : GradedObservableAlgebra F] (g n : Nat)
    (_h_solvable : Nonempty (Solver F n)) : ProjectionPair F n where
  forward := ∃ (Profile : Type), Nonempty (SelectionFunction F n Profile)
  backward := Nonempty (DescentWitness F g n)
  h_necessary := fun ⟨dw⟩ =>
    ⟨Fin dw.basis.width → Nat, ⟨descentWitness_to_selection F dw⟩⟩
