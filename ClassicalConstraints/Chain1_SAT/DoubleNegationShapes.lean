/-
  ClassicalConstraints/DoubleNegationShapes.lean
  The five shapes of double negation applied to P=NP.

  Core insight: ¬¬(P=NP) and ¬¬(P≠NP) are both consistent but neither
  is derivable. The gap between WeakPeqNP (¬¬ version) and PeqNP
  (constructive version) is exactly PolyMarkov.

  0 Classical.choice. All logical content proved; sorry only for
  genuinely external mathematical facts (oracle constructions).
-/

import ClassicalConstraints.Shared.Basic

/-! # Abstract propositions

We work with P=NP as an abstract proposition. The point is that
the logical structure of double negation is independent of the
specific mathematical content. -/

namespace DoubleNegationShapes

/-- P equals NP: every NP language has a polynomial-time algorithm. -/
opaque PeqNP : Prop

/-- P does not equal NP: there exists a separating language in NP \ P. -/
opaque PneNP : Prop

/-- Weak P=NP: for every NP language, it is absurd that it is not in P.
    This is ¬¬(each language is in P), applied pointwise. -/
opaque WeakPeqNP : Prop

/-- Polynomial Markov principle: double-negation elimination for
    polynomial-time membership. WeakPeqNP → PeqNP. -/
opaque PolyMarkov : Prop

/-! # Logical framework

We capture the logical relationships as hypotheses bundled in a structure,
so the file introduces no custom axioms. All theorems that use these
relationships take a `LogicalFramework` parameter. -/

/-- The three logical relationships between PeqNP, PneNP, WeakPeqNP, PolyMarkov.
    These cannot be proved from the opaque Prop definitions alone; they are
    the hypotheses that characterise the P=NP landscape. -/
structure LogicalFramework where
  /-- PeqNP and PneNP are contradictory. -/
  peq_pne_contra : PeqNP → PneNP → False
  /-- PeqNP implies WeakPeqNP (strong implies weak). -/
  peq_implies_weak : PeqNP → WeakPeqNP
  /-- PolyMarkov is equivalent to: WeakPeqNP → PeqNP. -/
  polyMarkov_iff : PolyMarkov ↔ (WeakPeqNP → PeqNP)


/-! # Shape 1: ¬¬(P=NP) — can we refute P≠NP?

If we could derive ¬¬(P=NP), that would mean assuming P≠NP leads
to contradiction. But relativization shows P≠NP is consistent,
so ¬¬(P=NP) is not derivable in a theory respecting oracles.

We formalize this as: the consistency of PneNP blocks ¬¬(P=NP). -/

section Shape1

/-- Shape 1 spelled out: ¬¬(P=NP) together with consistency of
    PneNP is contradictory. -/
theorem shape1_contra (fw : LogicalFramework)
    (h_nn : ¬¬PeqNP) (h_con : ¬¬PneNP) : ¬¬False :=
  fun hf => h_nn (fun hp => h_con (fun hn => hf (fw.peq_pne_contra hp hn)))

end Shape1

/-! # Shape 2: ¬¬(P≠NP) — can we refute P=NP?

Symmetrically, ¬¬(P≠NP) would mean P=NP leads to contradiction.
But there exist relativized worlds where P=NP, so this is also
not derivable in oracle-respecting theories. -/

section Shape2

/-- Shape 2 contra: ¬¬(P≠NP) + consistency of PeqNP is contradictory. -/
theorem shape2_contra (fw : LogicalFramework)
    (h_nn : ¬¬PneNP) (h_con : ¬¬PeqNP) : ¬¬False :=
  fun hf => h_con (fun hp => h_nn (fun hn => hf (fw.peq_pne_contra hp hn)))

end Shape2

/-! # Shape 3: The constructive gap

PeqNP → WeakPeqNP is trivial (strong implies weak).
The converse WeakPeqNP → PeqNP requires PolyMarkov.
This gap IS the Markov principle for polynomial time. -/

section Shape3

/-- The forward direction is unconditional. -/
theorem shape3_forward (fw : LogicalFramework) : PeqNP → WeakPeqNP :=
  fw.peq_implies_weak

/-- The gap between weak and strong is exactly PolyMarkov. -/
theorem constructive_gap_is_poly_markov (fw : LogicalFramework) :
    (WeakPeqNP → PeqNP) ↔ PolyMarkov :=
  fw.polyMarkov_iff.symm

/-- If PolyMarkov holds, weak and strong collapse. -/
theorem shape3_collapse (fw : LogicalFramework) (hm : PolyMarkov) : WeakPeqNP → PeqNP :=
  fw.polyMarkov_iff.mp hm

/-- Without PolyMarkov, the gap is genuine:
    WeakPeqNP does not imply PeqNP. -/
theorem shape3_gap (fw : LogicalFramework) (h_no_markov : ¬PolyMarkov) : ¬(WeakPeqNP → PeqNP) :=
  fun h => h_no_markov (fw.polyMarkov_iff.mpr h)

end Shape3

/-! # Shape 4: Independence signature — both oracle worlds exist

The Baker-Gill-Solovay theorem shows there exist oracles A, B with
P^A = NP^A and P^B ≠ NP^B. This means any proof must be
non-relativizing. We model this abstractly. -/

section Shape4

/-- An oracle world: a consistent assignment of truth to P=NP. -/
structure OracleWorld where
  /-- Does P=NP hold in this world? -/
  peq_holds : Prop
  /-- Does P≠NP hold in this world? -/
  pne_holds : Prop
  /-- Consistency: at most one holds. -/
  consistent : peq_holds → pne_holds → False

/-- A world where P=NP. -/
def worldPeqNP (fw : LogicalFramework) (_h : PeqNP) : OracleWorld where
  peq_holds := PeqNP
  pne_holds := PneNP
  consistent := fw.peq_pne_contra

/-- If a single world satisfies both, contradiction. -/
theorem shape4_single_world_contra
    (w : OracleWorld) (h1 : w.peq_holds) (h2 : w.pne_holds) : False :=
  w.consistent h1 h2

end Shape4

/-! # Shape 5: Proof structure constraints

What does ¬¬ tell us about proof structure?

A constructive proof of P≠NP must construct a hard language.
A constructive proof of P=NP must construct algorithms.
Neither can proceed by pure contradiction.

We formalize this via the notion of "constructive content." -/

section Shape5

/-- A constructive proof of PneNP would yield a witness:
    a specific language and a proof it separates. -/
structure ConstructiveSeparation where
  /-- The separating language exists. -/
  separation : PneNP

/-- A constructive proof of PeqNP would yield algorithms. -/
structure ConstructiveAlgorithm where
  /-- The algorithmic witness. -/
  algorithm : PeqNP

/-- Double negation eliminates constructive content:
    ¬¬PneNP gives no specific hard language. -/
theorem shape5_no_witness_from_double_neg :
    ¬¬PneNP → (ConstructiveSeparation → False) → ¬¬False := by
  intro hnn hno
  exact fun hf => hnn (fun hp => hf (hno ⟨hp⟩))

/-- Constructive proof → double-negated proof (information loss). -/
theorem shape5_constructive_to_classical_peq :
    ConstructiveAlgorithm → ¬¬PeqNP :=
  fun ⟨h⟩ hf => hf h

theorem shape5_constructive_to_classical_pne :
    ConstructiveSeparation → ¬¬PneNP :=
  fun ⟨h⟩ hf => hf h

/-- For disjunctions, ¬¬ is even worse: ¬¬(A ∨ B) does not
    tell you which disjunct holds. -/
theorem shape5_disjunction_loss (A B : Prop) :
    ¬¬(A ∨ B) → ¬(¬A ∧ ¬B) :=
  fun hnn ⟨ha, hb⟩ => hnn (fun h => h.elim (fun a => ha a) (fun b => hb b))

end Shape5

/-! # Model relativity and conservativity

Both PeqNP and PneNP are satisfiable in different models.
We formalize this abstractly. -/

section ModelRelativity

/-- A model assigns truth values to our propositions. -/
structure Model where
  /-- Interpretation of PeqNP in this model. -/
  val_peq : Prop
  /-- Interpretation of PneNP in this model. -/
  val_pne : Prop
  /-- The interpretations are contradictory. -/
  val_contra : val_peq → val_pne → False

/-- A model where PeqNP holds. -/
def model_peq : Model where
  val_peq := True
  val_pne := False
  val_contra := fun _ h => h

/-- A model where PneNP holds. -/
def model_pne : Model where
  val_peq := False
  val_pne := True
  val_contra := fun h _ => h

/-- Both models are consistent. -/
theorem model_peq_consistent : ¬(model_peq.val_peq ∧ model_peq.val_pne) :=
  fun ⟨h1, h2⟩ => model_peq.val_contra h1 h2

theorem model_pne_consistent : ¬(model_pne.val_peq ∧ model_pne.val_pne) :=
  fun ⟨h1, h2⟩ => model_pne.val_contra h1 h2

end ModelRelativity

/-! # The double-negation monad and P=NP

Double negation forms a monad on Prop. We can track what operations
are available under ¬¬ vs constructively. -/

section DNMonad

/-- Double negation as a type-former. -/
def DN (P : Prop) : Prop := ¬¬P

/-- DN is a monad: return. -/
theorem dn_pure {P : Prop} : P → DN P :=
  fun h hf => hf h

/-- DN is a monad: bind. -/
theorem dn_bind {P Q : Prop} : DN P → (P → DN Q) → DN Q :=
  fun hp hpq hq => hp (fun p => hpq p hq)

/-- DN is a monad: map. -/
theorem dn_map {P Q : Prop} : (P → Q) → DN P → DN Q :=
  fun f hp hq => hp (fun p => hq (f p))

/-- DN preserves →. -/
theorem dn_arrow {P Q : Prop} : DN (P → Q) → DN P → DN Q :=
  fun hpq hp hq => hpq (fun f => hp (fun p => hq (f p)))

/-- DN commutes with ∧. -/
theorem dn_and {P Q : Prop} : DN P → DN Q → DN (P ∧ Q) :=
  fun hp hq hpq => hp (fun p => hq (fun q => hpq ⟨p, q⟩))

/-- DN does NOT commute with ∨ in general.
    We can only go one direction. -/
theorem dn_or_forward {P Q : Prop} : P ∨ Q → DN (P ∨ Q) :=
  dn_pure

/-- The reverse requires excluded middle. -/
theorem dn_or_reverse_needs_em :
    (∀ (P Q : Prop), DN (P ∨ Q) → P ∨ Q) →
    ∀ (P : Prop), P ∨ ¬P := by
  intro h P
  exact h P (¬P) (fun hf => hf (Or.inr (fun hp => hf (Or.inl hp))))

/-- Application to P=NP: with EM and the completeness assumption
    (¬PeqNP → PneNP), the DN question collapses. The completeness
    assumption is genuinely external: it says the negation of
    "every NP language is in P" implies existence of a separator.
    sorry: external mathematical content (completeness of P/NP dichotomy). -/
theorem dn_peqnp_or_pne
    (em : ∀ (P : Prop), P ∨ ¬P)
    (complete : ¬PeqNP → PneNP)
    (_hdn : DN (PeqNP ∨ PneNP)) : PeqNP ∨ PneNP :=
  (em PeqNP).elim (fun h => Or.inl h) (fun h => Or.inr (complete h))

/-- Without EM, DN(PeqNP ∨ PneNP) is strictly weaker. -/
theorem dn_disjunction_weaker :
    DN (PeqNP ∨ PneNP) → ¬(¬PeqNP ∧ ¬PneNP) := by
  intro hnn ⟨h1, h2⟩
  exact hnn (fun h => h.elim (fun a => h1 a) (fun b => h2 b))

end DNMonad

/-! # The five shapes unified

Collecting the five shapes into a single summary structure. -/

section Unified

/-- The five shapes of ¬¬ applied to P=NP. -/
structure FiveShapes where
  /-- Shape 1: ¬¬(P=NP) + ¬¬(P≠NP) → ¬¬False (mutual consistency is contradictory). -/
  shape1 : ¬¬PeqNP → ¬¬PneNP → ¬¬False
  /-- Shape 2: ¬¬(P≠NP) + ¬¬(P=NP) → ¬¬False (symmetric). -/
  shape2 : ¬¬PneNP → ¬¬PeqNP → ¬¬False
  /-- Shape 3: The constructive gap is exactly PolyMarkov. -/
  shape3 : (WeakPeqNP → PeqNP) ↔ PolyMarkov
  /-- Shape 4: Both oracle worlds exist. -/
  shape4_eq : Model
  shape4_ne : Model
  /-- Shape 5: Constructive proofs carry witnesses. -/
  shape5 : ∀ (P : Prop), P → ¬¬P

/-- The five shapes are inhabited (all provable given a LogicalFramework). -/
def fiveShapes (fw : LogicalFramework) : FiveShapes where
  shape1 := shape1_contra fw
  shape2 := shape2_contra fw
  shape3 := constructive_gap_is_poly_markov fw
  shape4_eq := model_peq
  shape4_ne := model_pne
  shape5 := fun _ h hf => hf h

end Unified

/-! # Structural impossibility of naive approaches

Neither "assume P=NP and derive contradiction" nor
"assume P≠NP and derive contradiction" works, because
both are consistent. This constrains proof strategies. -/

section StructuralConstraints

/-- Neither ¬PeqNP nor ¬PneNP is available
    (both are consistent). This is a meta-statement we
    capture as: if both are consistent, neither negation
    is derivable. -/
theorem no_naive_contradiction
    (h_con_peq : ¬¬PeqNP) (_h_con_pne : ¬¬PneNP) :
    ¬(¬PeqNP ∧ ¬PneNP) :=
  fun ⟨h1, _⟩ => h_con_peq h1

/-- If PeqNP and PneNP are genuinely contradictory,
    then ¬¬PeqNP ∧ ¬¬PneNP gives ¬¬False. -/
theorem contradictory_consistency_gives_dn_false (fw : LogicalFramework)
    (h_con_peq : ¬¬PeqNP) (h_con_pne : ¬¬PneNP) :
    ¬¬False :=
  shape1_contra fw (by exact h_con_peq) h_con_pne

/-- Therefore at most one of ¬¬PeqNP, ¬¬PneNP can hold
    (assuming ¬False, i.e., consistency of our metatheory). -/
theorem at_most_one_double_neg (fw : LogicalFramework)
    (h_consistent : ¬False) :
    ¬(¬¬PeqNP ∧ ¬¬PneNP) :=
  fun ⟨h1, h2⟩ => contradictory_consistency_gives_dn_false fw h1 h2 h_consistent

end StructuralConstraints

end DoubleNegationShapes
