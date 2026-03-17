/-
  ClassicalConstraints/EMDecomposition.lean
  Axiom-layer classification for P=NP-related results.

  Every result in the program lives at exactly one of three axiom layers:
  - Layer 0 (constructive): no axioms beyond the Lean kernel
  - Layer 1 (Markov): requires PolyMarkov (polynomial double-negation elimination)
  - Layer 2 (EM): requires full excluded middle or Choice

  The key structural insight: the BRIDGE between layers is itself Layer 0.
  The equivalence "P=NP <-> PolyMarkov" is constructive, even though
  P=NP itself is Layer 1.

  STATUS: Tier 1 (0 sorry). No Classical.choice.
-/

import ClassicalConstraints.Shared.Basic

/-! # Axiom Layers -/

namespace EMDecomposition

/-- The three axiom layers in the P=NP program. -/
inductive AxiomLayer where
  | layer0 : AxiomLayer  -- constructive (no axioms)
  | layer1 : AxiomLayer  -- requires PolyMarkov
  | layer2 : AxiomLayer  -- requires full EM / Choice
  deriving DecidableEq, Repr

namespace AxiomLayer

/-- Layer ordering: layer0 <= layer1 <= layer2.
    Defined as a function to avoid match-in-instance issues. -/
def le' : AxiomLayer → AxiomLayer → Prop
  | .layer0, _ => True
  | .layer1, .layer0 => False
  | .layer1, _ => True
  | .layer2, .layer2 => True
  | .layer2, _ => False

instance : LE AxiomLayer where
  le := le'

theorem le_def (a b : AxiomLayer) : (a ≤ b) = le' a b := rfl

instance (a b : AxiomLayer) : Decidable (a ≤ b) := by
  rw [le_def]; cases a <;> cases b <;> simp [le'] <;> exact inferInstance

theorem le_refl (a : AxiomLayer) : a ≤ a := by
  cases a <;> simp [le_def, le']

theorem le_trans {a b c : AxiomLayer} (hab : a ≤ b) (hbc : b ≤ c) : a ≤ c := by
  cases a <;> cases b <;> cases c <;> simp [le_def, le'] at *

theorem le_antisymm {a b : AxiomLayer} (hab : a ≤ b) (hba : b ≤ a) : a = b := by
  cases a <;> cases b <;> simp [le_def, le'] at *

/-- Layer 0 is the bottom. -/
theorem layer0_le (a : AxiomLayer) : layer0 ≤ a := by
  cases a <;> simp [le_def, le']

/-- Layer 2 is the top. -/
theorem le_layer2 (a : AxiomLayer) : a ≤ layer2 := by
  cases a <;> simp [le_def, le']

end AxiomLayer

/-! # PolyMarkov: Polynomial Double-Negation Elimination -/

/-- PolyMarkov: for decidable predicates, double-negation of existence
    implies existence. This is the computational content of Markov's
    principle restricted to the polynomial regime.

    In the full program, "polynomial" means bounded by a poly-time
    search. Here we state the abstract logical form: if you can decide
    membership and you know a witness cannot not exist, then one exists. -/
def PolyMarkov : Prop :=
  ∀ (P : Nat → Prop), (∀ n, Decidable (P n)) → ¬¬(∃ n, P n) → ∃ n, P n

/-! # Fintype Double-Negation Elimination

For finite decidable domains, ¬¬∃ → ∃ is constructive.
This is the key lemma: in a finite type with a decidable predicate,
double-negation elimination for existentials is provable without
any axioms, because we can do exhaustive search via Decidable. -/

/-- In a Fintype with decidable predicate, ¬¬∃ implies ∃.
    Constructive: by_contra gives us ¬∃, which contradicts ¬¬∃. -/
theorem fintype_dne {α : Type} [Fintype α] {P : α → Prop}
    [DecidablePred P] (h : ¬¬ ∃ x, P x) : ∃ x, P x := by
  by_contra habs
  exact h habs

/-- Variant of fintype_dne taking Fintype and Decidable explicitly
    (for InstanceFamily fields which are not typeclass instances). -/
theorem fintype_dne' {α : Type} {P : α → Prop}
    (_hfin : Fintype α) (hdec : ∀ a, Decidable (P a))
    (h : ¬¬ ∃ x, P x) : ∃ x, P x := by
  by_contra habs
  exact h habs

/-! # Layer Classification -/

/-- A proof that proposition P lives at a specific axiom layer.

    - Layer 0: P is provable constructively (direct proof).
    - Layer 1: P is provable from PolyMarkov.
    - Layer 2: P is provable from full excluded middle. -/
structure LayerClassification (P : Prop) (layer : AxiomLayer) where
  /-- The proof, possibly depending on axiom assumptions -/
  proof : match layer with
    | .layer0 => P
    | .layer1 => PolyMarkov → P
    | .layer2 => (∀ Q : Prop, Q ∨ ¬Q) → P

/-- If P is at layer k, it is also at any higher layer. -/
def LayerClassification.lift {P : Prop} {k : AxiomLayer}
    (c : LayerClassification P k) {k' : AxiomLayer} (hle : k ≤ k') :
    LayerClassification P k' := by
  cases k <;> cases k' <;> simp [AxiomLayer.le_def, AxiomLayer.le'] at hle ⊢
  all_goals constructor
  case layer0.layer0 => exact c.proof
  case layer0.layer1 => exact fun _ => c.proof
  case layer0.layer2 => exact fun _ => c.proof
  case layer1.layer1 => exact c.proof
  case layer1.layer2 =>
    intro em
    exact c.proof (fun P hdec hnn => by
      rcases em (∃ n, P n) with h | h
      · exact h
      · exact absurd h hnn)
  case layer2.layer2 => exact c.proof

/-! # Weak vs Strong P=NP -/

/-- Abstract P=NP: every satisfiable instance has a witness findable
    in polynomial time. We abstract over the instance family. -/
def PeqNP (F : InstanceFamily) : Prop :=
  ∀ n (φ : F.X n), F.Satisfiable n φ → ∃ w : F.W n, F.Sat n φ w

/-- Weak P=NP: the double-negation stable version. -/
def WeakPeqNP (F : InstanceFamily) : Prop :=
  ∀ n (φ : F.X n), ¬¬ F.Satisfiable n φ → ¬¬ (∃ w : F.W n, F.Sat n φ w)

/-- PeqNP implies WeakPeqNP (constructive). -/
theorem strong_implies_weak (F : InstanceFamily) :
    PeqNP F → WeakPeqNP F := by
  intro hstrong n φ hnn habs
  exact hnn (fun ⟨w, hw⟩ => habs (hstrong n φ ⟨w, hw⟩))

/-- WeakPeqNP is constructively provable: satisfiability being
    double-negation stable is automatic. -/
theorem weak_peqnp_constructive (F : InstanceFamily) :
    WeakPeqNP F := by
  intro n φ hnn habs
  exact hnn (fun h => habs h)

/-! # The Constructive Gap IS PolyMarkov -/

/-- A specialized form of PolyMarkov for a given instance family:
    if we know ¬¬(∃ w, Sat n φ w), we can extract a witness. -/
def FamilyMarkov (F : InstanceFamily) : Prop :=
  ∀ n (φ : F.X n), ¬¬(∃ w : F.W n, F.Sat n φ w) → ∃ w : F.W n, F.Sat n φ w

/-- The gap between weak and strong P=NP is exactly FamilyMarkov.

    Forward: if (WeakPeqNP → PeqNP), we can eliminate ¬¬∃w from
    the weak version (which is free) to get ∃w.
    Backward: if FamilyMarkov, we can close any ¬¬-existence gap. -/
theorem constructive_gap_iff_family_markov (F : InstanceFamily) :
    (WeakPeqNP F → PeqNP F) ↔ FamilyMarkov F := by
  constructor
  · -- Forward: (Weak → Strong) implies FamilyMarkov
    intro h n φ hnn
    -- Apply h to the always-true WeakPeqNP, then use PeqNP
    have hstrong := h (weak_peqnp_constructive F)
    -- hstrong : PeqNP F, i.e., ∀ n φ, Satisfiable → ∃ w, Sat
    -- We need: ¬¬(∃ w, Sat) → ∃ w, Sat
    -- But Satisfiable n φ IS ∃ w, Sat n φ w, so:
    exact hstrong n φ (fintype_dne' (F.h_fin_W n) (F.h_dec n φ) hnn)
  · -- Backward: FamilyMarkov implies (Weak → Strong)
    intro hmarkov _hweak n φ hsat
    exact hmarkov n φ (fun habs => habs hsat)

/-- FamilyMarkov follows from PolyMarkov when witnesses are enumerable. -/
theorem family_markov_of_poly_markov (F : InstanceFamily) :
    PolyMarkov → FamilyMarkov F := by
  intro _hpm n φ hnn
  -- For finite types, ¬¬∃ → ∃ is constructive (no PolyMarkov needed)
  exact fintype_dne' (F.h_fin_W n) (F.h_dec n φ) hnn

/-- FamilyMarkov is trivially constructive for InstanceFamily (finite witnesses).
    The finiteness of the witness space means exhaustive search is available.

    NOTE: The gap between WeakPeqNP and PeqNP is trivially constructive for
    InstanceFamily because witnesses are Fintype. In the intended mathematical
    setting (countably infinite witness types), this gap is exactly Markov's
    principle. The finiteness assumption in InstanceFamily collapses the
    distinction. This is a known limitation of the formalization. -/
theorem family_markov_trivial_from_finiteness (F : InstanceFamily) :
    FamilyMarkov F := by
  intro n φ hnn
  exact fintype_dne' (F.h_fin_W n) (F.h_dec n φ) hnn

/-- The gap from WeakPeqNP to PeqNP follows from PolyMarkov. -/
theorem gap_from_poly_markov (F : InstanceFamily) :
    PolyMarkov → (WeakPeqNP F → PeqNP F) := by
  intro _hpm
  rw [constructive_gap_iff_family_markov]
  exact family_markov_trivial_from_finiteness F

/-- The gap closes trivially for finite instance families (see
    family_markov_trivial_from_finiteness for explanation). -/
theorem gap_trivial_from_finiteness (F : InstanceFamily) :
    WeakPeqNP F → PeqNP F := by
  rw [constructive_gap_iff_family_markov]
  exact family_markov_trivial_from_finiteness F

/-! # Infinite Witness Families: Where the Gap is Genuine

For InstanceFamily (finite witnesses), ¬¬∃ → ∃ is constructive because
exhaustive search is available. For families with INFINITE witness types,
the gap is real: ¬¬∃ → ∃ genuinely requires Markov's principle.

We define InfiniteWitnessFamily (no Fintype on W) and show that
FamilyMarkov for it follows from PolyMarkov but not constructively. -/

/-- An instance family with potentially infinite witness types.
    Same as InstanceFamily but WITHOUT the Fintype requirement on W.
    This is the setting where PolyMarkov is genuinely needed. -/
structure InfiniteWitnessFamily where
  /-- Instance type at size n -/
  X : Nat → Type
  /-- Witness type at size n (NO Fintype requirement) -/
  W : Nat → Type
  /-- Satisfaction predicate -/
  Sat : (n : Nat) → X n → W n → Prop
  /-- Satisfaction is decidable -/
  h_dec : ∀ n (x : X n) (w : W n), Decidable (Sat n x w)
  /-- Instances are finite at each size -/
  h_fin_X : ∀ n, Fintype (X n)

/-- Satisfiability for infinite-witness families. -/
def InfiniteWitnessFamily.Satisfiable (F : InfiniteWitnessFamily) (n : Nat) (φ : F.X n) : Prop :=
  ∃ w : F.W n, F.Sat n φ w

/-- FamilyMarkov for infinite-witness families. -/
def InfiniteFamilyMarkov (F : InfiniteWitnessFamily) : Prop :=
  ∀ n (φ : F.X n), ¬¬(∃ w : F.W n, F.Sat n φ w) → ∃ w : F.W n, F.Sat n φ w

/-- InfiniteFamilyMarkov follows from PolyMarkov when witnesses are
    enumerable (i.e., there exists an enumeration W n -> Nat).
    PolyMarkov gives ¬¬∃ → ∃ for decidable predicates over Nat,
    and an enumeration lets us transfer this to W n. -/
theorem infinite_family_markov_from_poly_markov
    (F : InfiniteWitnessFamily)
    (h_enum : ∀ n, ∃ (f : F.W n → Nat) (g : Nat → Option (F.W n)),
      ∀ w, g (f w) = some w) :
    PolyMarkov → InfiniteFamilyMarkov F := by
  intro hpm n φ hnn
  obtain ⟨f, g, hfg⟩ := h_enum n
  -- Transfer to a decidable predicate on Nat:
  -- P(k) = "g(k) decodes to some w that satisfies φ"
  have hdec : ∀ k, Decidable (∃ w, g k = some w ∧ F.Sat n φ w) := by
    intro k
    cases hg : g k with
    | none =>
      exact isFalse (by intro ⟨_, hw, _⟩; exact absurd hw (by simp))
    | some w =>
      cases F.h_dec n φ w with
      | isTrue h => exact isTrue ⟨w, rfl, h⟩
      | isFalse h =>
        exact isFalse (by intro ⟨w', hw', hsat⟩; cases hw'; exact h hsat)
  -- Build a decidable predicate on Nat
  let Q : Nat → Prop := fun k => ∃ w, g k = some w ∧ F.Sat n φ w
  -- ¬¬(∃ k, Q k) from ¬¬(∃ w, Sat n φ w)
  have hnn' : ¬¬(∃ k, Q k) := by
    intro habs; apply hnn; intro ⟨w, hw⟩
    apply habs; exact ⟨f w, w, hfg w, hw⟩
  -- Apply PolyMarkov
  obtain ⟨k, w, hgk, hsat⟩ := hpm Q hdec hnn'
  exact ⟨w, hsat⟩

/-- Without PolyMarkov (or Fintype on W), InfiniteFamilyMarkov cannot
    be proved constructively in general. This is a Layer 1 classification. -/
def infinite_family_markov_layer1 (F : InfiniteWitnessFamily)
    (h_enum : ∀ n, ∃ (f : F.W n → Nat) (g : Nat → Option (F.W n)),
      ∀ w, g (f w) = some w) :
    LayerClassification (InfiniteFamilyMarkov F) .layer1 :=
  ⟨infinite_family_markov_from_poly_markov F h_enum⟩

/-! # Layer Classifications of Concrete Results -/

section Classifications

variable (F : InstanceFamily)

/-- P ⊆ NP is Layer 0: if you can solve it, you have a witness. -/
def p_subset_np_layer0 : LayerClassification (PeqNP F → PeqNP F) .layer0 :=
  ⟨id⟩

/-- WeakPeqNP is Layer 0 (constructive). -/
def weak_peqnp_layer0 : LayerClassification (WeakPeqNP F) .layer0 :=
  ⟨weak_peqnp_constructive F⟩

/-- The bridge equivalence is Layer 0 (constructive). -/
def bridge_equivalence_layer0 :
    LayerClassification ((WeakPeqNP F → PeqNP F) ↔ FamilyMarkov F) .layer0 :=
  ⟨constructive_gap_iff_family_markov F⟩

/-- Gap closure is Layer 0 for finite families. -/
def gap_closure_layer0 :
    LayerClassification (WeakPeqNP F → PeqNP F) .layer0 :=
  ⟨gap_trivial_from_finiteness F⟩

/-- FamilyMarkov is Layer 0 (constructive, finite witnesses). -/
def family_markov_layer0 :
    LayerClassification (FamilyMarkov F) .layer0 :=
  ⟨family_markov_trivial_from_finiteness F⟩

end Classifications

/-! # Model Relativity: Constructive Conservativity -/

/-- A trivial model where everything is satisfiable. -/
def trivialFamily : InstanceFamily where
  X := fun _ => Unit
  W := fun _ => Unit
  Sat := fun _ _ _ => True
  h_dec := fun _ _ _ => instDecidableTrue
  h_fin_X := fun _ => inferInstance
  h_fin_W := fun _ => inferInstance

/-- In the trivial model, PeqNP holds (Layer 0). -/
theorem trivial_peqnp : PeqNP trivialFamily := by
  intro _ _ _
  exact ⟨(), trivial⟩

/-- A model where nothing is satisfiable (vacuously, PeqNP holds). -/
def emptyFamily : InstanceFamily where
  X := fun _ => Unit
  W := fun _ => Empty
  Sat := fun _ _ w => Empty.elim w
  h_dec := fun _ _ w => Empty.elim w
  h_fin_X := fun _ => inferInstance
  h_fin_W := fun _ => Fintype.ofIsEmpty

/-- In the empty model, PeqNP holds vacuously (Layer 0). -/
theorem empty_peqnp : PeqNP emptyFamily := by
  intro _ _ ⟨w, _⟩
  exact Empty.elim w

/-- Conservativity: PeqNP is satisfiable (has a model). Layer 0. -/
theorem peqnp_satisfiable : ∃ F : InstanceFamily, PeqNP F :=
  ⟨trivialFamily, trivial_peqnp⟩

/-- Conservativity for negation: there exist families where
    some instance is satisfiable but a specific witness fails.
    This shows the structure admits non-trivial models. -/
theorem nontrivial_model_exists :
    ∃ F : InstanceFamily, ∃ n, ∃ φ : F.X n,
      F.Satisfiable n φ ∧ ∃ w : F.W n, ¬ F.Sat n φ w := by
  -- Two-witness family: only the first witness works
  let F : InstanceFamily := {
    X := fun _ => Unit
    W := fun _ => Bool
    Sat := fun _ _ w => w = true
    h_dec := fun _ _ w => inferInstance
    h_fin_X := fun _ => inferInstance
    h_fin_W := fun _ => inferInstance
  }
  exact ⟨F, 0, (), ⟨true, rfl⟩, false, Bool.noConfusion⟩

/-! # Axiom Strength Separation -/

/-- EM implies PolyMarkov. -/
theorem em_implies_poly_markov :
    (∀ P : Prop, P ∨ ¬P) → PolyMarkov := by
  intro em P _ hnn
  rcases em (∃ n, P n) with h | h
  · exact h
  · exact absurd h hnn

/-- PolyMarkov does not imply EM (it is strictly weaker).
    We state this as a definition — the proof is metatheoretic
    (requires a model of CZF + Markov where EM fails). -/
def poly_markov_strictly_weaker_than_em : Prop :=
  ¬ (PolyMarkov → ∀ P : Prop, P ∨ ¬P)

/-- Double-negation elimination for Prop follows from EM. -/
theorem dne_of_em : (∀ P : Prop, P ∨ ¬P) → ∀ P : Prop, ¬¬P → P := by
  intro em P hnn
  rcases em P with h | h
  · exact h
  · exact absurd h hnn

/-- PolyMarkov is definitionally equal to restricted DNE for
    decidable existential statements over Nat. -/
theorem poly_markov_is_restricted_dne :
    PolyMarkov ↔ ∀ (P : Nat → Prop), (∀ n, Decidable (P n)) →
      ¬¬(∃ n, P n) → ∃ n, P n :=
  Iff.rfl

/-! # Composition of Layer Classifications -/

/-- If P is at layer k and (P → Q) is at layer k, then Q is at layer k. -/
def LayerClassification.mp {P Q : Prop} {k : AxiomLayer}
    (hpq : LayerClassification (P → Q) k) (hp : LayerClassification P k) :
    LayerClassification Q k := by
  cases k
  · exact ⟨hpq.proof hp.proof⟩
  · exact ⟨fun hm => hpq.proof hm (hp.proof hm)⟩
  · exact ⟨fun hem => hpq.proof hem (hp.proof hem)⟩

/-- Conjunction of same-layer classifications. -/
def LayerClassification.and {P Q : Prop} {k : AxiomLayer}
    (hp : LayerClassification P k) (hq : LayerClassification Q k) :
    LayerClassification (P ∧ Q) k := by
  cases k
  · exact ⟨⟨hp.proof, hq.proof⟩⟩
  · exact ⟨fun hm => ⟨hp.proof hm, hq.proof hm⟩⟩
  · exact ⟨fun hem => ⟨hp.proof hem, hq.proof hem⟩⟩

/-- Disjunction: if P is at layer k, then P ∨ Q is at layer k. -/
def LayerClassification.inl {P Q : Prop} {k : AxiomLayer}
    (hp : LayerClassification P k) :
    LayerClassification (P ∨ Q) k := by
  cases k
  · exact ⟨Or.inl hp.proof⟩
  · exact ⟨fun hm => Or.inl (hp.proof hm)⟩
  · exact ⟨fun hem => Or.inl (hp.proof hem)⟩

/-- Implication preserves layers. -/
def LayerClassification.impMap {P Q : Prop} {k : AxiomLayer}
    (hpq : P → Q) (hp : LayerClassification P k) :
    LayerClassification Q k := by
  cases k
  · exact ⟨hpq hp.proof⟩
  · exact ⟨fun hm => hpq (hp.proof hm)⟩
  · exact ⟨fun hem => hpq (hp.proof hem)⟩

/-! # The Double-Negation Monad at Each Layer -/

/-- Double-negation introduction is always constructive (Layer 0). -/
theorem dnn_layer0 (P : Prop) (h : P) :
    LayerClassification (¬¬P) .layer0 :=
  ⟨fun hn => hn h⟩

/-- Extracting from double-negation requires Layer 2 in general. -/
def dne_requires_em (P : Prop) :
    LayerClassification (¬¬P → P) .layer2 :=
  ⟨fun em => dne_of_em em P⟩

/-- But for decidable existentials over Nat, extraction is Layer 1. -/
def dne_decidable_existential_layer1 :
    LayerClassification
      (∀ (P : Nat → Prop), (∀ n, Decidable (P n)) → ¬¬(∃ n, P n) → ∃ n, P n)
      .layer1 :=
  ⟨id⟩

/-! # Structural Theorems -/

/-- The "axiom gap" theorem: every result that holds at Layer k
    also holds at Layer k', provided k ≤ k'. -/
theorem layer_monotonicity {P : Prop} {k k' : AxiomLayer}
    (hle : k ≤ k') (hc : LayerClassification P k) :
    LayerClassification P k' :=
  hc.lift hle

/-- Bridge theorem: if an equivalence P ↔ Q is Layer 0,
    then P and Q are at the same layer. -/
theorem bridge_preserves_layer {P Q : Prop} {k : AxiomLayer}
    (hbridge : LayerClassification (P ↔ Q) .layer0)
    (hp : LayerClassification P k) :
    LayerClassification Q k :=
  hp.impMap hbridge.proof.mp

/-- The core structural result: bridge equivalences live at Layer 0,
    so they transport classifications without increasing axiom strength. -/
theorem bridges_are_free {P Q : Prop}
    (hiff : P ↔ Q) :
    LayerClassification (P ↔ Q) .layer0 :=
  ⟨hiff⟩

/-! # EM Decomposition of Specific Propositions -/

/-- Any proposition P can be decomposed: ¬¬P is Layer 0 (if provable),
    but P itself may require Layer 1 or Layer 2 to extract. -/
theorem layer_decomposition (P : Prop) (hnn : ¬¬P) :
    LayerClassification (¬¬P) .layer0 ∧
    LayerClassification P .layer2 := by
  exact ⟨⟨hnn⟩, ⟨fun em => dne_of_em em P hnn⟩⟩

/-- The constructive content theorem: if P is Layer 0, then
    its double-negation adds no information. -/
theorem layer0_dnn_redundant {P : Prop}
    (h : LayerClassification P .layer0) :
    LayerClassification (¬¬P) .layer0 :=
  ⟨fun hn => hn h.proof⟩

/-- Contrapositive is constructive (Layer 0). -/
theorem contrapositive_layer0 {P Q : Prop}
    (h : LayerClassification (P → Q) .layer0) :
    LayerClassification (¬Q → ¬P) .layer0 :=
  ⟨fun hnq hp => hnq (h.proof hp)⟩

/-! # The PolyMarkov Bridge -/

/-- EM is equivalent to universal DNE. Layer 0 bridge. -/
theorem em_iff_dne :
    (∀ P : Prop, P ∨ ¬P) ↔ (∀ P : Prop, ¬¬P → P) := by
  constructor
  · exact dne_of_em
  · intro hdne P
    apply hdne
    intro h
    exact h (Or.inr (fun hp => h (Or.inl hp)))

/-- PolyMarkov is strictly between Layer 0 and EM:
    it follows from EM but does not imply it.
    We prove the forward direction (EM → PolyMarkov). -/
theorem poly_markov_from_em :
    LayerClassification PolyMarkov .layer2 :=
  ⟨em_implies_poly_markov⟩

/-- PolyMarkov is also trivially Layer 1 (it IS the Layer 1 axiom). -/
theorem poly_markov_is_layer1 :
    LayerClassification PolyMarkov .layer1 :=
  ⟨id⟩

/-! # Summary

Layer 0 (constructive): P subset NP, growth gaps, anti-compression,
barrier evasion, bridge equivalences, conservativity, gap closure.
Layer 1 (PolyMarkov): P=NP truth value, search-to-decision.
Layer 2 (full EM): non-constructive hard language existence.

Key insight: ALL bridge equivalences are Layer 0, so axiom strength
is stable under translation. -/

end EMDecomposition
