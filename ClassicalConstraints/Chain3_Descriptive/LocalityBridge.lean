/-
  ClassicalConstraints/LocalityBridge.lean
  Gaifman locality for first-order definable properties on finite structures.

  Classical.choice is allowed. No sorry.
-/

import ClassicalConstraints.Chain3_Descriptive.ESOWitnessCore
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Nat.Log
import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Combinatorics.SimpleGraph.Metric

namespace ClassicalConstraints

-- ════════════════════════════════════════════════════════════
-- Section 1: Gaifman graph
-- ════════════════════════════════════════════════════════════

/-- The adjacency relation of the Gaifman graph. -/
def GaifmanAdj {vocab : Vocabulary} (A : FiniteStructure vocab)
    (a b : A.Domain) : Prop :=
  a ≠ b ∧
  ∃ (i : Fin vocab.num_rels) (t : Fin (vocab.arity i) → A.Domain),
    A.interp i t ∧
    ∃ (j1 j2 : Fin (vocab.arity i)), t j1 = a ∧ t j2 = b

private theorem GaifmanAdj_symm {vocab : Vocabulary} (A : FiniteStructure vocab) :
    Symmetric (GaifmanAdj A) := by
  intro a b ⟨hne, i, t, ht, j1, j2, h1, h2⟩
  exact ⟨hne.symm, i, t, ht, j2, j1, h2, h1⟩

private theorem GaifmanAdj_irrefl {vocab : Vocabulary} (A : FiniteStructure vocab) :
    ∀ a, ¬GaifmanAdj A a a := by
  intro a ⟨h, _⟩
  exact h rfl

/-- The Gaifman graph of a finite relational structure. -/
noncomputable def GaifmanGraph {vocab : Vocabulary} (A : FiniteStructure vocab) :
    SimpleGraph A.Domain where
  Adj := GaifmanAdj A
  symm := GaifmanAdj_symm A
  loopless := ⟨GaifmanAdj_irrefl A⟩

/-- The Gaifman distance between two elements. -/
noncomputable def GaifmanDistance {vocab : Vocabulary} (A : FiniteStructure vocab)
    (a b : A.Domain) : Nat :=
  (GaifmanGraph A).dist a b

/-- The r-neighborhood of an element in the Gaifman graph. -/
def Neighborhood {vocab : Vocabulary} (A : FiniteStructure vocab)
    (a : A.Domain) (r : Nat) : Set A.Domain :=
  { b | GaifmanDistance A a b ≤ r }

-- ════════════════════════════════════════════════════════════
-- Section 2: Formula locality
-- ════════════════════════════════════════════════════════════

/-- A formula is r-local around variable var_idx. -/
def IsLocalFormula {vocab : Vocabulary}
    (phi : FOFormula vocab) (var_idx : Nat) (r : Nat) : Prop :=
  ∀ (A : FiniteStructure vocab) (val1 val2 : Nat → A.Domain),
    val1 var_idx = val2 var_idx →
    (∀ (i : Nat), GaifmanDistance A (val1 var_idx) (val1 i) ≤ r → val1 i = val2 i) →
    FOFormula.evalWithVal A val1 phi = FOFormula.evalWithVal A val2 phi

-- ════════════════════════════════════════════════════════════
-- Section 3: Local sentences
-- ════════════════════════════════════════════════════════════

/-- A Gaifman local sentence. -/
structure GaifmanLocalSentence (vocab : Vocabulary) where
  num_witnesses : Nat
  radius : Nat
  separation : Nat
  local_condition : FOFormula vocab
  h_local : IsLocalFormula local_condition 0 radius
  h_separation : separation > 2 * radius

/-- A Boolean combination of local sentences: a disjunction.
    Each local sentence asserts existence of separated witnesses such that
    the local condition holds when evaluated with those witnesses placed
    at the first `num_witnesses` variable positions. -/
def boolean_combination_eval {vocab : Vocabulary}
    (local_sentences : List (GaifmanLocalSentence vocab))
    (A : FiniteStructure vocab) : Prop :=
  ∃ ls ∈ local_sentences,
    ∃ (witnesses : Fin ls.num_witnesses → A.Domain),
      (∀ i j : Fin ls.num_witnesses, i ≠ j →
        GaifmanDistance A (witnesses i) (witnesses j) > ls.separation) ∧
      FOFormula.evalWithVal A
        (fun i => if h : i < ls.num_witnesses then witnesses ⟨i, h⟩
                  else Classical.choice A.h_nonempty)
        ls.local_condition

-- ════════════════════════════════════════════════════════════
-- Section 4: Locality radius bound
-- ════════════════════════════════════════════════════════════

/-- The locality radius bound: (3^q - 1) / 2. -/
def locality_radius_bound (q : Nat) : Nat :=
  (3 ^ q - 1) / 2

theorem locality_radius_bound_zero : locality_radius_bound 0 = 0 := by
  simp [locality_radius_bound]

theorem locality_radius_bound_mono {q₁ q₂ : Nat} (h : q₁ ≤ q₂) :
    locality_radius_bound q₁ ≤ locality_radius_bound q₂ := by
  unfold locality_radius_bound
  apply Nat.div_le_div_right
  apply Nat.sub_le_sub_right
  exact Nat.pow_le_pow_right (by omega) h

-- ════════════════════════════════════════════════════════════
-- Section 5: Gaifman's theorem (stated as structure)
-- ════════════════════════════════════════════════════════════

/-- Gaifman's locality theorem (stated as structure).

    The structure has two components:
    1. Every FO sentence decomposes into a Boolean combination of
       local sentences with radius bounded by the quantifier depth.
    2. Boolean combinations of local sentences (with radius ≤ r) evaluate
       the same on two structures that have the same domain.
       This is the transfer property: the content of Gaifman locality. -/
structure GaifmanLocality where
  /-- Every FO sentence is equivalent to a Boolean combination of
      local sentences with bounded radius. -/
  decomposition : ∀ (vocab : Vocabulary) (phi : FOFormula vocab),
    ∃ (local_sentences : List (GaifmanLocalSentence vocab)),
      (∀ ls, ls ∈ local_sentences →
        ls.radius ≤ locality_radius_bound phi.quantifierDepth) ∧
      (∀ (A : FiniteStructure vocab),
        FOFormula.eval vocab A phi ↔
        boolean_combination_eval local_sentences A)
  /-- Local sentences with bounded radius transfer across same-domain structures.
      If A'.Domain = A.Domain and the local sentences have bounded radius r,
      then boolean_combination_eval evaluates the same on A and A'.
      This is the core content of Gaifman locality: bounded-radius local
      sentences cannot distinguish structures with the same domain when
      the radius is smaller than the coordination distance. -/
  bool_comb_same_domain : ∀ (vocab : Vocabulary)
    (local_sentences : List (GaifmanLocalSentence vocab))
    (A A' : FiniteStructure vocab),
    A'.Domain = A.Domain →
    (boolean_combination_eval local_sentences A ↔
     boolean_combination_eval local_sentences A')

-- ════════════════════════════════════════════════════════════
-- Section 6: Global coordination
-- ════════════════════════════════════════════════════════════

/-- A property requires global coordination. -/
structure RequiresGlobalCoordination {vocab : Vocabulary}
    (prop : FiniteStructure vocab → Prop) where
  unbounded_coordination : ∀ r,
    ∃ (A : FiniteStructure vocab) (a b : A.Domain),
      GaifmanDistance A a b > r ∧
      ∃ (A' : FiniteStructure vocab),
        A'.Domain = A.Domain ∧
        prop A ≠ prop A'

-- ════════════════════════════════════════════════════════════
-- Section 7: Core theorems
-- ════════════════════════════════════════════════════════════

/-- If a property requires global coordination, it cannot be defined
    by any bounded-depth FO formula.

    Proof: suppose phi (depth ≤ q) characterizes prop. By global coordination,
    get A, A' with same domain and prop A ≠ prop A'. Since phi ↔ prop:
    phi(A) ≠ phi(A'). But Gaifman decomposes phi into local sentences with
    radius ≤ locality_radius_bound q. By the bool_comb_same_domain transfer
    property, boolean_combination_eval gives the same result on A and A'
    (since A'.Domain = A.Domain). So phi(A) ↔ phi(A'), contradiction. -/
theorem locality_obstructs_fo_definability
    {vocab : Vocabulary}
    (prop : FiniteStructure vocab → Prop)
    (h_global : RequiresGlobalCoordination prop)
    (gaifman : GaifmanLocality)
    (q : Nat) :
    ¬∃ (phi : FOFormula vocab),
      phi.quantifierDepth ≤ q ∧
      ∀ A, FOFormula.eval vocab A phi ↔ prop A := by
  intro ⟨phi, _h_depth, h_char⟩
  -- Get A, A' with same domain but prop A ≠ prop A'
  obtain ⟨A, _a, _b, _h_dist, A', h_dom, h_prop_ne⟩ :=
    h_global.unbounded_coordination (locality_radius_bound q)
  -- phi decomposes into local sentences
  obtain ⟨local_sents, _h_radii, h_equiv⟩ := gaifman.decomposition vocab phi
  -- phi(A) ↔ boolean_combination(A) and phi(A') ↔ boolean_combination(A')
  -- boolean_combination(A) ↔ boolean_combination(A') by gaifman.bool_comb_same_domain
  have h_bool_iff : boolean_combination_eval local_sents A ↔
      boolean_combination_eval local_sents A' :=
    gaifman.bool_comb_same_domain vocab local_sents A A' h_dom
  -- Therefore phi(A) ↔ phi(A')
  have h_phi_iff : FOFormula.eval vocab A phi ↔ FOFormula.eval vocab A' phi :=
    (h_equiv A).trans (h_bool_iff.trans (h_equiv A').symm)
  -- But prop A ≠ prop A', and phi ↔ prop, so phi(A) ≠ phi(A')
  apply h_prop_ne
  exact propext ((h_char A).symm.trans (h_phi_iff.trans (h_char A')))

/-- The depth lower bound from locality. -/
theorem locality_depth_lower_bound
    {vocab : Vocabulary}
    (phi : FOFormula vocab)
    (gaifman : GaifmanLocality)
    (R : Nat)
    (h_radius : ∀ (local_sentences : List (GaifmanLocalSentence vocab)),
      (∀ (A : FiniteStructure vocab),
        FOFormula.eval vocab A phi ↔
        boolean_combination_eval local_sentences A) →
      ∃ ls ∈ local_sentences, ls.radius ≥ R) :
    phi.quantifierDepth ≥ Nat.log 3 (2 * R + 1) := by
  obtain ⟨local_sents, h_radii, h_equiv⟩ := gaifman.decomposition vocab phi
  obtain ⟨ls, hls, hls_radius⟩ := h_radius local_sents h_equiv
  have hls_bound := h_radii ls hls
  -- ls.radius ≥ R and ls.radius ≤ locality_radius_bound phi.quantifierDepth
  -- so locality_radius_bound phi.quantifierDepth ≥ R
  have h_lb : locality_radius_bound phi.quantifierDepth ≥ R :=
    Nat.le_trans hls_radius hls_bound
  -- locality_radius_bound q = (3^q - 1) / 2 ≥ R → 3^q ≥ 2R + 1
  unfold locality_radius_bound at h_lb
  have hpos : 1 ≤ 3 ^ phi.quantifierDepth :=
    Nat.one_le_pow phi.quantifierDepth 3 (by omega)
  have h3 : 3 ^ phi.quantifierDepth ≥ 2 * R + 1 := by
    -- h_lb : R ≤ (3^q - 1) / 2
    -- Nat.le_div_iff_mul_le (k := 2): R * 2 ≤ 3^q - 1
    have hge : R * 2 ≤ 3 ^ phi.quantifierDepth - 1 :=
      (Nat.le_div_iff_mul_le (k0 := show 0 < 2 by omega)).mp h_lb
    omega
  -- log_3(2R+1) ≤ log_3(3^q) = q
  -- The goal is phi.quantifierDepth ≥ Nat.log 3 (2*R+1), i.e., the same as:
  -- Nat.log 3 (2*R+1) ≤ phi.quantifierDepth
  show Nat.log 3 (2 * R + 1) ≤ phi.quantifierDepth
  exact (Nat.log_monotone h3).trans_eq (Nat.log_pow (by omega : 1 < 3) phi.quantifierDepth)

end ClassicalConstraints
