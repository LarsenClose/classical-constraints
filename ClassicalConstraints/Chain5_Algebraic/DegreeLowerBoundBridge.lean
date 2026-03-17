/-
  ClassicalConstraints/DegreeLowerBoundBridge.lean
  Concrete degree lower bounds for specific unsatisfiable formula families
  in PC, NS, and SoS.

  Two specific families:
  1. Tseitin formulas on expanders: PC degree >= Omega(n).
  2. Random k-SAT above threshold: SoS degree >= Omega(n).

  These are stated as structures with the lower bounds as fields (axioms).
  The proofs are deep combinatorial results not formalized here.

  STATUS: 0 sorry. Classical.choice allowed (Side B).
-/

import ClassicalConstraints.Shared.Basic
import ClassicalConstraints.Shared.CookSelectorBridge
import ClassicalConstraints.Chain5_Algebraic.PolynomialCalculusCore
import ClassicalConstraints.Chain5_Algebraic.NullstellensatzCore
import ClassicalConstraints.Chain5_Algebraic.SOSRankCore

namespace ClassicalConstraints

-- ================================================================
-- Section 1: Tseitin formulas
-- ================================================================

/-- A graph structure for Tseitin formula construction.
    Named GraphStructure to avoid collision with Mathlib's SimpleGraph. -/
structure GraphStructure (n : Nat) where
  /-- Adjacency relation. -/
  adj : Fin n → Fin n → Bool
  /-- Symmetric. -/
  h_symm : ∀ i j, adj i j = adj j i
  /-- Irreflexive. -/
  h_irrefl : ∀ i, adj i i = false

/-- The degree of a vertex in a graph. -/
def GraphStructure.vertexDegree {n : Nat} (G : GraphStructure n) (v : Fin n) : Nat :=
  (List.finRange n).countP (fun w => G.adj v w)

/-- An expander graph: regular with bounded expansion. -/
structure ExpanderGraph (n : Nat) extends GraphStructure n where
  /-- Expansion parameter (scaled by 1000). -/
  epsilon : Nat
  /-- Regularity: all vertices have the same degree. -/
  regularity : Nat
  /-- All vertices have degree = regularity. -/
  h_regular : ∀ v, GraphStructure.vertexDegree toGraphStructure v = regularity

/-- A Tseitin formula on a graph G with charge function chi.
    The formula is unsatisfiable iff the sum of charges is odd. -/
structure TseitinInstance (n : Nat) where
  /-- The underlying graph. -/
  graph : GraphStructure n
  /-- The charge function (0 or 1 per vertex). -/
  charges : Fin n → Bool
  /-- The sum of charges is odd (ensures unsatisfiability). -/
  h_odd_charge : (List.finRange n).countP (fun v => charges v) % 2 = 1
  /-- The number of edge variables. -/
  num_edges : Nat
  /-- The CNF encoding. -/
  clauses : List (List Int)

/-- The Tseitin formula family on d-regular expander graphs. -/
structure TseitinFamily where
  /-- Graph family indexed by size. -/
  graphs : Nat → Σ n, ExpanderGraph n
  /-- The Tseitin instances. -/
  instances : (k : Nat) → TseitinInstance (graphs k).1
  /-- Instance size grows. -/
  h_growing : ∀ k, (graphs k).1 ≥ k
  /-- All instances are unsatisfiable (charges sum to odd). -/
  h_all_unsat : ∀ k, (List.finRange (graphs k).1).countP
    (fun v => (instances k).charges v) % 2 = 1

-- ================================================================
-- Section 2: Tseitin PC degree lower bound
-- ================================================================

/-- The Tseitin PC degree lower bound theorem (Ben-Sasson 2002).
    PC degree >= constant * n for Tseitin formulas on expanders.
    Holds over ALL fields (characteristic-independent). -/
structure TseitinPCLowerBound where
  /-- The Tseitin family. -/
  family : TseitinFamily
  /-- The linear constant in the lower bound. -/
  constant : Nat
  /-- The constant is positive. -/
  h_const_pos : constant > 0
  /-- The lower bound over any Type 0 field: PC degree >= constant * n. -/
  h_lower_bound : ∀ (F : Type) [Field F] (k d : Nat),
    d < constant * (family.graphs k).1 →
    ¬PCRefutable F (family.instances k).num_edges (family.instances k).clauses d

-- ================================================================
-- Section 3: Random k-SAT
-- ================================================================

/-- A random k-SAT instance specification. -/
structure RandomKSATSpec where
  /-- Clause width. -/
  k : Nat
  /-- k >= 3 (otherwise trivial). -/
  h_k : k ≥ 3
  /-- Clause-to-variable ratio numerator. -/
  ratio_num : Nat
  /-- Clause-to-variable ratio denominator. -/
  ratio_den : Nat
  /-- Ratio is above the unsatisfiability threshold. -/
  h_above_threshold : ratio_num > ratio_den

/-- A random k-SAT family: for each n, a specific instance. -/
structure RandomKSATFamily extends RandomKSATSpec where
  /-- The instance at each size n: (num_vars, clauses). -/
  instances : Nat → (Nat × List (List Int))
  /-- Number of variables equals n. -/
  h_nvars : ∀ n, (instances n).1 = n
  /-- All instances are unsatisfiable. -/
  h_unsat : ∀ n, ¬∃ (a : Fin (instances n).1 → Bool),
    ∀ c ∈ (instances n).2, ∃ l ∈ c,
      if l > 0 then
        ∃ h : l.natAbs - 1 < (instances n).1, a ⟨l.natAbs - 1, h⟩ = true
      else
        ∃ h : (-l).natAbs - 1 < (instances n).1, a ⟨(-l).natAbs - 1, h⟩ = false

-- ================================================================
-- Section 4: Random k-SAT SoS degree lower bound
-- ================================================================

/-- The random k-SAT SoS degree lower bound (Schoenebeck 2008).
    SoS degree >= Omega(n) for suitable k and ratio. -/
structure RandomKSATSoSLowerBound (F : Type*) [Field F] [LinearOrder F]
    [IsStrictOrderedRing F] where
  /-- The random k-SAT family. -/
  family : RandomKSATFamily
  /-- The linear constant. -/
  constant : Nat
  /-- Positive constant. -/
  h_const_pos : constant > 0
  /-- The lower bound. -/
  h_lower_bound : ∀ (n d : Nat),
    d < constant * n →
    ¬SoSRefutable F (family.instances n).1 (family.instances n).2 d

-- ================================================================
-- Section 5: Abstract algebraic degree lower bound
-- ================================================================

/-- The degree lower bounds witness the algebraic growth gap:
    algebraic capacity required grows at least linearly. -/
structure AlgebraicDegreeLowerBound where
  /-- A family of unsatisfiable formulas: (num_vars, clauses) at each n. -/
  family : Nat → (Nat × List (List Int))
  /-- Size grows. -/
  h_growing : ∀ n, (family n).1 ≥ n
  /-- The degree lower bound function. -/
  lower_bound : Nat → Nat
  /-- The lower bound is at least linear. -/
  h_linear : ∃ c > 0, ∀ n, lower_bound n ≥ c * n
  /-- No PC refutation exists below the lower bound (over any Type 0 field). -/
  h_pc_hard : ∀ (F : Type) [Field F] (n d : Nat),
    d < lower_bound n →
    ¬PCRefutable F (family n).1 (family n).2 d

-- ================================================================
-- Section 6: Tseitin lower bound instance
-- ================================================================

/-- A helper: if a graph on m vertices is d-regular with d >= 2,
    the number of edges is at least m. -/
def EdgeCountBound (m d : Nat) : Prop :=
  d ≥ 2 → m * d / 2 ≥ m

/-- Tseitin formulas provide an AlgebraicDegreeLowerBound. -/
def tseitinLowerBound
    (tpc : TseitinPCLowerBound)
    (h_edges_grow : ∀ k, (tpc.family.instances k).num_edges ≥ (tpc.family.graphs k).1) :
    AlgebraicDegreeLowerBound where
  family := fun k =>
    let inst := tpc.family.instances k
    (inst.num_edges, inst.clauses)
  h_growing := fun k =>
    Nat.le_trans (tpc.family.h_growing k) (h_edges_grow k)
  lower_bound := fun k => tpc.constant * (tpc.family.graphs k).1
  h_linear := ⟨tpc.constant, tpc.h_const_pos, fun n =>
    Nat.mul_le_mul_left tpc.constant (tpc.family.h_growing n)⟩
  h_pc_hard := fun F _ n d hd =>
    tpc.h_lower_bound F n d hd

-- ================================================================
-- Section 7: DegreeFaithful
-- ================================================================

/-- DegreeFaithful: Cook encoding preserves algebraic derivation degree
    up to polynomial distortion.

    This is the open bridge condition (analogous to CookFaithful in Chain 1). -/
structure DegreeFaithful where
  /-- Encoding from one SAT family to another. -/
  encode : SATFamily → SATFamily
  /-- Degree distortion: polynomial upper bound. -/
  degree_overhead : PolyBound
  /-- Faithfulness: PC degree of encoded formula is at most poly(original degree). -/
  h_faithful_upper : ∀ (F : Type) [Field F] (family : SATFamily)
    (n d : Nat),
    PCRefutable F (family n).num_vars (family n).clauses d →
    PCRefutable F ((encode family) n).num_vars ((encode family) n).clauses
      (degree_overhead.eval d)
  /-- Reverse faithfulness: hard instances stay hard. -/
  h_faithful_lower : ∀ (F : Type) [Field F] (family : SATFamily)
    (n d : Nat),
    ¬PCRefutable F ((encode family) n).num_vars ((encode family) n).clauses d →
    ¬PCRefutable F (family n).num_vars (family n).clauses
      (degree_overhead.eval d)

-- ================================================================
-- Section 8: Proofs
-- ================================================================

/-- For any positive constant c and bound B, there exists n₀ such that c * n > B for all n ≥ n₀. -/
theorem linear_beats_constant (c : Nat) (hc : c > 0) (B : Nat) :
    ∃ n₀, ∀ n ≥ n₀, c * n > B := by
  exact ⟨B + 1, fun n hn => by nlinarith⟩

/-- DegreeFaithful transfers hardness from the encoded family to the
    original: if the encoded family is hard at degree d, then the original
    is hard at the inflated degree overhead.eval d.

    This is the direct application of h_faithful_lower.

    DESIGN NOTE (was TODO): An AlgebraicDegreeLowerBound for the ENCODED
    family cannot be derived from DegreeFaithful + a lower bound for the
    ORIGINAL family. The directions are:
    - h_faithful_upper: original refutable at d → encoded refutable at
      overhead.eval d (REFUTABILITY transfers original → encoded)
    - h_faithful_lower: encoded hard at d → original hard at overhead.eval d
      (HARDNESS transfers encoded → original)
    Neither direction gives: original hard at d → encoded hard at f(d).
    To derive an encoded-family lower bound, DegreeFaithful would need an
    additional field: a "reverse encoding" or an explicit axiom that
    hardness transfers from original to encoded. -/
theorem degreeFaithful_transfers_hardness
    (df : DegreeFaithful)
    (family : SATFamily)
    (F : Type) [Field F]
    (n d : Nat)
    (h_encoded_hard : ¬PCRefutable F ((df.encode family) n).num_vars
                                     ((df.encode family) n).clauses d) :
    ¬PCRefutable F (family n).num_vars (family n).clauses
      (df.degree_overhead.eval d) :=
  df.h_faithful_lower F family n d h_encoded_hard
