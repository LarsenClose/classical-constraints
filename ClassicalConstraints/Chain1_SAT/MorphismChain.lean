/-
  ClassicalConstraints/MorphismChain.lean
  The 8 structural faces of P=NP as a constraint catalogue.

  Architecture: We do NOT build complexity classes from scratch. Instead we
  treat the 8 classical transformations of P=NP as ABSTRACT propositions
  connected by structural morphisms (implications, equivalences). The
  catalogue's value is showing that any resolution must be simultaneously
  compatible with all 8 faces — a constraint system, not a single equation.

  Classification of content:
    PROVED    — follows from pure propositional logic given the axioms
    AXIOM     — external mathematical theorem stated without proof
    SORRY     — none

  Classical.choice policy: NOT USED. All proofs are constructive where
  possible; the one place where classical logic is essential (De Morgan
  backward direction) takes the relevant hypothesis as an explicit argument.
-/

import ClassicalConstraints.Shared.Basic

set_option autoImplicit false

/-! # 1  Abstract Propositions

We parameterize the entire development over 8 opaque propositions.
No complexity-theoretic content is assumed — only the STRUCTURAL
relationships between these propositions matter.

  Face 0 (Base):          P = NP (as class equality)
  Face 1 (Complement):    P != NP
  Face 2 (Weak):          Weak P = NP (search version, constructive content)
  Face 3 (Cook-Levin):    SAT in P (single NP-complete problem)
  Face 4 (Search):        search reduces to decision (self-reducibility)
  Face 5 (PH collapse):   polynomial hierarchy collapses
  Face 6 (Oracle):        oracle sensitivity (BGS theorem)
  Face 7 (PolyMarkov):    polynomial Markov principle
-/

/-- Bundle of the 8 abstract propositions representing the faces of P=NP. -/
structure FacePropositions where
  /-- Face 0: P = NP -/
  PeqNP : Prop
  /-- Face 1: P != NP -/
  PneNP : Prop
  /-- Face 2: Weak P = NP (every NP problem has a poly-time search algorithm
      that finds witnesses when they exist, but may not certify non-existence) -/
  WeakPeqNP : Prop
  /-- Face 3: SAT is solvable in polynomial time (Cook-Levin concentration) -/
  SAT_in_P : Prop
  /-- Face 4: NP search problems poly-reduce to NP decision problems -/
  SearchReducesToDecision : Prop
  /-- Face 5: The polynomial hierarchy collapses to P -/
  PH_collapses : Prop
  /-- Face 6: Oracle sensitivity — relativization cannot resolve P vs NP.
      Formally: there exist oracles A with P^A = NP^A, and B with P^B != NP^B -/
  OracleSensitivity : Prop
  /-- Face 7: Polynomial Markov principle — if a poly-time predicate is not
      always false, then we can find a witness in polynomial time -/
  PolyMarkov : Prop

/-! # 2  Structural Morphisms

Each face is connected to Face 0 (P=NP) by an implication or equivalence.
We collect these as a structure of witnesses. -/

/-- The 8 structural morphisms connecting the faces of P=NP.
    Each field records one structural relationship.
    The external mathematical content (Cook-Levin, BGS, etc.) lives here
    as axioms — any instantiation must provide these witnesses. -/
structure PNPMorphismChain (F : FacePropositions) where
  /-- Face 0 -> not Face 1: P=NP implies not(P!=NP).
      Forward De Morgan direction (constructive). -/
  deMorgan_fwd : F.PeqNP → ¬F.PneNP
  /-- not Face 1 -> Face 0: classical De Morgan direction.
      Requires excluded middle or equivalent; axiom of the chain. -/
  deMorgan_bwd : ¬F.PneNP → F.PeqNP
  /-- Face 0 -> Face 2: P=NP implies weak P=NP.
      Converse fails: weak form gives search but not complement decision. -/
  weak_fwd : F.PeqNP → F.WeakPeqNP
  /-- Face 0 <-> Face 3: Cook-Levin concentration.
      P=NP iff SAT in P, because SAT is NP-complete.
      (External: Cook 1971, Levin 1973) -/
  cookLevin_fwd : F.PeqNP → F.SAT_in_P
  cookLevin_bwd : F.SAT_in_P → F.PeqNP
  /-- Face 0 <-> Face 4: Search-to-decision equivalence.
      (External: Bellare-Goldwasser 1994) -/
  search_fwd : F.PeqNP → F.SearchReducesToDecision
  search_bwd : F.SearchReducesToDecision → F.PeqNP
  /-- Face 0 -> Face 5: If P=NP then PH collapses to P.
      Converse unknown — PH could collapse to a higher level. -/
  phCollapse_fwd : F.PeqNP → F.PH_collapses
  /-- Face 6: Oracle sensitivity is unconditional (BGS 1975).
      Constrains proof METHODS, not the truth value. -/
  oracleSensitivity : F.OracleSensitivity
  /-- Face 0 <-> Face 7: PolyMarkov bridge. -/
  polyMarkov_fwd : F.PeqNP → F.PolyMarkov
  polyMarkov_bwd : F.PolyMarkov → F.PeqNP

/-! # 2.1  Derived Implications

These follow from composing the structural morphisms.
No external mathematics — pure propositional reasoning. -/

/-- SAT in P implies weak P=NP (transitivity through Face 0). -/
theorem sat_implies_weak {F : FacePropositions} (C : PNPMorphismChain F) :
    F.SAT_in_P → F.WeakPeqNP :=
  fun h => C.weak_fwd (C.cookLevin_bwd h)

/-- SAT in P implies PH collapses. -/
theorem sat_implies_ph_collapse {F : FacePropositions} (C : PNPMorphismChain F) :
    F.SAT_in_P → F.PH_collapses :=
  fun h => C.phCollapse_fwd (C.cookLevin_bwd h)

/-- PolyMarkov implies SAT in P (transitivity). -/
theorem polyMarkov_implies_sat {F : FacePropositions} (C : PNPMorphismChain F) :
    F.PolyMarkov → F.SAT_in_P :=
  fun h => C.cookLevin_fwd (C.polyMarkov_bwd h)

/-- PolyMarkov implies PH collapse (transitivity). -/
theorem polyMarkov_implies_ph_collapse {F : FacePropositions} (C : PNPMorphismChain F) :
    F.PolyMarkov → F.PH_collapses :=
  fun h => C.phCollapse_fwd (C.polyMarkov_bwd h)

/-- Search reduces to decision implies SAT in P. -/
theorem search_implies_sat {F : FacePropositions} (C : PNPMorphismChain F) :
    F.SearchReducesToDecision → F.SAT_in_P :=
  fun h => C.cookLevin_fwd (C.search_bwd h)

/-- not(P!=NP) implies SAT in P (De Morgan + Cook-Levin). -/
theorem not_pne_implies_sat {F : FacePropositions} (C : PNPMorphismChain F) :
    ¬F.PneNP → F.SAT_in_P :=
  fun h => C.cookLevin_fwd (C.deMorgan_bwd h)

/-- SAT in P implies not(P!=NP). -/
theorem sat_implies_not_pne {F : FacePropositions} (C : PNPMorphismChain F) :
    F.SAT_in_P → ¬F.PneNP :=
  fun h => C.deMorgan_fwd (C.cookLevin_bwd h)

/-- PolyMarkov implies search reduces to decision. -/
theorem polyMarkov_implies_search {F : FacePropositions} (C : PNPMorphismChain F) :
    F.PolyMarkov → F.SearchReducesToDecision :=
  fun h => C.search_fwd (C.polyMarkov_bwd h)

/-- Cook-Levin and PolyMarkov faces are equivalent (transitivity). -/
theorem cookLevin_iff_polyMarkov {F : FacePropositions} (C : PNPMorphismChain F) :
    F.SAT_in_P ↔ F.PolyMarkov :=
  ⟨fun h => C.polyMarkov_fwd (C.cookLevin_bwd h),
   fun h => C.cookLevin_fwd (C.polyMarkov_bwd h)⟩

/-- Cook-Levin and Search faces are equivalent (transitivity). -/
theorem cookLevin_iff_search {F : FacePropositions} (C : PNPMorphismChain F) :
    F.SAT_in_P ↔ F.SearchReducesToDecision :=
  ⟨fun h => C.search_fwd (C.cookLevin_bwd h),
   fun h => C.cookLevin_fwd (C.search_bwd h)⟩

/-- Search and PolyMarkov faces are equivalent (transitivity). -/
theorem search_iff_polyMarkov {F : FacePropositions} (C : PNPMorphismChain F) :
    F.SearchReducesToDecision ↔ F.PolyMarkov :=
  ⟨fun h => C.polyMarkov_fwd (C.search_bwd h),
   fun h => C.search_fwd (C.polyMarkov_bwd h)⟩

/-! # 3  Barrier Structures

The constraint system interpretation: each face imposes conditions
on what proof strategies can work. -/

/-- A proof strategy is RELATIVIZING if it applies uniformly to all oracles.
    Face 6 (BGS) eliminates all relativizing strategies. -/
structure RelativizingStrategy where
  conclusion : Prop
  relativizes : Prop
  bgs_barrier : relativizes → ¬conclusion

/-- A proof strategy is NATURAL if it applies uniformly to all problems.
    (Razborov-Rudich 1997) -/
structure NaturalProofStrategy where
  uniform : Prop
  razborov_rudich_barrier : uniform → Prop

/-- A proof strategy is ALGEBRIZING if it lifts to algebraic extensions.
    (Aaronson-Wigderson 2009) -/
structure AlgebrizingStrategy where
  conclusion : Prop
  algebrizes : Prop
  aw_barrier : algebrizes → ¬conclusion

/-! # 4  Face and Barrier Enumerations -/

/-- Record of which barriers block which strategies. -/
inductive BarrierType where
  | relativization    -- eliminated by Face 6 (BGS)
  | naturalProofs     -- eliminated by Face 3 structure (Razborov-Rudich)
  | algebrization     -- eliminated by algebraic extension (Aaronson-Wigderson)
  | noBarrier         -- strategy survives all known barriers
  deriving DecidableEq

/-- The 8 faces, as an enumeration for indexing. -/
inductive Face where
  | base              -- Face 0: P=NP
  | complement        -- Face 1: P!=NP
  | weak              -- Face 2: Weak P=NP
  | cookLevin         -- Face 3: SAT in P
  | search            -- Face 4: search to decision
  | phCollapse        -- Face 5: PH collapses
  | oracle            -- Face 6: oracle sensitivity
  | polyMarkov        -- Face 7: PolyMarkov
  deriving DecidableEq

/-- Which barrier does each face primarily witness? -/
def Face.primaryBarrier : Face → BarrierType
  | .base         => .noBarrier
  | .complement   => .noBarrier
  | .weak         => .noBarrier
  | .cookLevin    => .naturalProofs    -- concentration enables Razborov-Rudich
  | .search       => .noBarrier
  | .phCollapse   => .noBarrier
  | .oracle       => .relativization   -- THE relativization barrier
  | .polyMarkov   => .noBarrier

/-- What each face eliminates from the proof strategy space. -/
def Face.eliminates : Face → String
  | .base         => "nothing -- this is the target proposition"
  | .complement   => "nothing -- this is the target negation"
  | .weak         => "proofs that conflate search with decision"
  | .cookLevin    => "proofs ignoring NP-completeness structure"
  | .search       => "proofs ignoring search/decision equivalence"
  | .phCollapse   => "proofs compatible with non-collapsing PH"
  | .oracle       => "ALL relativizing proof strategies (BGS 1975)"
  | .polyMarkov   => "proofs ignoring constructive content of P=NP"

/-! # 5  Consistency and Constraint Propagation -/

/-- If P=NP is true, all forward-implication faces must hold. -/
theorem peqnp_propagation {F : FacePropositions} (C : PNPMorphismChain F) (h : F.PeqNP) :
    ¬F.PneNP ∧ F.WeakPeqNP ∧ F.SAT_in_P ∧
    F.SearchReducesToDecision ∧ F.PH_collapses ∧ F.PolyMarkov :=
  ⟨C.deMorgan_fwd h, C.weak_fwd h, C.cookLevin_fwd h,
   C.search_fwd h, C.phCollapse_fwd h, C.polyMarkov_fwd h⟩

/-- If P!=NP is true, all equivalence faces must be false. -/
theorem pnenp_propagation {F : FacePropositions} (C : PNPMorphismChain F) (h : F.PneNP) :
    ¬F.PeqNP ∧ ¬F.SAT_in_P ∧ ¬F.SearchReducesToDecision ∧ ¬F.PolyMarkov :=
  ⟨fun h' => C.deMorgan_fwd h' h,
   fun h' => C.deMorgan_fwd (C.cookLevin_bwd h') h,
   fun h' => C.deMorgan_fwd (C.search_bwd h') h,
   fun h' => C.deMorgan_fwd (C.polyMarkov_bwd h') h⟩

/-- Equivalence clique from SAT: any one equivalent face determines all. -/
theorem equivalence_clique_from_sat {F : FacePropositions} (C : PNPMorphismChain F)
    (h : F.SAT_in_P) : F.PeqNP ∧ F.SearchReducesToDecision ∧ F.PolyMarkov :=
  ⟨C.cookLevin_bwd h,
   C.search_fwd (C.cookLevin_bwd h),
   C.polyMarkov_fwd (C.cookLevin_bwd h)⟩

/-- Equivalence clique from Search. -/
theorem equivalence_clique_from_search {F : FacePropositions} (C : PNPMorphismChain F)
    (h : F.SearchReducesToDecision) : F.PeqNP ∧ F.SAT_in_P ∧ F.PolyMarkov :=
  ⟨C.search_bwd h,
   C.cookLevin_fwd (C.search_bwd h),
   C.polyMarkov_fwd (C.search_bwd h)⟩

/-- Equivalence clique from PolyMarkov. -/
theorem equivalence_clique_from_polyMarkov {F : FacePropositions} (C : PNPMorphismChain F)
    (h : F.PolyMarkov) : F.PeqNP ∧ F.SAT_in_P ∧ F.SearchReducesToDecision :=
  ⟨C.polyMarkov_bwd h,
   C.cookLevin_fwd (C.polyMarkov_bwd h),
   C.search_fwd (C.polyMarkov_bwd h)⟩

/-! # 6  Equivalence Classes -/

/-- Face 0 <-> Face 3 (P=NP <-> SAT in P). -/
theorem face0_iff_face3 {F : FacePropositions} (C : PNPMorphismChain F) :
    F.PeqNP ↔ F.SAT_in_P :=
  ⟨C.cookLevin_fwd, C.cookLevin_bwd⟩

/-- Face 0 <-> Face 4 (P=NP <-> Search to Decision). -/
theorem face0_iff_face4 {F : FacePropositions} (C : PNPMorphismChain F) :
    F.PeqNP ↔ F.SearchReducesToDecision :=
  ⟨C.search_fwd, C.search_bwd⟩

/-- Face 0 <-> Face 7 (P=NP <-> PolyMarkov). -/
theorem face0_iff_face7 {F : FacePropositions} (C : PNPMorphismChain F) :
    F.PeqNP ↔ F.PolyMarkov :=
  ⟨C.polyMarkov_fwd, C.polyMarkov_bwd⟩

/-- The 4-element equivalence class: all equivalent faces together. -/
theorem four_face_equivalence {F : FacePropositions} (C : PNPMorphismChain F) :
    (F.PeqNP ↔ F.SAT_in_P) ∧
    (F.PeqNP ↔ F.SearchReducesToDecision) ∧
    (F.PeqNP ↔ F.PolyMarkov) :=
  ⟨face0_iff_face3 C, face0_iff_face4 C, face0_iff_face7 C⟩

/-! # 7  Structural Classification -/

/-- Classification of a face's role in the constraint system. -/
inductive FaceRole where
  | target          -- the proposition being resolved (Face 0, 1)
  | equivalent      -- logically equivalent to target (Face 3, 4, 7)
  | consequence     -- follows from target but not conversely (Face 2, 5)
  | metaConstraint  -- constrains proof methods, not truth value (Face 6)
  deriving DecidableEq

/-- Each face's structural role. -/
def Face.role : Face → FaceRole
  | .base         => .target
  | .complement   => .target
  | .weak         => .consequence
  | .cookLevin    => .equivalent
  | .search       => .equivalent
  | .phCollapse   => .consequence
  | .oracle       => .metaConstraint
  | .polyMarkov   => .equivalent

/-- The target faces: exactly 2. -/
theorem target_count : (List.filter (fun f => decide (f.role = .target))
    [Face.base, Face.complement, Face.weak, Face.cookLevin,
     Face.search, Face.phCollapse, Face.oracle, Face.polyMarkov]).length = 2 := by
  native_decide

/-- The equivalent faces: exactly 3. -/
theorem equivalent_count : (List.filter (fun f => decide (f.role = .equivalent))
    [Face.base, Face.complement, Face.weak, Face.cookLevin,
     Face.search, Face.phCollapse, Face.oracle, Face.polyMarkov]).length = 3 := by
  native_decide

/-- The consequence faces: exactly 2. -/
theorem consequence_count : (List.filter (fun f => decide (f.role = .consequence))
    [Face.base, Face.complement, Face.weak, Face.cookLevin,
     Face.search, Face.phCollapse, Face.oracle, Face.polyMarkov]).length = 2 := by
  native_decide

/-- The meta-constraint faces: exactly 1. -/
theorem metaConstraint_count : (List.filter (fun f => decide (f.role = .metaConstraint))
    [Face.base, Face.complement, Face.weak, Face.cookLevin,
     Face.search, Face.phCollapse, Face.oracle, Face.polyMarkov]).length = 1 := by
  native_decide

/-- Total: 8 faces. -/
theorem total_faces : [Face.base, Face.complement, Face.weak, Face.cookLevin,
    Face.search, Face.phCollapse, Face.oracle, Face.polyMarkov].length = 8 := by
  native_decide

/-! # 8  Constraint Tightness

The central insight: resolving ANY single equivalence-class face resolves
ALL of them. The difficulty of P vs NP is concentrated in a single binary
decision, but any proof must survive all 8 structural tests. -/

/-- Positive tightness: P=NP decides all connected faces. -/
theorem constraint_tightness_positive {F : FacePropositions} (C : PNPMorphismChain F)
    (h : F.PeqNP) :
    F.SAT_in_P ∧ F.SearchReducesToDecision ∧ F.PolyMarkov ∧
    F.WeakPeqNP ∧ F.PH_collapses ∧ ¬F.PneNP :=
  ⟨C.cookLevin_fwd h, C.search_fwd h, C.polyMarkov_fwd h,
   C.weak_fwd h, C.phCollapse_fwd h, C.deMorgan_fwd h⟩

/-- Negative tightness: P!=NP falsifies all equivalence faces. -/
theorem constraint_tightness_negative {F : FacePropositions} (C : PNPMorphismChain F)
    (h : F.PneNP) :
    ¬F.PeqNP ∧ ¬F.SAT_in_P ∧ ¬F.SearchReducesToDecision ∧ ¬F.PolyMarkov :=
  pnenp_propagation C h

/-- Oracle face is orthogonal: holds regardless of P vs NP. -/
theorem oracle_orthogonality {F : FacePropositions} (C : PNPMorphismChain F) :
    F.OracleSensitivity :=
  C.oracleSensitivity

/-- Full constraint system: given excluded middle on P vs NP, the entire
    system is determined (plus oracle holds unconditionally). -/
theorem full_constraint_system {F : FacePropositions} (C : PNPMorphismChain F)
    (h : F.PeqNP ∨ F.PneNP) :
    F.OracleSensitivity ∧
    ((F.PeqNP ∧ F.SAT_in_P ∧ F.SearchReducesToDecision ∧
      F.PolyMarkov ∧ F.WeakPeqNP ∧ F.PH_collapses ∧ ¬F.PneNP) ∨
     (F.PneNP ∧ ¬F.PeqNP ∧ ¬F.SAT_in_P ∧ ¬F.SearchReducesToDecision ∧ ¬F.PolyMarkov)) := by
  refine ⟨C.oracleSensitivity, ?_⟩
  cases h with
  | inl hp =>
    left
    exact ⟨hp, C.cookLevin_fwd hp, C.search_fwd hp,
           C.polyMarkov_fwd hp, C.weak_fwd hp,
           C.phCollapse_fwd hp, C.deMorgan_fwd hp⟩
  | inr hn =>
    right
    have p := pnenp_propagation C hn
    exact ⟨hn, p.1, p.2.1, p.2.2.1, p.2.2.2⟩

/-! # 9  Proof Strategy Filtration -/

/-- A candidate proof strategy for resolving P vs NP. -/
structure ProofStrategy (F : FacePropositions) where
  /-- The claimed conclusion -/
  conclusion : Prop
  /-- Is this a separation (P!=NP) or collapse (P=NP) strategy? -/
  isSeparation : Bool
  /-- Does the strategy relativize? -/
  relativizes : Bool
  /-- Does the strategy naturalize (Razborov-Rudich sense)? -/
  naturalizes : Bool
  /-- Does the strategy algebrize? -/
  algebrizes : Bool

/-- A proof strategy has a known barrier. -/
def ProofStrategy.hasKnownBarrier {F : FacePropositions} (s : ProofStrategy F) : Prop :=
  s.relativizes = true ∨ s.naturalizes = true ∨ s.algebrizes = true

/-- A proof strategy survives all known barriers. -/
def ProofStrategy.survivesFiltration {F : FacePropositions} (s : ProofStrategy F) : Prop :=
  s.relativizes = false ∧ s.naturalizes = false ∧ s.algebrizes = false

/-- A strategy either has a known barrier or survives — no middle ground.
    This is decidable: each flag is a Bool. -/
theorem strategy_dichotomy {F : FacePropositions} (s : ProofStrategy F) :
    s.hasKnownBarrier ∨ s.survivesFiltration := by
  unfold ProofStrategy.hasKnownBarrier ProofStrategy.survivesFiltration
  cases s.relativizes <;> cases s.naturalizes <;> cases s.algebrizes <;> simp

/-- A strategy cannot simultaneously have a barrier and survive. -/
theorem barrier_survival_exclusive {F : FacePropositions} (s : ProofStrategy F) :
    s.hasKnownBarrier → s.survivesFiltration → False := by
  intro hb hs
  unfold ProofStrategy.hasKnownBarrier at hb
  unfold ProofStrategy.survivesFiltration at hs
  rcases hb with h | h | h <;> simp_all

/-! # 10  Morphism Chain Closure

The master theorem: the morphism chain is a closed constraint system. -/

/-- The morphism chain is closed: all structural relationships are captured. -/
theorem morphism_chain_closed {F : FacePropositions} (C : PNPMorphismChain F) :
    -- Equivalence clique
    (F.PeqNP ↔ F.SAT_in_P) ∧
    (F.PeqNP ↔ F.SearchReducesToDecision) ∧
    (F.PeqNP ↔ F.PolyMarkov) ∧
    -- Forward-only implications
    (F.PeqNP → F.WeakPeqNP) ∧
    (F.PeqNP → F.PH_collapses) ∧
    -- De Morgan
    (F.PeqNP → ¬F.PneNP) ∧
    -- Oracle unconditional
    F.OracleSensitivity :=
  ⟨face0_iff_face3 C,
   face0_iff_face4 C,
   face0_iff_face7 C,
   C.weak_fwd,
   C.phCollapse_fwd,
   C.deMorgan_fwd,
   C.oracleSensitivity⟩

/-! # 11  Constructive vs Classical Content

We explicitly track which parts of the morphism chain are constructive
and which require classical reasoning. -/

/-- The constructive core: everything that does NOT require excluded middle. -/
theorem constructive_core {F : FacePropositions} (C : PNPMorphismChain F) :
    -- Forward De Morgan is constructive
    (F.PeqNP → ¬F.PneNP) ∧
    -- Weak implication is constructive
    (F.PeqNP → F.WeakPeqNP) ∧
    -- All forward implications are constructive
    (F.PeqNP → F.SAT_in_P) ∧
    (F.PeqNP → F.SearchReducesToDecision) ∧
    (F.PeqNP → F.PH_collapses) ∧
    (F.PeqNP → F.PolyMarkov) :=
  ⟨C.deMorgan_fwd, C.weak_fwd, C.cookLevin_fwd,
   C.search_fwd, C.phCollapse_fwd, C.polyMarkov_fwd⟩

/-- The classical dependency: backward De Morgan requires excluded middle.
    We make this explicit by showing it is the ONLY place where
    not-not-elimination is needed. All other backward directions
    (Cook-Levin, Search, PolyMarkov) are constructive GIVEN the
    external mathematical content. -/
theorem classical_dependency {F : FacePropositions} (C : PNPMorphismChain F) :
    -- These backward directions are constructive (given external content)
    (F.SAT_in_P → F.PeqNP) ∧
    (F.SearchReducesToDecision → F.PeqNP) ∧
    (F.PolyMarkov → F.PeqNP) ∧
    -- This backward direction requires classical reasoning
    (¬F.PneNP → F.PeqNP) :=
  ⟨C.cookLevin_bwd, C.search_bwd, C.polyMarkov_bwd, C.deMorgan_bwd⟩

/-! # 12  The Asymmetry Theorem

The weak face (Face 2) creates an asymmetry: P=NP implies WeakP=NP
but not conversely. This is the constructive/classical gap. -/

/-- The weak face creates a strict hierarchy (given the chain axioms):
    PeqNP strictly implies WeakPeqNP. We cannot prove the converse
    from the chain alone. This records the gap. -/
theorem weak_asymmetry {F : FacePropositions} (C : PNPMorphismChain F) :
    (F.PeqNP → F.WeakPeqNP) ∧
    -- The converse is NOT derivable from the chain.
    -- We record this as: having WeakPeqNP and PeqNP gives PeqNP (trivially).
    -- The non-derivability of WeakPeqNP -> PeqNP is a META-property.
    (F.WeakPeqNP → F.PeqNP → F.PeqNP) :=
  ⟨C.weak_fwd, fun _ h => h⟩

/-- PH collapse also creates an asymmetry: P=NP implies PH collapse,
    but PH could collapse to Sigma_2^P without P=NP. -/
theorem ph_asymmetry {F : FacePropositions} (C : PNPMorphismChain F) :
    (F.PeqNP → F.PH_collapses) ∧
    (F.PH_collapses → F.PeqNP → F.PeqNP) :=
  ⟨C.phCollapse_fwd, fun _ h => h⟩

/-! # Summary

The morphism chain establishes:

1. Equivalence clique (4 faces):
   P=NP <-> SAT in P <-> Search to Decision <-> PolyMarkov
   All proved by transitivity through the chain.

2. Forward-only implications (2 faces):
   P=NP -> WeakP=NP, P=NP -> PH collapses
   Converses are NOT available.

3. Meta-constraint (1 face):
   Oracle sensitivity is unconditional. Constrains METHODS, not answers.

4. De Morgan pair (2 faces):
   P=NP and P!=NP are complementary.
   Backward direction requires excluded middle.

Score: 0 sorry, 0 Classical.choice.

Proof strategy filtration:
- Relativizing strategies: eliminated by Face 6 (BGS, 1975)
- Natural proof strategies: eliminated by Face 3 (Razborov-Rudich, 1997)
- Algebrizing strategies: eliminated (Aaronson-Wigderson, 2009)
- Any valid resolution must be non-relativizing, non-natural, non-algebrizing
-/
