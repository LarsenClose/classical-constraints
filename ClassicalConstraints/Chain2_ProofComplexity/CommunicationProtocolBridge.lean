/-
  ClassicalConstraints/CommunicationProtocolBridge.lean
  Karchmer-Wigderson games and communication protocols.

  A KW game for a Boolean function f: given Alice holds x in f⁻¹(1) and Bob
  holds y in f⁻¹(0), they must find a coordinate i where x_i ≠ y_i.

  Key content:
  - ProtocolTree: generic binary communication tree with depth and leafCount
  - KWGame, CommProtocol, Rectangle, RectanglePartition
  - protocol_leaf_count: leaf count ≤ 2^depth (proved)
  - protocol_subtree_depth_le (proved)
  - Deep results (protocol_to_rectangles, kw_protocol_*) stated as axioms

  STATUS: 0 sorry. Classical.choice allowed.
-/

import ClassicalConstraints.Shared.Basic
import ClassicalConstraints.Shared.CookSelectorBridge
import ClassicalConstraints.Chain2_ProofComplexity.ResolutionWidthCore
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Bool.Basic

namespace ClassicalConstraints

-- ════════════════════════════════════════════════════════════
-- Section 1: Protocol Trees
-- ════════════════════════════════════════════════════════════

/-- A communication protocol tree: a binary tree where each internal
    node is labeled with which player sends a bit and which bit of
    their input they reveal. Leaves are labeled with an output. -/
inductive ProtocolTree (n_alice n_bob : Nat) (Output : Type) where
  /-- A leaf: the protocol terminates with this output -/
  | leaf (out : Output) : ProtocolTree n_alice n_bob Output
  /-- Alice sends: she reveals a bit of her input -/
  | alice_sends
      (query : Fin n_alice)
      (on_zero : ProtocolTree n_alice n_bob Output)
      (on_one : ProtocolTree n_alice n_bob Output)
      : ProtocolTree n_alice n_bob Output
  /-- Bob sends: he reveals a bit of his input -/
  | bob_sends
      (query : Fin n_bob)
      (on_zero : ProtocolTree n_alice n_bob Output)
      (on_one : ProtocolTree n_alice n_bob Output)
      : ProtocolTree n_alice n_bob Output

/-- The depth of a protocol tree: longest root-to-leaf path. -/
def ProtocolTree.depth {n_alice n_bob : Nat} {Output : Type} :
    ProtocolTree n_alice n_bob Output → Nat
  | .leaf _ => 0
  | .alice_sends _ t0 t1 => 1 + max t0.depth t1.depth
  | .bob_sends _ t0 t1 => 1 + max t0.depth t1.depth

/-- Evaluate a protocol tree on concrete inputs for Alice and Bob. -/
def ProtocolTree.eval {n_alice n_bob : Nat} {Output : Type}
    (t : ProtocolTree n_alice n_bob Output)
    (alice_input : Fin n_alice → Bool)
    (bob_input : Fin n_bob → Bool) : Output :=
  match t with
  | .leaf out => out
  | .alice_sends q t0 t1 =>
    if alice_input q then t1.eval alice_input bob_input
    else t0.eval alice_input bob_input
  | .bob_sends q t0 t1 =>
    if bob_input q then t1.eval alice_input bob_input
    else t0.eval alice_input bob_input

/-- The number of leaves in a protocol tree. -/
def ProtocolTree.leafCount {n_alice n_bob : Nat} {Output : Type} :
    ProtocolTree n_alice n_bob Output → Nat
  | .leaf _ => 1
  | .alice_sends _ t0 t1 => t0.leafCount + t1.leafCount
  | .bob_sends _ t0 t1 => t0.leafCount + t1.leafCount

/-- Protocol subtree depth is strictly less than parent depth. -/
theorem protocol_subtree_depth_le {n_alice n_bob : Nat} {Output : Type}
    (t : ProtocolTree n_alice n_bob Output) :
    match t with
    | .leaf _ => True
    | .alice_sends _ t0 t1 => t0.depth < t.depth ∧ t1.depth < t.depth
    | .bob_sends _ t0 t1 => t0.depth < t.depth ∧ t1.depth < t.depth := by
  cases t with
  | leaf _ => trivial
  | alice_sends _ t0 t1 =>
    simp only [ProtocolTree.depth]
    constructor <;> omega
  | bob_sends _ t0 t1 =>
    simp only [ProtocolTree.depth]
    constructor <;> omega

/-- Leaf count is at most 2^depth. -/
theorem protocol_leaf_count {n_alice n_bob : Nat} {Output : Type}
    (t : ProtocolTree n_alice n_bob Output) :
    t.leafCount ≤ 2 ^ t.depth := by
  induction t with
  | leaf _ => simp [ProtocolTree.leafCount, ProtocolTree.depth]
  | alice_sends _ t0 t1 ih0 ih1 =>
    simp only [ProtocolTree.leafCount, ProtocolTree.depth]
    have h2pos : (2 : Nat) > 0 := Nat.succ_le_succ (Nat.zero_le _)
    have hmax0 : 2 ^ t0.depth ≤ 2 ^ max t0.depth t1.depth :=
      Nat.pow_le_pow_right h2pos (Nat.le_max_left _ _)
    have hmax1 : 2 ^ t1.depth ≤ 2 ^ max t0.depth t1.depth :=
      Nat.pow_le_pow_right h2pos (Nat.le_max_right _ _)
    have hpow : (2 : Nat) ^ (1 + max t0.depth t1.depth) =
                2 ^ max t0.depth t1.depth + 2 ^ max t0.depth t1.depth := by
      have heq : 1 + max t0.depth t1.depth = max t0.depth t1.depth + 1 := by omega
      rw [heq, Nat.pow_succ]; omega
    omega
  | bob_sends _ t0 t1 ih0 ih1 =>
    simp only [ProtocolTree.leafCount, ProtocolTree.depth]
    have h2pos : (2 : Nat) > 0 := Nat.succ_le_succ (Nat.zero_le _)
    have hmax0 : 2 ^ t0.depth ≤ 2 ^ max t0.depth t1.depth :=
      Nat.pow_le_pow_right h2pos (Nat.le_max_left _ _)
    have hmax1 : 2 ^ t1.depth ≤ 2 ^ max t0.depth t1.depth :=
      Nat.pow_le_pow_right h2pos (Nat.le_max_right _ _)
    have hpow : (2 : Nat) ^ (1 + max t0.depth t1.depth) =
                2 ^ max t0.depth t1.depth + 2 ^ max t0.depth t1.depth := by
      have heq : 1 + max t0.depth t1.depth = max t0.depth t1.depth + 1 := by omega
      rw [heq, Nat.pow_succ]; omega
    omega

-- ════════════════════════════════════════════════════════════
-- Section 2: KW Games and Communication Protocols
-- ════════════════════════════════════════════════════════════

/-- A Karchmer-Wigderson game for a Boolean function on n-bit inputs. -/
structure KWGame (n : Nat) where
  /-- The Boolean function -/
  f : (Fin n → Bool) → Bool
  /-- The protocol tree: both players have n-bit inputs, output is a coordinate -/
  protocol : ProtocolTree n n (Fin n)

/-- A KW protocol is correct if for every (x, y) with f(x)=true and f(y)=false,
    the protocol outputs a coordinate i where x_i ≠ y_i. -/
def KWGame.correct {n : Nat} (game : KWGame n) : Prop :=
  ∀ (x y : Fin n → Bool),
    game.f x = true → game.f y = false →
    let i := game.protocol.eval x y
    x i ≠ y i

/-- The communication complexity of a KW game: the depth of the protocol. -/
def KWGame.commComplexity {n : Nat} (game : KWGame n) : Nat :=
  game.protocol.depth

/-- A communication protocol for a Boolean function. -/
structure CommProtocol (n_alice n_bob : Nat) where
  /-- The protocol tree, outputting Bool -/
  tree : ProtocolTree n_alice n_bob Bool
  /-- The function being computed -/
  target : (Fin n_alice → Bool) → (Fin n_bob → Bool) → Bool
  /-- Correctness: the protocol computes the target -/
  h_correct : ∀ (a : Fin n_alice → Bool) (b : Fin n_bob → Bool),
    tree.eval a b = target a b

-- ════════════════════════════════════════════════════════════
-- Section 3: Combinatorial Rectangles
-- ════════════════════════════════════════════════════════════

/-- A combinatorial rectangle: a product set A × B. -/
structure Rectangle (n_alice n_bob : Nat) where
  /-- Alice's input set (characteristic function) -/
  alice_set : (Fin n_alice → Bool) → Prop
  /-- Bob's input set (characteristic function) -/
  bob_set : (Fin n_bob → Bool) → Prop

/-- A rectangle is monochromatic for a function if the function
    is constant on the rectangle. -/
def Rectangle.monochromatic {n_alice n_bob : Nat}
    (rect : Rectangle n_alice n_bob)
    (f : (Fin n_alice → Bool) → (Fin n_bob → Bool) → Bool)
    (val : Bool) : Prop :=
  ∀ a b, rect.alice_set a → rect.bob_set b → f a b = val

/-- A protocol of depth d partitions the input space into at most
    2^d monochromatic rectangles. -/
structure RectanglePartition (n_alice n_bob : Nat) (d : Nat) where
  /-- The rectangles -/
  rectangles : List (Rectangle n_alice n_bob)
  /-- Number of rectangles bounded by 2^d -/
  h_count : rectangles.length ≤ 2 ^ d
  /-- Every input pair is in at least one rectangle -/
  h_covering : ∀ (a : Fin n_alice → Bool) (b : Fin n_bob → Bool),
    ∃ r ∈ rectangles, r.alice_set a ∧ r.bob_set b

-- ════════════════════════════════════════════════════════════
-- Section 4: Protocol → Rectangle Partition (proved)
-- ════════════════════════════════════════════════════════════

-- Helper: collect leaves of a protocol tree as rectangles,
-- tracking path constraints accumulated along the way.
private def tree_rectangles {n_alice n_bob : Nat} (t : ProtocolTree n_alice n_bob Bool)
    (ac : (Fin n_alice → Bool) → Prop)
    (bc : (Fin n_bob → Bool) → Prop) :
    List (Rectangle n_alice n_bob) :=
  match t with
  | .leaf _ => [⟨ac, bc⟩]
  | .alice_sends q t0 t1 =>
    tree_rectangles t0 (fun a => ac a ∧ a q = false) bc ++
    tree_rectangles t1 (fun a => ac a ∧ a q = true) bc
  | .bob_sends q t0 t1 =>
    tree_rectangles t0 ac (fun b => bc b ∧ b q = false) ++
    tree_rectangles t1 ac (fun b => bc b ∧ b q = true)

-- Each rectangle tracks its path constraints (for monochromaticity proof).
private theorem tree_rectangles_spec {n_alice n_bob : Nat}
    (t : ProtocolTree n_alice n_bob Bool)
    (ac : (Fin n_alice → Bool) → Prop) (bc : (Fin n_bob → Bool) → Prop) :
    ∀ r ∈ tree_rectangles t ac bc,
      (∀ a, r.alice_set a → ac a) ∧
      (∀ b, r.bob_set b → bc b) ∧
      ((∀ a b, r.alice_set a → r.bob_set b → t.eval a b = true) ∨
       (∀ a b, r.alice_set a → r.bob_set b → t.eval a b = false)) := by
  induction t generalizing ac bc with
  | leaf v =>
    intro r hr
    simp only [tree_rectangles, List.mem_singleton] at hr
    subst hr
    refine ⟨fun a ha => ha, fun b hb => hb, ?_⟩
    cases v
    · right; intro a b _ _; rfl
    · left; intro a b _ _; rfl
  | alice_sends q t0 t1 ih0 ih1 =>
    intro r hr
    simp only [tree_rectangles, List.mem_append] at hr
    rcases hr with h | h
    · obtain ⟨h_a, h_b, h_mono⟩ := ih0 (fun a => ac a ∧ a q = false) bc r h
      refine ⟨fun a ha => (h_a a ha).1, h_b, ?_⟩
      rcases h_mono with hm | hm
      · left; intro a b ha hb
        simp [ProtocolTree.eval, (h_a a ha).2, hm a b ha hb]
      · right; intro a b ha hb
        simp [ProtocolTree.eval, (h_a a ha).2, hm a b ha hb]
    · obtain ⟨h_a, h_b, h_mono⟩ := ih1 (fun a => ac a ∧ a q = true) bc r h
      refine ⟨fun a ha => (h_a a ha).1, h_b, ?_⟩
      rcases h_mono with hm | hm
      · left; intro a b ha hb
        simp [ProtocolTree.eval, (h_a a ha).2, hm a b ha hb]
      · right; intro a b ha hb
        simp [ProtocolTree.eval, (h_a a ha).2, hm a b ha hb]
  | bob_sends q t0 t1 ih0 ih1 =>
    intro r hr
    simp only [tree_rectangles, List.mem_append] at hr
    rcases hr with h | h
    · obtain ⟨h_a, h_b, h_mono⟩ := ih0 ac (fun b => bc b ∧ b q = false) r h
      refine ⟨h_a, fun b hb => (h_b b hb).1, ?_⟩
      rcases h_mono with hm | hm
      · left; intro a b ha hb
        simp [ProtocolTree.eval, (h_b b hb).2, hm a b ha hb]
      · right; intro a b ha hb
        simp [ProtocolTree.eval, (h_b b hb).2, hm a b ha hb]
    · obtain ⟨h_a, h_b, h_mono⟩ := ih1 ac (fun b => bc b ∧ b q = true) r h
      refine ⟨h_a, fun b hb => (h_b b hb).1, ?_⟩
      rcases h_mono with hm | hm
      · left; intro a b ha hb
        simp [ProtocolTree.eval, (h_b b hb).2, hm a b ha hb]
      · right; intro a b ha hb
        simp [ProtocolTree.eval, (h_b b hb).2, hm a b ha hb]

private theorem tree_rectangles_covering {n_alice n_bob : Nat}
    (t : ProtocolTree n_alice n_bob Bool)
    (ac : (Fin n_alice → Bool) → Prop) (bc : (Fin n_bob → Bool) → Prop)
    (a : Fin n_alice → Bool) (b : Fin n_bob → Bool)
    (ha : ac a) (hb : bc b) :
    ∃ r ∈ tree_rectangles t ac bc, r.alice_set a ∧ r.bob_set b := by
  induction t generalizing ac bc a b with
  | leaf _ =>
    exact ⟨⟨ac, bc⟩, List.mem_singleton.mpr rfl, ha, hb⟩
  | alice_sends q t0 t1 ih0 ih1 =>
    simp only [tree_rectangles, List.mem_append]
    cases hq : a q with
    | false =>
      have ⟨r, hrm, hrr⟩ := ih0 (fun a' => ac a' ∧ a' q = false) bc a b
        (And.intro ha hq) hb
      exact ⟨r, Or.inl hrm, hrr⟩
    | true =>
      have ⟨r, hrm, hrr⟩ := ih1 (fun a' => ac a' ∧ a' q = true) bc a b
        (And.intro ha hq) hb
      exact ⟨r, Or.inr hrm, hrr⟩
  | bob_sends q t0 t1 ih0 ih1 =>
    simp only [tree_rectangles, List.mem_append]
    cases hq : b q with
    | false =>
      have ⟨r, hrm, hrr⟩ := ih0 ac (fun b' => bc b' ∧ b' q = false) a b ha
        (And.intro hb hq)
      exact ⟨r, Or.inl hrm, hrr⟩
    | true =>
      have ⟨r, hrm, hrr⟩ := ih1 ac (fun b' => bc b' ∧ b' q = true) a b ha
        (And.intro hb hq)
      exact ⟨r, Or.inr hrm, hrr⟩

private theorem tree_rectangles_count {n_alice n_bob : Nat}
    (t : ProtocolTree n_alice n_bob Bool)
    (ac : (Fin n_alice → Bool) → Prop) (bc : (Fin n_bob → Bool) → Prop) :
    (tree_rectangles t ac bc).length ≤ 2 ^ t.depth := by
  induction t generalizing ac bc with
  | leaf _ => simp [tree_rectangles, ProtocolTree.depth]
  | alice_sends q t0 t1 ih0 ih1 =>
    simp only [tree_rectangles, List.length_append, ProtocolTree.depth]
    have i0 := ih0 (fun a => ac a ∧ a q = false) bc
    have i1 := ih1 (fun a => ac a ∧ a q = true) bc
    have h2pos : (2 : Nat) > 0 := by omega
    have hm0 : 2 ^ t0.depth ≤ 2 ^ max t0.depth t1.depth :=
      Nat.pow_le_pow_right h2pos (Nat.le_max_left _ _)
    have hm1 : 2 ^ t1.depth ≤ 2 ^ max t0.depth t1.depth :=
      Nat.pow_le_pow_right h2pos (Nat.le_max_right _ _)
    have hpow : (2 : Nat) ^ (1 + max t0.depth t1.depth) =
                2 ^ max t0.depth t1.depth + 2 ^ max t0.depth t1.depth := by
      rw [show 1 + max t0.depth t1.depth = max t0.depth t1.depth + 1 from by omega, Nat.pow_succ]
      omega
    omega
  | bob_sends q t0 t1 ih0 ih1 =>
    simp only [tree_rectangles, List.length_append, ProtocolTree.depth]
    have i0 := ih0 ac (fun b => bc b ∧ b q = false)
    have i1 := ih1 ac (fun b => bc b ∧ b q = true)
    have h2pos : (2 : Nat) > 0 := by omega
    have hm0 : 2 ^ t0.depth ≤ 2 ^ max t0.depth t1.depth :=
      Nat.pow_le_pow_right h2pos (Nat.le_max_left _ _)
    have hm1 : 2 ^ t1.depth ≤ 2 ^ max t0.depth t1.depth :=
      Nat.pow_le_pow_right h2pos (Nat.le_max_right _ _)
    have hpow : (2 : Nat) ^ (1 + max t0.depth t1.depth) =
                2 ^ max t0.depth t1.depth + 2 ^ max t0.depth t1.depth := by
      rw [show 1 + max t0.depth t1.depth = max t0.depth t1.depth + 1 from by omega, Nat.pow_succ]
      omega
    omega

/-- A depth-d protocol partitions the input space into at most 2^d
    monochromatic rectangles. Proved by structural induction on the protocol tree:
    each leaf is one monochromatic rectangle; internal nodes split into two halves. -/
theorem protocol_to_rectangles {n_alice n_bob : Nat}
    (proto : CommProtocol n_alice n_bob) :
    ∃ part : RectanglePartition n_alice n_bob proto.tree.depth,
      ∀ r ∈ part.rectangles,
        r.monochromatic proto.target true ∨ r.monochromatic proto.target false := by
  refine ⟨⟨tree_rectangles proto.tree (fun _ => True) (fun _ => True),
           tree_rectangles_count proto.tree _ _,
           fun a b => tree_rectangles_covering proto.tree _ _ a b trivial trivial⟩,
          fun r hr => ?_⟩
  obtain ⟨_, _, h_mono⟩ := tree_rectangles_spec proto.tree _ _ r hr
  rcases h_mono with hm | hm
  · left; intro a b ha hb
    rw [← proto.h_correct]; exact hm a b ha hb
  · right; intro a b ha hb
    rw [← proto.h_correct]; exact hm a b ha hb

-- KW characterization axioms (kw_protocol_from_solver, kw_protocol_correct,
-- kw_protocol_depth_bounded, comm_lower_bound_implies_selector_obstruction)
-- were removed: all four were unused downstream and inflated the axiom count.
-- The KW characterization theorem (communication complexity = depth complexity)
-- is aspirational future work requiring a full ProtocolTree construction from
-- solver access profiles.

-- ════════════════════════════════════════════════════════════
-- Section 5: Short proof → bounded protocol
-- ════════════════════════════════════════════════════════════

/-- A resolution refutation of size s yields a protocol of depth at most s.

    Note: This statement is vacuously true. The CommProtocol type only requires
    existence of a ProtocolTree computing SOME Boolean function — it does not
    constrain WHICH function. A constant protocol (leaf true, depth 0) always
    works. The meaningful version (Krajíček extraction) would additionally
    require the protocol to compute a KW-game separation function, which the
    current type does not impose.

    Previously stated as axiom; now proved directly. -/
theorem short_proof_bounded_comm_trivial (φ : CNF)
    (ref : ResolutionRefutation φ) :
    ∃ proto : CommProtocol φ.num_vars φ.num_vars,
      proto.tree.depth ≤ ref.size :=
  ⟨⟨.leaf true, fun _ _ => true, fun _ _ => rfl⟩, Nat.zero_le _⟩

end ClassicalConstraints
