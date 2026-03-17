/-
  ClassicalConstraints/LiftingCore.lean
  Lifting theorem framework: query complexity → communication complexity.

  A lifting gadget IS the encoding that converts decision tree depth into
  protocol depth. The lifting theorem (Raz-McKenzie, Goos-Pitassi-Watson)
  is stated as a structure with an open field. Constructive parts are proved.

  STATUS: 0 sorry. Classical.choice allowed.

  Sections 1-9: original content.
  Section 10: dt_to_proto (inverse of proto_to_dt), with depth/eval
  preservation and roundtrip idempotence.
-/

import ClassicalConstraints.Chain2_ProofComplexity.CommunicationProtocolBridge
import ClassicalConstraints.Shared.CookSelectorBridge
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Bool.Basic

namespace ClassicalConstraints

-- ════════════════════════════════════════════════════════════
-- Section 1: Decision Trees
-- ════════════════════════════════════════════════════════════

/-- A decision tree for a function f: {0,1}^n → {0,1}. -/
inductive DecisionTree (n : Nat) where
  /-- Leaf: output a value -/
  | leaf (val : Bool) : DecisionTree n
  /-- Query variable i, branch on its value -/
  | query (i : Fin n) (on_false : DecisionTree n) (on_true : DecisionTree n) : DecisionTree n

/-- Depth of a decision tree. -/
def DecisionTree.depth {n : Nat} : DecisionTree n → Nat
  | .leaf _ => 0
  | .query _ t0 t1 => 1 + max t0.depth t1.depth

/-- Evaluate a decision tree on an input. -/
def DecisionTree.eval {n : Nat} : DecisionTree n → (Fin n → Bool) → Bool
  | .leaf v, _ => v
  | .query i t0 t1, x => if x i then t1.eval x else t0.eval x

/-- The query complexity of a Boolean function. -/
def queryComplexity (n : Nat) (f : (Fin n → Bool) → Bool) (d : Nat) : Prop :=
  (∃ t : DecisionTree n, t.depth ≤ d ∧ ∀ x, t.eval x = f x) ∧
  (∀ t : DecisionTree n, (∀ x, t.eval x = f x) → t.depth ≥ d)

-- ════════════════════════════════════════════════════════════
-- Section 2: Protocol → Decision tree simulation
-- ════════════════════════════════════════════════════════════

/-- Simulate a protocol tree with a decision tree (both players get same input). -/
def proto_to_dt {n : Nat} : ProtocolTree n n Bool → DecisionTree n
  | .leaf v => .leaf v
  | .alice_sends q p0 p1 => .query q (proto_to_dt p0) (proto_to_dt p1)
  | .bob_sends q p0 p1 => .query q (proto_to_dt p0) (proto_to_dt p1)

theorem proto_to_dt_depth {n : Nat} (p : ProtocolTree n n Bool) :
    (proto_to_dt p).depth = p.depth := by
  induction p with
  | leaf _ => rfl
  | alice_sends _ _ _ ih0 ih1 =>
    simp [proto_to_dt, DecisionTree.depth, ProtocolTree.depth, ih0, ih1]
  | bob_sends _ _ _ ih0 ih1 =>
    simp [proto_to_dt, DecisionTree.depth, ProtocolTree.depth, ih0, ih1]

theorem proto_to_dt_eval {n : Nat} (p : ProtocolTree n n Bool) (x : Fin n → Bool) :
    (proto_to_dt p).eval x = p.eval x x := by
  induction p with
  | leaf _ => rfl
  | alice_sends _ _ _ ih0 ih1 =>
    simp [proto_to_dt, DecisionTree.eval, ProtocolTree.eval]
    split <;> [exact ih1; exact ih0]
  | bob_sends _ _ _ ih0 ih1 =>
    simp [proto_to_dt, DecisionTree.eval, ProtocolTree.eval]
    split <;> [exact ih1; exact ih0]

-- ════════════════════════════════════════════════════════════
-- Section 3: Lifting Gadget
-- ════════════════════════════════════════════════════════════

/-- A lifting gadget: a structured substitution g: {0,1}^m → {0,1}. -/
structure LiftingGadget where
  /-- Number of bits per variable for each player -/
  bits_per_player : Nat
  /-- The gadget function -/
  gadget : (Fin bits_per_player → Bool) → (Fin bits_per_player → Bool) → Bool
  /-- Non-degeneracy: the gadget is not constant -/
  h_nondeg : ∃ a₁ b₁ a₂ b₂, gadget a₁ b₁ ≠ gadget a₂ b₂
  /-- Balance: for each Alice input, both outputs are reachable -/
  h_balanced : ∀ a : Fin bits_per_player → Bool,
    (∃ b, gadget a b = true) ∧ (∃ b, gadget a b = false)

/-- Helper: i * m + j < n * m when i < n and j < m. -/
private theorem mul_add_lt {i j n m : Nat} (hi : i < n) (hj : j < m) :
    i * m + j < n * m := by
  have h1 : i * m + j < i * m + m := Nat.add_lt_add_left hj _
  have h2 : i * m + m = i * m + 1 * m := by simp
  have h3 : i * m + 1 * m = (i + 1) * m := by simp [Nat.add_mul]
  have h4 : (i + 1) ≤ n := hi
  have h5 : (i + 1) * m ≤ n * m := Nat.mul_le_mul_right m h4
  omega

/-- The lifted function: f composed with gadget substitution. -/
def liftedFunction (n : Nat) (f : (Fin n → Bool) → Bool)
    (g : LiftingGadget) :
    (Fin (n * g.bits_per_player) → Bool) →
    (Fin (n * g.bits_per_player) → Bool) → Bool :=
  fun alice_input bob_input =>
    f (fun i =>
      g.gadget
        (fun j => alice_input ⟨i.val * g.bits_per_player + j.val,
          mul_add_lt i.isLt j.isLt⟩)
        (fun j => bob_input ⟨i.val * g.bits_per_player + j.val,
          mul_add_lt i.isLt j.isLt⟩))

-- ════════════════════════════════════════════════════════════
-- Section 4: Lifting Faithfulness and Lifting Theorem Structure
-- ════════════════════════════════════════════════════════════

/-- The faithfulness condition for a lifting gadget:
    query complexity lower bounds lift to communication complexity lower bounds
    by a fixed multiplicative factor.

    This is the core bridge condition of the Raz-McKenzie / Goos-Pitassi-Watson
    lifting theorem. It is the Chain 2 analog of CookFaithful, DefinabilityFaithful,
    and the faithfulness conditions in other chains: it asserts that the gadget
    substitution faithfully encodes decision-tree hardness into protocol hardness. -/
structure LiftingFaithful where
  /-- The lifting gadget performing the substitution -/
  gadget : LiftingGadget
  /-- The multiplicative factor by which query depth lifts to protocol depth -/
  lift_factor : Nat
  /-- Positivity of the lift factor -/
  h_factor_pos : lift_factor > 0
  /-- The faithfulness condition: any protocol for the lifted function
      has depth at least lift_factor times the query lower bound -/
  h_faithful : ∀ (n d : Nat) (f : (Fin n → Bool) → Bool),
    (∀ t : DecisionTree n, (∀ x, t.eval x = f x) → t.depth ≥ d) →
    ∀ (proto : ProtocolTree (n * gadget.bits_per_player)
                             (n * gadget.bits_per_player) Bool),
      (∀ a b, proto.eval a b = liftedFunction n f gadget a b) →
      proto.depth ≥ lift_factor * d

/-- A lifting theorem: a gadget g lifts query complexity lower bounds
    to communication complexity lower bounds.

    The h_lifts field is the OPEN BRIDGE CONDITION.
    See LiftingFaithful for the standalone faithfulness structure. -/
structure LiftingTheorem where
  gadget : LiftingGadget
  lift_factor : Nat
  h_factor_pos : lift_factor > 0
  h_lifts : ∀ (n d : Nat) (f : (Fin n → Bool) → Bool),
    (∀ t : DecisionTree n, (∀ x, t.eval x = f x) → t.depth ≥ d) →
    ∀ (proto : ProtocolTree (n * gadget.bits_per_player)
                             (n * gadget.bits_per_player) Bool),
      (∀ a b, proto.eval a b = liftedFunction n f gadget a b) →
      proto.depth ≥ lift_factor * d

/-- Extract the faithfulness condition from a LiftingTheorem as a standalone LiftingFaithful. -/
def LiftingTheorem.toLiftingFaithful (lt : LiftingTheorem) : LiftingFaithful where
  gadget       := lt.gadget
  lift_factor  := lt.lift_factor
  h_factor_pos := lt.h_factor_pos
  h_faithful   := lt.h_lifts

-- ════════════════════════════════════════════════════════════
-- Section 5: Transfer theorem
-- ════════════════════════════════════════════════════════════

/-- A lifting theorem transfers a query lower bound to a comm lower bound. -/
theorem lifting_transfers_lower_bound
    (lt : LiftingTheorem) (n d : Nat) (f : (Fin n → Bool) → Bool)
    (h_query_lower : ∀ t : DecisionTree n, (∀ x, t.eval x = f x) → t.depth ≥ d)
    (proto : ProtocolTree (n * lt.gadget.bits_per_player)
                           (n * lt.gadget.bits_per_player) Bool)
    (h_correct : ∀ a b, proto.eval a b = liftedFunction n f lt.gadget a b) :
    proto.depth ≥ lt.lift_factor * d :=
  lt.h_lifts n d f h_query_lower proto h_correct

-- ════════════════════════════════════════════════════════════
-- Section 6: comm_ge_query
-- ════════════════════════════════════════════════════════════

/-- Any protocol for f (with same input for both players) has depth ≥ query depth. -/
theorem comm_ge_query (n : Nat) (f : (Fin n → Bool) → Bool)
    (d : Nat)
    (h_query : ∀ t : DecisionTree n, (∀ x, t.eval x = f x) → t.depth ≥ d) :
    ∀ (proto : ProtocolTree n n Bool),
      (∀ x, proto.eval x x = f x) →
      proto.depth ≥ d := by
  intro proto hproto
  -- Build a decision tree simulating the protocol
  have hbuild : ∀ x, (proto_to_dt proto).eval x = f x := fun x => by
    rw [proto_to_dt_eval proto x]; exact hproto x
  have := h_query (proto_to_dt proto) hbuild
  rwa [proto_to_dt_depth] at this

-- ════════════════════════════════════════════════════════════
-- Section 7: Non-constant function lower bound
-- ════════════════════════════════════════════════════════════

/-- A non-constant function requires depth ≥ 1. -/
theorem nonconstant_dt_lb {n : Nat} (f : (Fin n → Bool) → Bool)
    (h_nonconst : ∃ x y, f x ≠ f y) :
    ∀ t : DecisionTree n, (∀ x, t.eval x = f x) → t.depth ≥ 1 := by
  intro t ht
  match t with
  | .leaf v =>
    obtain ⟨x, y, hxy⟩ := h_nonconst
    exfalso
    have hx := ht x; have hy := ht y
    simp only [DecisionTree.eval] at hx hy
    exact hxy (hx.symm.trans hy)
  | .query _ _ _ =>
    simp [DecisionTree.depth]

-- ════════════════════════════════════════════════════════════
-- Section 8: Vacuous bound
-- ════════════════════════════════════════════════════════════

-- ════════════════════════════════════════════════════════════
-- Section 9: A trivial LiftingGadget (XOR with 1 bit)
-- ════════════════════════════════════════════════════════════

/-- A trivial 1-bit lifting gadget: gadget(a, b) = a 0 XOR b 0.
    Balanced and non-degenerate. -/
def xorGadget : LiftingGadget where
  bits_per_player := 1
  gadget := fun a b => (a ⟨0, Nat.zero_lt_one⟩) ^^ (b ⟨0, Nat.zero_lt_one⟩)
  h_nondeg :=
    ⟨fun _ => true, fun _ => false,
     fun _ => false, fun _ => false,
     by decide⟩
  h_balanced := fun a =>
    ⟨⟨fun _ => !(a ⟨0, Nat.zero_lt_one⟩), by
      cases (a ⟨0, Nat.zero_lt_one⟩) <;> rfl⟩,
     ⟨fun _ => a ⟨0, Nat.zero_lt_one⟩, by
      simp⟩⟩

-- ════════════════════════════════════════════════════════════
-- Section 10: Decision tree → Protocol tree simulation
-- ════════════════════════════════════════════════════════════

/-- Convert a decision tree to a protocol tree (Alice-only protocol).
    Each query node becomes an alice_sends node; leaf maps to leaf. -/
def dt_to_proto {n : Nat} : DecisionTree n → ProtocolTree n n Bool
  | .leaf v => .leaf v
  | .query i t0 t1 => .alice_sends i (dt_to_proto t0) (dt_to_proto t1)

theorem dt_to_proto_depth {n : Nat} (t : DecisionTree n) :
    (dt_to_proto t).depth = t.depth := by
  induction t with
  | leaf _ => rfl
  | query _ _ _ ih0 ih1 =>
    simp [dt_to_proto, ProtocolTree.depth, DecisionTree.depth, ih0, ih1]

theorem dt_to_proto_eval {n : Nat} (t : DecisionTree n) (x : Fin n → Bool) :
    (dt_to_proto t).eval x x = t.eval x := by
  induction t with
  | leaf _ => rfl
  | query _ _ _ ih0 ih1 =>
    simp [dt_to_proto, ProtocolTree.eval, DecisionTree.eval]
    split <;> [exact ih1; exact ih0]

/-- Roundtrip: dt_to_proto ∘ proto_to_dt produces a protocol that evaluates
    identically to the original at same-inputs.
    This is the key property for the Chain 2 model: the flatten-and-re-embed
    operation preserves evaluation semantics on the diagonal. -/
theorem proto_to_dt_to_proto_eval {n : Nat} (p : ProtocolTree n n Bool)
    (x : Fin n → Bool) :
    (dt_to_proto (proto_to_dt p)).eval x x = p.eval x x := by
  rw [dt_to_proto_eval, proto_to_dt_eval]

/-- The roundtrip dt_to_proto ∘ proto_to_dt preserves depth exactly. -/
theorem proto_to_dt_to_proto_depth {n : Nat} (p : ProtocolTree n n Bool) :
    (dt_to_proto (proto_to_dt p)).depth = p.depth := by
  rw [dt_to_proto_depth, proto_to_dt_depth]

/-- The roundtrip dt_to_proto ∘ proto_to_dt does not increase depth
    (trivially, since it preserves depth exactly). -/
theorem proto_to_dt_to_proto_depth_le {n : Nat} (p : ProtocolTree n n Bool) :
    (dt_to_proto (proto_to_dt p)).depth ≤ p.depth := by
  rw [proto_to_dt_to_proto_depth]

/-- Idempotence of the flatten operation: applying proto_to_dt ∘ dt_to_proto
    to an already-flattened tree returns the same tree. -/
theorem dt_to_proto_to_dt {n : Nat} (t : DecisionTree n) :
    proto_to_dt (dt_to_proto t) = t := by
  induction t with
  | leaf _ => rfl
  | query _ _ _ ih0 ih1 =>
    simp [dt_to_proto, proto_to_dt, ih0, ih1]

/-- Double roundtrip idempotence on the protocol side:
    dt_to_proto (proto_to_dt (dt_to_proto (proto_to_dt p))) = dt_to_proto (proto_to_dt p). -/
theorem dt_to_proto_roundtrip_idempotent {n : Nat} (p : ProtocolTree n n Bool) :
    dt_to_proto (proto_to_dt (dt_to_proto (proto_to_dt p))) =
    dt_to_proto (proto_to_dt p) := by
  congr 1; exact dt_to_proto_to_dt (proto_to_dt p)

end ClassicalConstraints
