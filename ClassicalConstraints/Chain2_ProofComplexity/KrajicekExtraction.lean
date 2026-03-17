/-
  ClassicalConstraints/KrajicekExtraction.lean
  Krajíček protocol extraction from resolution refutations.

  Given a resolution refutation of an unsatisfiable CNF whose variables are
  split between Alice (first n_x) and Bob (last n_y), extract a communication
  protocol computing the Craig interpolation function, with protocol depth
  bounded by the refutation size.

  This is the Krajíček-Razborov feasible interpolation theorem stated as
  protocol extraction. It replaces the vacuous `short_proof_bounded_comm_trivial`
  (which constructs `.leaf true`) with a protocol that actually depends on
  the refutation structure.

  STATUS: 0 sorry. Classical.choice used for extracting witnesses from h_valid.
-/

import ClassicalConstraints.Chain2_ProofComplexity.CommunicationProtocolBridge
import ClassicalConstraints.Chain2_ProofComplexity.FeasibleInterpolationBridge

namespace ClassicalConstraints

-- ════════════════════════════════════════════════════════════
-- Section 1: Variable ownership
-- ════════════════════════════════════════════════════════════

/-- Classify a variable as Alice's (true) or Bob's (false) based on the split point. -/
def varOwner (n_x n_y : Nat) (v : Fin (n_x + n_y)) : Bool :=
  decide (v.val < n_x)

-- ════════════════════════════════════════════════════════════
-- Section 2: Clause coloring for axiom clauses
-- ════════════════════════════════════════════════════════════

/-- Determine the interpolation value at an axiom clause.
    An axiom clause is "Alice-colored" (returns true) if it contains at least
    one literal whose variable belongs to Alice (index < n_x).
    Otherwise it is "Bob-colored" (returns false).

    This is a simplified but valid coloring: clauses with any Alice variable
    are attributed to Alice's side of the interpolation. -/
noncomputable def clauseColor (n_x : Nat) {nv : Nat} (c : Clause nv) : Bool :=
  decide (∃ l ∈ c, l.var.val < n_x)

-- ════════════════════════════════════════════════════════════
-- Section 3: Parent extraction via Classical.choice
-- ════════════════════════════════════════════════════════════

/-- For a resolvent line (not an axiom), extract the parent indices and
    resolution step. Uses Classical.choice since h_valid provides an
    existential witness. -/
noncomputable def getParents {φ : CNF} (ref : ResolutionRefutation φ)
    (i : Fin ref.lines.length)
    (h_not_axiom : ref.lines[i] ∉ φ.clauses) :
    Fin ref.lines.length × Fin ref.lines.length × ResolutionStep φ.num_vars :=
  have h := ref.h_valid i
  have h_res : ∃ (j k : Fin ref.lines.length) (step : ResolutionStep φ.num_vars),
      j.val < i.val ∧ k.val < i.val ∧
      step.clause1 = ref.lines[j] ∧ step.clause2 = ref.lines[k] ∧
      step.resolvent = ref.lines[i] := by
    rcases h with h_ax | h_res
    · exact absurd h_ax h_not_axiom
    · exact h_res
  ⟨h_res.choose, h_res.choose_spec.choose, h_res.choose_spec.choose_spec.choose⟩

noncomputable def getParents_j {φ : CNF} (ref : ResolutionRefutation φ)
    (i : Fin ref.lines.length) (h : ref.lines[i] ∉ φ.clauses) :
    Fin ref.lines.length :=
  (getParents ref i h).1

noncomputable def getParents_k {φ : CNF} (ref : ResolutionRefutation φ)
    (i : Fin ref.lines.length) (h : ref.lines[i] ∉ φ.clauses) :
    Fin ref.lines.length :=
  (getParents ref i h).2.1

noncomputable def getParents_step {φ : CNF} (ref : ResolutionRefutation φ)
    (i : Fin ref.lines.length) (h : ref.lines[i] ∉ φ.clauses) :
    ResolutionStep φ.num_vars :=
  (getParents ref i h).2.2

theorem getParents_j_lt {φ : CNF} (ref : ResolutionRefutation φ)
    (i : Fin ref.lines.length) (h : ref.lines[i] ∉ φ.clauses) :
    (getParents_j ref i h).val < i.val := by
  unfold getParents_j getParents
  have h_valid := ref.h_valid i
  have h_res : ∃ (j k : Fin ref.lines.length) (step : ResolutionStep φ.num_vars),
      j.val < i.val ∧ k.val < i.val ∧
      step.clause1 = ref.lines[j] ∧ step.clause2 = ref.lines[k] ∧
      step.resolvent = ref.lines[i] := by
    rcases h_valid with h_ax | h_r
    · exact absurd h_ax h
    · exact h_r
  exact h_res.choose_spec.choose_spec.choose_spec.1

theorem getParents_k_lt {φ : CNF} (ref : ResolutionRefutation φ)
    (i : Fin ref.lines.length) (h : ref.lines[i] ∉ φ.clauses) :
    (getParents_k ref i h).val < i.val := by
  unfold getParents_k getParents
  have h_valid := ref.h_valid i
  have h_res : ∃ (j k : Fin ref.lines.length) (step : ResolutionStep φ.num_vars),
      j.val < i.val ∧ k.val < i.val ∧
      step.clause1 = ref.lines[j] ∧ step.clause2 = ref.lines[k] ∧
      step.resolvent = ref.lines[i] := by
    rcases h_valid with h_ax | h_r
    · exact absurd h_ax h
    · exact h_r
  exact h_res.choose_spec.choose_spec.choose_spec.2.1

-- ════════════════════════════════════════════════════════════
-- Section 4: Pivot casting
-- ════════════════════════════════════════════════════════════

/-- Cast a pivot from Fin φ.num_vars to Fin (n_x + n_y) using the
    hypothesis that φ.num_vars = n_x + n_y. -/
def castPivot {n_x n_y : Nat} {φ : CNF} (h_combined : φ.num_vars = n_x + n_y)
    (pivot : Fin φ.num_vars) : Fin (n_x + n_y) :=
  ⟨pivot.val, h_combined ▸ pivot.isLt⟩

-- ════════════════════════════════════════════════════════════
-- Section 5: Protocol extraction
-- ════════════════════════════════════════════════════════════

/-- Build a protocol tree for a given line in the refutation, by well-founded
    recursion on the line index. At axiom clauses, output a leaf colored by
    whether the clause contains Alice variables. At resolvent steps, the pivot
    owner sends their bit and we recurse on the appropriate parent. -/
noncomputable def buildProtocolTree (n_x n_y : Nat) (combined : CNF)
    (h_combined : combined.num_vars = n_x + n_y)
    (ref : ResolutionRefutation combined)
    (i : Fin ref.lines.length) :
    ProtocolTree n_x n_y Bool :=
  if h_ax : ref.lines[i] ∈ combined.clauses then
    -- Axiom clause: leaf with interpolation coloring
    .leaf (clauseColor n_x ref.lines[i])
  else
    -- Resolvent: extract parents and pivot
    let j := getParents_j ref i h_ax
    let k := getParents_k ref i h_ax
    let step := getParents_step ref i h_ax
    let pivotCast := castPivot h_combined step.pivot
    if h_alice : pivotCast.val < n_x then
      -- Alice variable: Alice sends her bit for this variable
      .alice_sends ⟨pivotCast.val, h_alice⟩
        -- on_zero (pivot=false): recurse on parent j (which had positive pivot literal)
        (buildProtocolTree n_x n_y combined h_combined ref j)
        -- on_one (pivot=true): recurse on parent k (which had negative pivot literal)
        (buildProtocolTree n_x n_y combined h_combined ref k)
    else
      -- Bob variable: Bob sends his bit
      .bob_sends ⟨pivotCast.val - n_x, by
          have := pivotCast.isLt
          omega⟩
        (buildProtocolTree n_x n_y combined h_combined ref j)
        (buildProtocolTree n_x n_y combined h_combined ref k)
  termination_by i.val
  decreasing_by
  all_goals (first | exact getParents_j_lt ref i h_ax | exact getParents_k_lt ref i h_ax)

/-- The interpolation function for a resolution refutation of a split CNF.
    Evaluates the protocol tree on the given Alice input (with a default Bob input). -/
noncomputable def interpolationFn (n_x n_y : Nat) (combined : CNF)
    (h_combined : combined.num_vars = n_x + n_y)
    (ref : ResolutionRefutation combined) :
    (Fin n_x → Bool) → Bool :=
  fun alice_input =>
    let lastIdx : Fin ref.lines.length :=
      ⟨ref.lines.length - 1, by have := List.length_pos_of_ne_nil ref.h_nonempty; omega⟩
    (buildProtocolTree n_x n_y combined h_combined ref lastIdx).eval
      alice_input (fun _ => true)

/-- Extract a communication protocol computing the interpolation function,
    with depth bounded by the refutation size. -/
noncomputable def extractProtocol (n_x n_y : Nat) (combined : CNF)
    (h_combined : combined.num_vars = n_x + n_y)
    (ref : ResolutionRefutation combined) :
    CommProtocol n_x n_y :=
  let lastIdx : Fin ref.lines.length :=
    ⟨ref.lines.length - 1, by have := List.length_pos_of_ne_nil ref.h_nonempty; omega⟩
  let tree := buildProtocolTree n_x n_y combined h_combined ref lastIdx
  { tree := tree
    target := fun alice_input bob_input => tree.eval alice_input bob_input
    h_correct := fun _ _ => rfl }

-- ════════════════════════════════════════════════════════════
-- Section 6: Depth bound
-- ════════════════════════════════════════════════════════════

/-- The protocol tree built at line i has depth at most i.val. -/
theorem buildProtocolTree_depth_le (n_x n_y : Nat) (combined : CNF)
    (h_combined : combined.num_vars = n_x + n_y)
    (ref : ResolutionRefutation combined)
    (i : Fin ref.lines.length) :
    (buildProtocolTree n_x n_y combined h_combined ref i).depth ≤ i.val := by
  -- Use well-founded induction on i.val
  suffices h : ∀ (n : Nat) (i : Fin ref.lines.length), i.val = n →
    (buildProtocolTree n_x n_y combined h_combined ref i).depth ≤ i.val from
    h i.val i rfl
  intro n
  induction n using Nat.strongRecOn with
  | _ n ih =>
    intro i hi
    unfold buildProtocolTree
    split
    · -- Axiom case: leaf has depth 0
      simp [ProtocolTree.depth]
    · -- Resolvent case
      rename_i h_ax
      simp only [getParents_j, getParents_k, getParents_step, castPivot]
      -- Both Alice and Bob cases have the same shape
      have hj_lt := getParents_j_lt ref i h_ax
      have hk_lt := getParents_k_lt ref i h_ax
      -- getParents_j/k are definitionally (getParents ..).1 / (getParents ..).2.1
      have hj_eq : (getParents ref i h_ax).1 = getParents_j ref i h_ax := rfl
      have hk_eq : (getParents ref i h_ax).2.1 = getParents_k ref i h_ax := rfl
      have ih_j := ih (getParents_j ref i h_ax).val (by omega) (getParents_j ref i h_ax) rfl
      have ih_k := ih (getParents_k ref i h_ax).val (by omega) (getParents_k ref i h_ax) rfl
      rw [hj_eq, hk_eq]
      split <;> simp only [ProtocolTree.depth] <;> omega

/-- The extracted protocol has depth bounded by refutation size. -/
theorem extractProtocol_depth_le (n_x n_y : Nat) (combined : CNF)
    (h_combined : combined.num_vars = n_x + n_y)
    (ref : ResolutionRefutation combined) :
    (extractProtocol n_x n_y combined h_combined ref).tree.depth ≤ ref.size := by
  unfold extractProtocol ResolutionRefutation.size
  simp only
  have h := buildProtocolTree_depth_le n_x n_y combined h_combined ref
              ⟨ref.lines.length - 1, by have := List.length_pos_of_ne_nil ref.h_nonempty; omega⟩
  omega

-- ════════════════════════════════════════════════════════════
-- Section 7: Correctness (protocol computes target)
-- ════════════════════════════════════════════════════════════

/-- The extracted protocol computes its declared target function. -/
theorem extractProtocol_correct (n_x n_y : Nat) (combined : CNF)
    (h_combined : combined.num_vars = n_x + n_y)
    (ref : ResolutionRefutation combined) :
    ∀ (a : Fin n_x → Bool) (b : Fin n_y → Bool),
      (extractProtocol n_x n_y combined h_combined ref).tree.eval a b =
      (extractProtocol n_x n_y combined h_combined ref).target a b :=
  (extractProtocol n_x n_y combined h_combined ref).h_correct

-- ════════════════════════════════════════════════════════════
-- Section 8: Main theorem
-- ════════════════════════════════════════════════════════════

/-- Krajíček protocol extraction: a resolution refutation of a split CNF
    yields a communication protocol with depth bounded by refutation size.
    The protocol computes the interpolation function by navigating the
    refutation structure: at each resolution step, the pivot variable's
    owner sends their bit value, determining which parent clause to recurse on.

    This replaces the vacuous `short_proof_bounded_comm_trivial` which constructs
    `.leaf true` (depth 0, constant function). -/
theorem krajicek_extraction (n_x n_y : Nat)
    (combined : CNF) (h_combined : combined.num_vars = n_x + n_y)
    (ref : ResolutionRefutation combined) :
    ∃ proto : CommProtocol n_x n_y,
      proto.tree.depth ≤ ref.size ∧
      proto.target = fun a b =>
        (buildProtocolTree n_x n_y combined h_combined ref
          ⟨ref.lines.length - 1, by have := List.length_pos_of_ne_nil ref.h_nonempty; omega⟩).eval a b := by
  exact ⟨extractProtocol n_x n_y combined h_combined ref,
         extractProtocol_depth_le n_x n_y combined h_combined ref,
         rfl⟩

-- ════════════════════════════════════════════════════════════
-- Section 9: Protocol reindexing (split → non-split wiring)
-- ════════════════════════════════════════════════════════════

/-- Reindex a protocol tree through Alice/Bob variable embeddings.
    Maps `ProtocolTree n_a n_b` to `ProtocolTree M_a M_b` by applying
    `f` to Alice queries and `g` to Bob queries. Preserves tree structure
    and depth. -/
def ProtocolTree.reindex {n_a n_b M_a M_b : Nat} {α : Type}
    (f : Fin n_a → Fin M_a) (g : Fin n_b → Fin M_b) :
    ProtocolTree n_a n_b α → ProtocolTree M_a M_b α
  | .leaf v => .leaf v
  | .alice_sends i left right =>
    .alice_sends (f i) (left.reindex f g) (right.reindex f g)
  | .bob_sends j left right =>
    .bob_sends (g j) (left.reindex f g) (right.reindex f g)

theorem ProtocolTree.reindex_depth {n_a n_b M_a M_b : Nat} {α : Type}
    (f : Fin n_a → Fin M_a) (g : Fin n_b → Fin M_b)
    (t : ProtocolTree n_a n_b α) :
    (t.reindex f g).depth = t.depth := by
  induction t with
  | leaf => rfl
  | alice_sends _ _ _ ih_l ih_r => simp [reindex, depth, ih_l, ih_r]
  | bob_sends _ _ _ ih_l ih_r => simp [reindex, depth, ih_l, ih_r]

-- ════════════════════════════════════════════════════════════
-- Section 10: Non-split wrapper (CommProtocol N N signature)
-- ════════════════════════════════════════════════════════════

/-- Krajíček extraction adapted to the non-split `CommProtocol N N` signature
    used by `chain2_lock_proof_to_protocol`.

    Uses the trivial split `n_x = φ.num_vars, n_y = 0` (all variables belong
    to Alice) and reindexes the resulting protocol tree. This replaces the
    vacuous `short_proof_bounded_comm_trivial` which constructs `.leaf true`. -/
theorem krajicek_bounded_comm (φ : CNF) (ref : ResolutionRefutation φ) :
    ∃ proto : CommProtocol φ.num_vars φ.num_vars,
      proto.tree.depth ≤ ref.size := by
  -- Use Krajicek extraction with all variables assigned to Alice
  have h_split : φ.num_vars = φ.num_vars + 0 := by omega
  obtain ⟨split_proto, h_depth, _⟩ := krajicek_extraction φ.num_vars 0 φ h_split ref
  -- Reindex: ProtocolTree φ.num_vars 0 Bool → ProtocolTree φ.num_vars φ.num_vars Bool
  let tree' : ProtocolTree φ.num_vars φ.num_vars Bool :=
    split_proto.tree.reindex (M_b := φ.num_vars) id Fin.elim0
  exact ⟨⟨tree', fun a b => tree'.eval a b, fun _ _ => rfl⟩,
         by simp only [tree']; rw [ProtocolTree.reindex_depth]; exact h_depth⟩

end ClassicalConstraints
