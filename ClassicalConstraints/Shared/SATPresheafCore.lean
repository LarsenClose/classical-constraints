/-
  ClassicalConstraints/SATPresheafCore.lean
  SAT instances, assignments, local/global sections, and gluing.

  This file defines the combinatorial structure of SAT: variables,
  clauses, assignments, and the local-to-global passage from
  clause-level satisfiability to full satisfiability.
-/

import ClassicalConstraints.Shared.Basic
import Mathlib.Data.Fintype.Pi

/-! # SAT Presheaf Core

The presheaf perspective on SAT: each clause defines a "local site"
(its variables), a local section is a partial assignment satisfying
that clause, and a global section is a total assignment satisfying
all clauses. The gluing question — whether compatible local sections
extend to a global section — is exactly the satisfiability question. -/

namespace ClassicalConstraints

/-- A SAT instance: a number of variables and a list of clauses.
    Each clause is a list of signed integers: positive means the
    variable appears positive, negative means negated. Variables
    are 1-indexed in the literal encoding: literal `k` means
    variable `k-1`, literal `-k` means `¬(variable k-1)`. -/
structure SATInstance where
  num_vars : Nat
  clauses : List (List Int)

namespace SATInstance

/-- The set of variable indices appearing in a clause
    (absolute values of literals, converted to variable indices). -/
def clauseVars (clause : List Int) : List Nat :=
  clause.map (fun l => (Int.natAbs l) - 1)

/-- A total assignment of Boolean values to variables. -/
def Assignment (φ : SATInstance) : Type :=
  Fin φ.num_vars → Bool

/-- Whether a single literal is satisfied by an assignment.
    Literal `k` (k > 0) is satisfied when variable `k-1` is true.
    Literal `-k` (k > 0) is satisfied when variable `k-1` is false.
    Literal `0` is never satisfied.
    Out-of-range literals are vacuously not satisfied. -/
def literalSatisfied (φ : SATInstance) (a : φ.Assignment) (lit : Int) : Bool :=
  if lit == 0 then false
  else
    let idx := Int.natAbs lit - 1
    if hlt : idx < φ.num_vars then
      if lit > 0 then a ⟨idx, hlt⟩
      else !a ⟨idx, hlt⟩
    else false

/-- Whether a clause is satisfied: at least one literal is satisfied. -/
def clauseSatisfied (φ : SATInstance) (a : φ.Assignment) (clause : List Int) : Bool :=
  clause.any (literalSatisfied φ a)

/-- Whether all clauses of a SAT instance are satisfied by an assignment. -/
def instanceSatisfied (φ : SATInstance) (a : φ.Assignment) : Bool :=
  φ.clauses.all (clauseSatisfied φ a)

/-- A SAT instance is satisfiable if there exists a satisfying assignment. -/
def Satisfiable (φ : SATInstance) : Prop :=
  ∃ a : φ.Assignment, φ.instanceSatisfied a = true

/-! ## Local and Global Sections -/

/-- A local section for clause index `i`: a total assignment that
    satisfies that particular clause. We use a total assignment
    rather than a partial one to keep proofs simple — the "locality"
    is in which clause it certifies, not in the domain of the function. -/
structure LocalSection (φ : SATInstance) (i : Fin φ.clauses.length) where
  assignment : φ.Assignment
  satisfies : φ.clauseSatisfied assignment (φ.clauses.get i) = true

/-- A global section: a total assignment satisfying all clauses. -/
structure GlobalSection (φ : SATInstance) where
  assignment : φ.Assignment
  satisfies : φ.instanceSatisfied assignment = true

/-- Two local sections are compatible if they agree on all variables. -/
def LocalSection.compatible (φ : SATInstance) (i j : Fin φ.clauses.length)
    (si : LocalSection φ i) (sj : LocalSection φ j) : Prop :=
  si.assignment = sj.assignment

/-- The gluing problem: whether there exist pairwise compatible
    local sections covering all clauses. Since our local sections
    use total assignments, compatibility means they all use the
    same assignment. -/
def GluingProblem (φ : SATInstance) : Prop :=
  ∃ (sections : ∀ i : Fin φ.clauses.length, LocalSection φ i),
    ∀ i j, (sections i).assignment = (sections j).assignment

/-! ## Restriction and Gluing Theorems -/

/-- Helper: if instanceSatisfied is true, then every clause is satisfied. -/
theorem all_clauses_satisfied_of_instance (φ : SATInstance) (a : φ.Assignment)
    (h : φ.instanceSatisfied a = true) (i : Fin φ.clauses.length) :
    φ.clauseSatisfied a (φ.clauses.get i) = true := by
  unfold instanceSatisfied at h
  rw [List.all_eq_true] at h
  apply h
  exact List.get_mem _ _

/-- A global section restricts to a local section at each clause. -/
def global_gives_local (φ : SATInstance) (g : GlobalSection φ)
    (i : Fin φ.clauses.length) : LocalSection φ i :=
  ⟨g.assignment, all_clauses_satisfied_of_instance φ g.assignment g.satisfies i⟩

/-- The local sections obtained from a global section are pairwise compatible
    (they all use the same underlying assignment). -/
theorem global_sections_compatible (φ : SATInstance) (g : GlobalSection φ)
    (i j : Fin φ.clauses.length) :
    (global_gives_local φ g i).assignment = (global_gives_local φ g j).assignment := by
  rfl

/-- A global section solves the gluing problem. -/
theorem global_solves_gluing (φ : SATInstance) (g : GlobalSection φ) :
    GluingProblem φ := by
  exact ⟨global_gives_local φ g, global_sections_compatible φ g⟩

/-- Satisfiability implies the gluing problem is solvable. -/
theorem satisfiable_implies_gluing (φ : SATInstance) (h : φ.Satisfiable) :
    GluingProblem φ := by
  obtain ⟨a, ha⟩ := h
  exact global_solves_gluing φ ⟨a, ha⟩

/-- Helper: if we have compatible local sections using the same assignment,
    that assignment satisfies all clauses. -/
theorem compatible_locals_give_instance_sat (φ : SATInstance)
    (sections : ∀ i : Fin φ.clauses.length, LocalSection φ i)
    (a : φ.Assignment)
    (h_eq : ∀ i, (sections i).assignment = a) :
    φ.instanceSatisfied a = true := by
  unfold instanceSatisfied
  rw [List.all_eq_true]
  intro clause h_mem
  obtain ⟨i, hi⟩ := List.get_of_mem h_mem
  have := (sections i).satisfies
  rw [h_eq i] at this
  rw [← hi]
  exact this

/-- If the gluing problem is solvable, the instance is satisfiable. -/
theorem gluing_implies_satisfiable (φ : SATInstance) (h : GluingProblem φ) :
    φ.Satisfiable := by
  obtain ⟨sections, h_compat⟩ := h
  by_cases hlen : φ.clauses.length = 0
  · -- No clauses: any assignment works
    refine ⟨fun _ => true, ?_⟩
    unfold instanceSatisfied
    rw [List.all_eq_true]
    intro clause h_mem
    have : φ.clauses = [] := List.eq_nil_of_length_eq_zero hlen
    rw [this] at h_mem
    contradiction
  · -- At least one clause: use the first local section's assignment
    have hpos : 0 < φ.clauses.length := Nat.pos_of_ne_zero hlen
    let a := (sections ⟨0, hpos⟩).assignment
    refine ⟨a, ?_⟩
    apply compatible_locals_give_instance_sat φ sections a
    intro i
    exact h_compat i ⟨0, hpos⟩

/-- The gluing problem is solvable if and only if the instance is satisfiable. -/
theorem gluing_iff_satisfiable (φ : SATInstance) :
    GluingProblem φ ↔ φ.Satisfiable :=
  ⟨gluing_implies_satisfiable φ, satisfiable_implies_gluing φ⟩

/-! ## Connection to InstanceFamily -/

/-- Every SATInstance gives rise to a trivial InstanceFamily at a single size,
    where the instance type is Unit (there is one instance: the formula itself)
    and the witness type is the assignment type. -/
def toInstanceFamily (φ : SATInstance) : InstanceFamily where
  X := fun _ => Unit
  W := fun _ => Fin φ.num_vars → Bool
  Sat := fun _ _ w => φ.instanceSatisfied w = true
  h_dec := fun _ _ _ => inferInstance
  h_fin_X := fun _ => inferInstance
  h_fin_W := fun _ => inferInstance

/-! ## Concrete examples -/

/-- The empty SAT instance (no variables, no clauses) is satisfiable. -/
theorem empty_satisfiable : (⟨0, []⟩ : SATInstance).Satisfiable := by
  refine ⟨Fin.elim0, ?_⟩
  rfl

/-- A single empty clause is unsatisfiable. -/
theorem empty_clause_unsat : ¬(⟨0, [[]]⟩ : SATInstance).Satisfiable := by
  intro ⟨a, ha⟩
  simp [instanceSatisfied, clauseSatisfied] at ha

/-- The gluing problem for the empty instance is trivially solvable. -/
theorem empty_gluing : GluingProblem ⟨0, []⟩ := by
  rw [gluing_iff_satisfiable]
  exact empty_satisfiable

/-- A single unit clause (x₁) is satisfiable. -/
theorem unit_clause_sat : (⟨1, [[1]]⟩ : SATInstance).Satisfiable := by
  refine ⟨fun _ => true, ?_⟩
  decide

/-- A contradiction (x₁) ∧ (¬x₁) is unsatisfiable. -/
theorem contradiction_unsat : ¬(⟨1, [[1], [-1]]⟩ : SATInstance).Satisfiable := by
  intro ⟨a, ha⟩
  simp [instanceSatisfied, clauseSatisfied, literalSatisfied] at ha

end SATInstance

end ClassicalConstraints
