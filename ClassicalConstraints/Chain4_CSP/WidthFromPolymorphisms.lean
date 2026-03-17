/-
Copyright (c) 2026 Larsen Close. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Larsen Close

ClassicalConstraints/WidthFromPolymorphisms.lean — Bounded width and
polymorphism arity correspondence (Barto-Kozik 2014).

STATUS: 0 sorry, Classical.choice allowed (Side B).
-/

import ClassicalConstraints.Chain4_CSP.CSPInstanceCore
import ClassicalConstraints.Chain4_CSP.PolymorphismCore
import ClassicalConstraints.Chain4_CSP.TractabilityDichotomy
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Finset.Basic

namespace ClassicalConstraints

-- ════════════════════════════════════════════════════════════
-- Section 1: Partial assignments and consistency
-- ════════════════════════════════════════════════════════════

/-- A partial assignment: assigns values to some variables (None = unassigned). -/
def PartialAssignment (dom : CSPDomain) (num_vars : Nat) :=
  Fin num_vars → Option dom.D

/-- The support of a partial assignment: variables that are assigned. -/
def PartialAssignment.support {dom : CSPDomain} {n : Nat}
    (pa : PartialAssignment dom n) : Finset (Fin n) :=
  Finset.filter (fun v => (pa v).isSome) Finset.univ

/-- A partial assignment is consistent with a constraint if,
    whenever all variables in the constraint's scope are assigned,
    the resulting tuple is in the relation. -/
def partialConsistent {dom : CSPDomain}
    {lang : ConstraintLanguage dom}
    (inst : CSPInstance dom lang)
    (pa : PartialAssignment dom inst.num_vars)
    (c : Σ (idx : Fin lang.rels.length),
      Fin (lang.rels[idx].1) → Fin inst.num_vars) : Prop :=
  (∀ i, (pa (c.2 i)).isSome) →
  (lang.rels[c.1]).2.mem (fun i =>
    match pa (c.2 i) with
    | some v => v
    | none => Classical.choice (by
        have h : @Fintype.card dom.D dom.fin ≥ 2 := dom.card_ge_two
        exact @Fintype.card_pos_iff dom.D dom.fin |>.mp (by omega))) = true

-- ════════════════════════════════════════════════════════════
-- Section 2: (k,l)-consistency
-- ════════════════════════════════════════════════════════════

/-- (k,l)-consistency: a CSP instance is (k,l)-consistent if
    every consistent partial assignment on at most k variables
    can be extended to a consistent partial assignment on at most
    l variables. Here l >= k. -/
structure KLConsistency (dom : CSPDomain)
    (lang : ConstraintLanguage dom)
    (inst : CSPInstance dom lang) (k l : Nat) where
  /-- k <= l. -/
  hkl : k ≤ l
  /-- Extension property. -/
  extends_consistent :
    ∀ (pa : PartialAssignment dom inst.num_vars),
      pa.support.card ≤ k →
      (∀ c ∈ inst.constraints, partialConsistent inst pa c) →
      ∀ (v : Fin inst.num_vars), v ∉ pa.support →
      ∃ (pa' : PartialAssignment dom inst.num_vars),
        pa'.support.card ≤ l ∧
        (∀ w ∈ pa.support, pa' w = pa w) ∧
        (pa' v).isSome ∧
        (∀ c ∈ inst.constraints, partialConsistent inst pa' c)

/-- A consistency decision algorithm for a constraint language. -/
structure ConsistencyAlgorithm (dom : CSPDomain)
    (lang : ConstraintLanguage dom) (k l : Nat) where
  decide : CSPInstance dom lang → Bool
  sound : ∀ inst, decide inst = true → inst.Satisfiable dom lang
  complete : ∀ inst, inst.Satisfiable dom lang → decide inst = true

/-- CSP(Gamma) has bounded width if there exist k,l such that
    (k,l)-consistency decides CSP(Gamma). -/
structure HasBoundedWidth (dom : CSPDomain)
    (lang : ConstraintLanguage dom) where
  k : Nat
  l : Nat
  hkl : k ≤ l
  decides : ∀ inst : CSPInstance dom lang,
    Nonempty (KLConsistency dom lang inst k l) ↔
    inst.Satisfiable dom lang

-- ════════════════════════════════════════════════════════════
-- Section 3: Width-polymorphism correspondence (structure)
-- ════════════════════════════════════════════════════════════

/-- The width-polymorphism correspondence (Barto-Kozik 2014):
    CSP(Gamma) has bounded width iff Pol(Gamma) contains WNU
    operations of all sufficiently high arities.
    Carried as structure with axiom-level trust. -/
structure WidthPolymorphismCorrespondence (dom : CSPDomain)
    (lang : ConstraintLanguage dom) where
  width_implies_wnus :
    HasBoundedWidth dom lang →
    ∃ k₀, ∀ k, k ≥ k₀ →
      ∃ (w : WNU dom.D k), isPolymorphism lang w.op
  wnus_imply_width :
    (∃ k₀, ∀ k, k ≥ k₀ →
      ∃ (w : WNU dom.D k), isPolymorphism lang w.op) →
    HasBoundedWidth dom lang

-- ════════════════════════════════════════════════════════════
-- Section 4: Proved theorems
-- ════════════════════════════════════════════════════════════

/-- A language with bounded width is tractable (via the BulatovZhuk dichotomy
    and width-polymorphism correspondence). -/
def bounded_width_is_tractable (dom : CSPDomain)
    (lang : ConstraintLanguage dom)
    (hw : HasBoundedWidth dom lang)
    (wpc : WidthPolymorphismCorrespondence dom lang)
    (bz : BulatovZhukDichotomy dom lang) :
    CSPTractable dom lang :=
  -- Get WNUs at all large arities from width.
  let h_wnus := wpc.width_implies_wnus hw
  let k₀ := Classical.choose h_wnus
  let hwnus := Classical.choose_spec h_wnus
  -- Use WNU at arity max(2, k₀).
  let hk : max 2 k₀ ≥ 2 := le_max_left 2 k₀
  let hk₀ : max 2 k₀ ≥ k₀ := le_max_right 2 k₀
  let h_w := hwnus (max 2 k₀) hk₀
  let w := Classical.choose h_w
  let hw_pol := Classical.choose_spec h_w
  -- Apply Bulatov-Zhuk dichotomy.
  bz.dichotomy ⟨max 2 k₀, hk, w, hw_pol⟩

/-- WNUs of all large arities implies bounded width (via wpc).
    This is the algebraic witness for tractability. -/
def wnu_family_gives_bounded_width (dom : CSPDomain)
    (lang : ConstraintLanguage dom)
    (wpc : WidthPolymorphismCorrespondence dom lang)
    (k₀ : Nat)
    (hwnus : ∀ k, k ≥ k₀ →
      ∃ (w : WNU dom.D k), isPolymorphism lang w.op) :
    HasBoundedWidth dom lang :=
  wpc.wnus_imply_width ⟨k₀, hwnus⟩

/-- Arc consistency (width 2) suffices for languages with majority polymorphism.
    This is the algebraic explanation of why 2-SAT is in P. -/
def majority_gives_bounded_width (dom : CSPDomain)
    (lang : ConstraintLanguage dom)
    (m : MajorityOp dom.D)
    (hm : isPolymorphism lang m.op)
    (wpc : WidthPolymorphismCorrespondence dom lang) :
    HasBoundedWidth dom lang :=
  -- majority is a StrongWNU (use Classical.choose to extract from ∃).
  let h_sw := majority_is_strong_wnu dom.D m
  let sw := Classical.choose h_sw
  let hswop := Classical.choose_spec h_sw
  -- For each arity k ≥ 3, construct WNU of arity k from StrongWNU.
  -- op_k(args) := sw.op (fun (i : Fin 3) => args (Fin.castLE hk3 i)) where hk3 : 3 ≤ k.
  wpc.wnus_imply_width ⟨3, fun k hk => by
  let embed : Fin 3 → Fin k := Fin.castLE hk
  obtain ⟨w_k, hw_k_eq⟩ := strong_wnu_via_val_embedding sw embed (fun _ => rfl)
  refine ⟨w_k, ?_⟩
  intro rel_idx rows hrows
  have key := hm rel_idx (fun m3 col => rows (embed m3) col)
    (fun m3 => hrows (embed m3))
  convert key using 2
  funext j
  rw [hw_k_eq, hswop]
  ⟩

/-- 3-SAT does not have bounded width, given no WNU and the
    width-polymorphism correspondence. -/
theorem threeSAT_no_bounded_width (lang : ConstraintLanguage boolDomain)
    (_ : ∀ (_ : BoolClause 3), ∃ idx : Fin lang.rels.length,
      (lang.rels[idx]).1 = 3)
    (h_no_wnu : ¬∃ k, k ≥ 2 ∧ ∃ (w : WNU Bool k), isPolymorphism lang w.op)
    (wpc : WidthPolymorphismCorrespondence boolDomain lang) :
    ¬Nonempty (HasBoundedWidth boolDomain lang) := by
  intro ⟨hw⟩
  -- Bounded width implies WNUs of all large arities (Barto-Kozik, in wpc).
  obtain ⟨k₀, hwnus⟩ := wpc.width_implies_wnus hw
  -- k₀ may be 0 or 1; we need k ≥ 2.
  apply h_no_wnu
  exact ⟨max 2 k₀, le_max_left 2 k₀, hwnus (max 2 k₀) (le_max_right 2 k₀)⟩

end ClassicalConstraints
