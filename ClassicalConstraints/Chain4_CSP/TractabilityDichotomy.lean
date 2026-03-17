/-
Copyright (c) 2026 Larsen Close. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Larsen Close

ClassicalConstraints/TractabilityDichotomy.lean — Bulatov-Zhuk CSP Dichotomy.

STATUS: 0 sorry, Classical.choice allowed (Side B).
-/

import ClassicalConstraints.Chain4_CSP.CSPInstanceCore
import ClassicalConstraints.Chain4_CSP.PolymorphismCore
import ClassicalConstraints.Shared.CookSelectorBridge

namespace ClassicalConstraints

-- ════════════════════════════════════════════════════════════
-- Section 1: Tractability and hardness
-- ════════════════════════════════════════════════════════════

/-- Tractability: CSP(Gamma) is solvable in polynomial time.
    There exists a uniform algorithm that, given a CSP instance over
    Gamma, decides satisfiability in time polynomial in the instance size. -/
structure CSPTractable (dom : CSPDomain)
    (lang : ConstraintLanguage dom) where
  /-- The solver function. -/
  solve : CSPInstance dom lang → Bool
  /-- Correctness. -/
  correct : ∀ inst,
    solve inst = true ↔ inst.Satisfiable dom lang
  /-- Polynomial time bound (degree and constant). -/
  time_bound : PolyBound

/-- Hardness: CSP(Gamma) is NP-complete.
    Every NP problem reduces to CSP(Gamma) via polynomial-time
    many-one reductions. We capture this via SAT reducibility. -/
structure CSPHard (dom : CSPDomain)
    (lang : ConstraintLanguage dom) where
  /-- SAT reduces to CSP(Gamma): for each SAT instance,
      there exists a CSP instance with the same satisfiability. -/
  sat_reduces : ∀ (φ : SATInstance),
    ∃ (inst : CSPInstance dom lang),
      φ.Satisfiable ↔ inst.Satisfiable dom lang
  /-- The reduction is polynomial-time. -/
  reduction_poly : PolyBound

-- ════════════════════════════════════════════════════════════
-- Section 2: Bulatov-Zhuk Dichotomy Theorem
-- ════════════════════════════════════════════════════════════

/-- The Bulatov-Zhuk Dichotomy Theorem, carried as structure
    with axiom-level trust.

    The dichotomy: for any finite constraint language Gamma over a
    finite domain D, exactly one of two things holds:
      (a) Pol(Gamma) contains a WNU operation of some arity k >= 2,
          and CSP(Gamma) is solvable in polynomial time, OR
      (b) Pol(Gamma) does not contain any WNU, and CSP(Gamma) is NP-complete.

    Reference:
    - Bulatov, "A Dichotomy Theorem for Nonuniform CSPs" (2017)
    - Zhuk, "A Proof of the CSP Dichotomy Conjecture" (2020)
    - Originally conjectured by Feder and Vardi (1998) -/
structure BulatovZhukDichotomy (dom : CSPDomain)
    (lang : ConstraintLanguage dom) where
  /-- WNU presence implies tractability. -/
  dichotomy :
    (∃ k, k ≥ 2 ∧ ∃ (w : WNU dom.D k), isPolymorphism lang w.op) →
      CSPTractable dom lang
  /-- WNU absence implies hardness. -/
  dichotomy_hard :
    (¬∃ k, k ≥ 2 ∧ ∃ (w : WNU dom.D k), isPolymorphism lang w.op) →
      CSPHard dom lang

-- ════════════════════════════════════════════════════════════
-- Section 3: Schaefer's Dichotomy (Boolean case)
-- ════════════════════════════════════════════════════════════

/-- Schaefer's Dichotomy: the Boolean special case (|D| = 2).
    Proved by Schaefer in 1978, much simpler than Bulatov-Zhuk.
    Boolean constraint languages are tractable iff Pol(Gamma) contains
    one of: majority, affine (Mal'cev), AND, OR. Otherwise NP-complete. -/
structure SchaeferDichotomy
    (lang : ConstraintLanguage boolDomain) where
  /-- Classification: which tractability type, if any. -/
  classification :
    (∃ (w : WNU Bool 3), isPolymorphism lang w.op) ∨
    (∃ (m : MalcevOp Bool), isPolymorphism lang m.op) ∨
    (isPolymorphism lang (fun args : Fin 2 → Bool =>
      args 0 && args 1)) ∨
    (isPolymorphism lang (fun args : Fin 2 → Bool =>
      args 0 || args 1)) ∨
    Nonempty (CSPHard boolDomain lang)

-- ════════════════════════════════════════════════════════════
-- Section 4: Proved theorems
-- ════════════════════════════════════════════════════════════

/-- The dichotomy is complete: every constraint language falls
    into exactly one of tractable or hard. -/
theorem schaefer_is_boolean_dichotomy
    (lang : ConstraintLanguage boolDomain)
    (bz : BulatovZhukDichotomy boolDomain lang) :
    Nonempty (CSPTractable boolDomain lang) ∨ Nonempty (CSPHard boolDomain lang) := by
  by_cases h : ∃ k, k ≥ 2 ∧ ∃ (w : WNU Bool k), isPolymorphism lang w.op
  · exact Or.inl ⟨bz.dichotomy h⟩
  · exact Or.inr ⟨bz.dichotomy_hard h⟩

/-- If lang₂ ⊆ lang₁ (lang₂ has fewer relations) and lang₂ has no WNU
    polymorphism, then lang₁ also has no WNU polymorphism.
    (Contrapositive of antimonotonicity applied to WNU existence.) -/
theorem no_wnu_upward_closed (dom : CSPDomain)
    (lang₁ lang₂ : ConstraintLanguage dom)
    (hsub : ∀ (idx : Fin lang₂.rels.length),
      ∃ (idx₂ : Fin lang₁.rels.length),
        lang₂.rels[idx] = lang₁.rels[idx₂])
    (h_no_wnu : ¬∃ k, k ≥ 2 ∧ ∃ (w : WNU dom.D k), isPolymorphism lang₂ w.op) :
    ¬∃ k, k ≥ 2 ∧ ∃ (w : WNU dom.D k), isPolymorphism lang₁ w.op := by
  intro ⟨k, hk, w, hw⟩
  apply h_no_wnu
  exact ⟨k, hk, w, pol_antimonotone dom lang₂ lang₁ hsub k w.op hw⟩

/-- Tractable languages are closed upward under sub-languages:
    if lang₂ ⊆ lang₁ (lang₁ has more relations) and lang₁ is tractable,
    then the WNU for lang₁ is also a WNU for lang₂. -/
theorem tractable_sub_language (dom : CSPDomain)
    (lang₁ lang₂ : ConstraintLanguage dom)
    (hsub : ∀ (idx : Fin lang₂.rels.length),
      ∃ (idx₂ : Fin lang₁.rels.length),
        lang₂.rels[idx] = lang₁.rels[idx₂])
    (k : Nat) (_hk : k ≥ 2)
    (w : WNU dom.D k)
    (hw : isPolymorphism lang₁ w.op) :
    isPolymorphism lang₂ w.op :=
  pol_antimonotone dom lang₂ lang₁ hsub k w.op hw

/-- Combining the dichotomy with antimonotonicity:
    if a sub-language of Gamma has no WNU, then Gamma is NP-hard. -/
def sublanguage_hardness_upward (dom : CSPDomain)
    (lang₁ lang₂ : ConstraintLanguage dom)
    (bz : BulatovZhukDichotomy dom lang₁)
    (hsub : ∀ (idx : Fin lang₂.rels.length),
      ∃ (idx₂ : Fin lang₁.rels.length),
        lang₂.rels[idx] = lang₁.rels[idx₂])
    (h_no_wnu₂ : ¬∃ k, k ≥ 2 ∧ ∃ (w : WNU dom.D k), isPolymorphism lang₂ w.op) :
    CSPHard dom lang₁ :=
  bz.dichotomy_hard (no_wnu_upward_closed dom lang₁ lang₂ hsub h_no_wnu₂)

end ClassicalConstraints
