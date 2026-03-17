/-
  ClassicalConstraints/SideAMirror.lean
  Canonical mirror of Side A (pnp-integrated) types used across all lock files.

  These are copies of definitions from pnp-integrated/PNP/Core.lean and
  pnp-integrated/PNP/Categorical/SelectionObstructionCore.lean. They are
  duplicated here so that classical-constraints files can be compiled without
  importing the constructive repo.

  All lock files should import this file and use these definitions rather than
  defining their own local copies.

  STATUS: 0 sorry, 0 Classical.choice.
-/

import ClassicalConstraints.Shared.CookSelectorBridge

namespace ClassicalConstraints

-- ============================================================
-- Mirror types from Side A
-- ============================================================

/-- Mirror of GradedReflModel from pnp-integrated/PNP/Core.lean.
    A graded reflexive model: a type with fold/unfold (the Lambek
    isomorphism of D ≅ D → D), and a grade function. -/
structure GradedReflModel_Mirror where
  /-- The carrier type (fixed-point object D). -/
  carrier : Type
  /-- fold : D → D (one half of Lambek iso, simplified to endomorphism). -/
  fold : carrier → carrier
  /-- unfold : D → D (other half of Lambek iso, simplified). -/
  unfold : carrier → carrier
  /-- Round-trip: fold ∘ unfold = id. -/
  roundtrip : ∀ x, fold (unfold x) = x
  /-- Grade function on carrier elements. -/
  grade : carrier → Nat

/-- Mirror of GradedReflModel.selfApp. selfApp x = unfold(fold(x)).
    The self-application map, computational core of the Y combinator. -/
def GradedReflModel_Mirror.selfApp (M : GradedReflModel_Mirror) (x : M.carrier) : M.carrier :=
  M.unfold (M.fold x)

/-- Mirror of SelfAppUnbounded from pnp-integrated/PNP/Core.lean.
    selfApp is unbounded in grade: for every target grade d, there exists
    an element x with grade x ≤ d but grade(selfApp x) > d. -/
structure SelfAppUnbounded_Mirror (M : GradedReflModel_Mirror) where
  /-- For every grade bound d, some element's selfApp output exceeds it. -/
  overflows : ∀ d, ∃ x, M.grade x ≤ d ∧ M.grade (M.selfApp x) > d

-- ============================================================
-- Side A theorem (proved in pnp-integrated, mirrored as axiom)
-- ============================================================

/-- Mirror of selfApp_not_factors from pnp-integrated/PNP/Core.lean.
    If selfApp is unbounded, no grade-bounded evaluator exists:
    there is no function that agrees with selfApp on grade-bounded
    inputs and has grade-bounded outputs on those inputs.
    (Equivalent to ¬FactorsThrough M selfApp d, since any such f
    would witness factoring via f(x) = selfApp(x) on the bounded domain.) -/
axiom sideA_bounded_selector_impossible (M : GradedReflModel_Mirror)
    (hub : SelfAppUnbounded_Mirror M) (d : Nat) :
    ¬∃ (f : M.carrier → M.carrier),
      (∀ x, M.grade x ≤ d → f x = M.selfApp x) ∧
      (∀ x, M.grade x ≤ d → M.grade (f x) ≤ d)

-- ============================================================
-- Direct contradiction: grade-non-increasing selfApp vs unbounded
-- ============================================================

/-- If selfApp equals some function f that is grade-non-increasing,
    then SelfAppUnbounded is contradicted directly.

    This is the simplest bridge pattern: when a chain's model data shows
    selfApp = red and red is grade-non-increasing, selfApp cannot overflow.
    The proof uses only two of the four ModelData fields (selfApp_eq_red
    and red_grade_le), bypassing Fragment, Cofinality, RelevantSubdomain,
    and partial_bridge entirely.

    Used by: chain5_direct_bridge, chain2_direct_bridge, chain3_direct_bridge. -/
theorem selfApp_nonincreasing_contradiction
    (M : GradedReflModel_Mirror)
    (hub : SelfAppUnbounded_Mirror M)
    (f : M.carrier → M.carrier)
    (h_eq : ∀ x, M.selfApp x = f x)
    (h_le : ∀ x, M.grade (f x) ≤ M.grade x) : False := by
  obtain ⟨x, hxd, hxsa⟩ := hub.overflows 0
  have : M.grade (M.selfApp x) ≤ M.grade x := by rw [h_eq]; exact h_le x
  omega

-- ============================================================
-- Mirror helper definitions
-- ============================================================

/-- FactorsThrough: f factors through grade d means grade(f(x)) ≤ d whenever grade(x) ≤ d. -/
def FactorsThrough_Mirror (M : GradedReflModel_Mirror) (f : M.carrier → M.carrier) (d : Nat) : Prop :=
  ∀ x, M.grade x ≤ d → M.grade (f x) ≤ d

/-- PEqNP: selfApp factors through some grade. -/
def PEqNP_Mirror (M : GradedReflModel_Mirror) : Prop :=
  ∃ d, FactorsThrough_Mirror M M.selfApp d

/-- Realizable: grade(x) ≤ d and grade(fold(x)) ≤ d. -/
def Realizable_Mirror (M : GradedReflModel_Mirror) (x : M.carrier) (d : Nat) : Prop :=
  M.grade x ≤ d ∧ M.grade (M.fold x) ≤ d

-- ============================================================
-- GRM morphism framework (mirrored from Sections 15-16)
-- ============================================================

/-- Mirror of GRMorphism: strict morphism commuting with fold/unfold, grade-preserving. -/
structure GRMorphism_Mirror (M₁ M₂ : GradedReflModel_Mirror) where
  map : M₁.carrier → M₂.carrier
  map_fold : ∀ x, map (M₁.fold x) = M₂.fold (map x)
  map_unfold : ∀ x, map (M₁.unfold x) = M₂.unfold (map x)
  map_grade : ∀ x, M₂.grade (map x) = M₁.grade x

/-- Mirror of GRRetraction: grade non-increasing variant. -/
structure GRRetraction_Mirror (M₁ M₂ : GradedReflModel_Mirror) where
  map : M₁.carrier → M₂.carrier
  map_fold : ∀ x, map (M₁.fold x) = M₂.fold (map x)
  map_unfold : ∀ x, map (M₁.unfold x) = M₂.unfold (map x)
  map_grade_le : ∀ x, M₂.grade (map x) ≤ M₁.grade x

/-- Every strict morphism is a retraction. -/
def GRMorphism_Mirror.toRetraction {M₁ M₂ : GradedReflModel_Mirror}
    (φ : GRMorphism_Mirror M₁ M₂) : GRRetraction_Mirror M₁ M₂ where
  map := φ.map
  map_fold := φ.map_fold
  map_unfold := φ.map_unfold
  map_grade_le := fun x => by have := φ.map_grade x; omega

/-- Morphisms preserve selfApp: φ(selfApp(x)) = selfApp(φ(x)). -/
theorem GRMorphism_Mirror.map_selfApp {M₁ M₂ : GradedReflModel_Mirror}
    (φ : GRMorphism_Mirror M₁ M₂) (x : M₁.carrier) :
    φ.map (M₁.selfApp x) = M₂.selfApp (φ.map x) := by
  simp only [GradedReflModel_Mirror.selfApp]
  rw [φ.map_unfold, φ.map_fold]

/-- Retractions preserve selfApp. -/
theorem GRRetraction_Mirror.map_selfApp {M₁ M₂ : GradedReflModel_Mirror}
    (ψ : GRRetraction_Mirror M₁ M₂) (x : M₁.carrier) :
    ψ.map (M₁.selfApp x) = M₂.selfApp (ψ.map x) := by
  simp only [GradedReflModel_Mirror.selfApp]
  rw [ψ.map_unfold, ψ.map_fold]

/-- Strict morphisms reflect FactorsThrough. -/
theorem GRMorphism_Mirror.reflects_factorsThrough {M₁ M₂ : GradedReflModel_Mirror}
    (φ : GRMorphism_Mirror M₁ M₂) (d : Nat)
    (hf : FactorsThrough_Mirror M₂ M₂.selfApp d) :
    FactorsThrough_Mirror M₁ M₁.selfApp d := by
  intro x hx
  have h1 : M₂.grade (φ.map x) ≤ d := by rw [φ.map_grade]; exact hx
  have h2 := hf _ h1
  rw [← φ.map_selfApp] at h2
  rw [φ.map_grade] at h2
  exact h2

/-- Strict morphisms reflect PEqNP. -/
theorem GRMorphism_Mirror.reflects_PEqNP {M₁ M₂ : GradedReflModel_Mirror}
    (φ : GRMorphism_Mirror M₁ M₂) (h : PEqNP_Mirror M₂) :
    PEqNP_Mirror M₁ := by
  obtain ⟨d, hd⟩ := h
  exact ⟨d, φ.reflects_factorsThrough d hd⟩

/-- Morphism from TC model propagates separation to target. -/
theorem strict_morphism_propagates_separation_mirror {M₁ M₂ : GradedReflModel_Mirror}
    (φ : GRMorphism_Mirror M₁ M₂) (hub : SelfAppUnbounded_Mirror M₁) :
    ¬PEqNP_Mirror M₂ := by
  intro ⟨d, hd⟩
  have hf := φ.reflects_factorsThrough d hd
  obtain ⟨x, hxd, hsa⟩ := hub.overflows d
  have := hf x hxd
  omega

/-- GRM morphisms preserve realizability. -/
theorem GRMorphism_Mirror.preserves_realizable {M₁ M₂ : GradedReflModel_Mirror}
    (φ : GRMorphism_Mirror M₁ M₂) (x : M₁.carrier) (d : Nat)
    (hr : Realizable_Mirror M₁ x d) :
    Realizable_Mirror M₂ (φ.map x) d := by
  obtain ⟨hg, hfg⟩ := hr
  constructor
  · rw [φ.map_grade]; exact hg
  · rw [← φ.map_fold, φ.map_grade]; exact hfg

/-- GR retractions preserve realizability. -/
theorem GRRetraction_Mirror.preserves_realizable {M₁ M₂ : GradedReflModel_Mirror}
    (ψ : GRRetraction_Mirror M₁ M₂) (x : M₁.carrier) (d : Nat)
    (hr : Realizable_Mirror M₁ x d) :
    Realizable_Mirror M₂ (ψ.map x) d := by
  obtain ⟨hg, hfg⟩ := hr
  constructor
  · exact Nat.le_trans (ψ.map_grade_le x) hg
  · rw [← ψ.map_fold]; exact Nat.le_trans (ψ.map_grade_le _) hfg

-- ============================================================
-- Polynomial-grade retraction (used across chains)
-- ============================================================

/-- PolyGRRetraction_Mirror: a GR retraction with polynomial grade distortion.
    Weaker than GRRetraction_Mirror (which requires grade non-increasing).
    Captures chains that preserve fold/unfold structure up to polynomial
    overhead in grade.

    This is the correct target for Chain 5: the algebraic transfer preserves
    polynomial-degree structure, so grade distortion is polynomial, not linear.
    The fold/unfold commutation is the open condition. -/
structure PolyGRRetraction_Mirror (M₁ M₂ : GradedReflModel_Mirror) where
  map : M₁.carrier → M₂.carrier
  map_fold : ∀ x, map (M₁.fold x) = M₂.fold (map x)
  map_unfold : ∀ x, map (M₁.unfold x) = M₂.unfold (map x)
  bound : PolyBound
  map_grade_poly : ∀ x, M₂.grade (map x) ≤ bound.eval (M₁.grade x)

/-- Every GRRetraction is a PolyGRRetraction with the identity polynomial. -/
def GRRetraction_Mirror.toPolyRetraction {M₁ M₂ : GradedReflModel_Mirror}
    (ψ : GRRetraction_Mirror M₁ M₂) : PolyGRRetraction_Mirror M₁ M₂ where
  map := ψ.map
  map_fold := ψ.map_fold
  map_unfold := ψ.map_unfold
  bound := ⟨1, 0⟩
  map_grade_poly := fun x => by
    simp [PolyBound.eval]
    exact ψ.map_grade_le x

/-- PolyGRRetractions preserve selfApp: φ(selfApp(x)) = selfApp(φ(x)).
    The proof is identical to the GRRetraction case — it only needs
    fold/unfold commutation, not grade bounds. -/
theorem PolyGRRetraction_Mirror.map_selfApp {M₁ M₂ : GradedReflModel_Mirror}
    (φ : PolyGRRetraction_Mirror M₁ M₂) (x : M₁.carrier) :
    φ.map (M₁.selfApp x) = M₂.selfApp (φ.map x) := by
  simp only [GradedReflModel_Mirror.selfApp]
  rw [φ.map_unfold, φ.map_fold]

-- ============================================================
-- Lambek data (mirrored from OmegaChainCompletion Section 5)
-- ============================================================

/-- Lambek data: the cotrip condition unfold(fold(x)) = x.
    When a GradedReflModel_Mirror has Lambek data, selfApp = id. -/
structure LambekData_Mirror (M : GradedReflModel_Mirror) where
  cotrip : ∀ x, M.unfold (M.fold x) = x

theorem LambekData_Mirror.selfApp_eq_id {M : GradedReflModel_Mirror}
    (L : LambekData_Mirror M) : ∀ x, M.selfApp x = x :=
  L.cotrip

theorem LambekData_Mirror.PEqNP {M : GradedReflModel_Mirror}
    (L : LambekData_Mirror M) : PEqNP_Mirror M := by
  refine ⟨0, fun x hx => ?_⟩
  rw [L.selfApp_eq_id x]; exact hx

-- ============================================================
-- Partial Lambek data (mirrored from OmegaChainCompletion §6-7)
-- Cross-chain infrastructure used by Chains 5, 2, 3.
-- ============================================================

/-- Partial Lambek data on a subdomain: cotrip holds only for domain elements.
    Mirror of PartialLambekData from OmegaChainCompletion.lean. -/
structure PartialLambekData_Mirror (M : GradedReflModel_Mirror) where
  domain : M.carrier → Prop
  cotrip_on : ∀ x, domain x → M.unfold (M.fold x) = x

/-- A relevant subdomain: partial Lambek + cofinality for separation witnesses.
    Mirror of RelevantSubdomain from OmegaChainCompletion.lean. -/
structure RelevantSubdomain_Mirror (M : GradedReflModel_Mirror) extends PartialLambekData_Mirror M where
  cofinal : ∀ d, (∃ x, M.grade x ≤ d ∧ M.grade (M.selfApp x) > d) →
    (∃ x, domain x ∧ M.grade x ≤ d ∧ M.grade (M.selfApp x) > d)

/-- Partial bridge theorem (mirror): a relevant subdomain contradicts
    SelfAppUnbounded. Proof follows the pnp-integrated version. -/
theorem partial_bridge_mirror (M : GradedReflModel_Mirror)
    (R : RelevantSubdomain_Mirror M) (hub : SelfAppUnbounded_Mirror M) : False := by
  obtain ⟨x, hxd, hxsa⟩ := hub.overflows 0
  obtain ⟨x', hdom, hxd', hxsa'⟩ := R.cofinal 0 ⟨x, hxd, hxsa⟩
  have heq := R.cotrip_on x' hdom
  simp only [GradedReflModel_Mirror.selfApp] at hxsa'
  rw [heq] at hxsa'
  omega

-- ============================================================
-- GRM Endofunctor (mirrored from OmegaChainCompletion Section 1)
-- ============================================================

/-- Mirror of GRMEndofunctor from pnp-integrated/PNP/Transport/OmegaChainCompletion.lean.
    A GRM endofunctor: an operation on GradedReflModels that produces
    a section-retraction pair with meta-collapse (selfApp = id at F(M)).

    The defining properties:
    - F maps GradedReflModel_Mirrors to GradedReflModel_Mirrors
    - F(M) embeds into F(F(M)) as a strict GRM morphism (section)
    - F(F(M)) retracts onto F(M) as a GR retraction (projection)
    - The retraction-section pair satisfies eval ∘ lift = id
    - F(M) always has selfApp = id (meta-collapse / fixed-point property)

    The meta-collapse is the key axiom: it says F is a "completion"
    functor that always reaches the fixed point in one step. -/
structure GRMEndofunctor_Mirror where
  /-- The endofunctor on objects. -/
  F : GradedReflModel_Mirror → GradedReflModel_Mirror
  /-- Section: F(M) ↪ F(F(M)) as a strict GRM morphism. -/
  lift : ∀ M, GRMorphism_Mirror (F M) (F (F M))
  /-- Retraction: F(F(M)) ↞ F(M) as a GR retraction. -/
  eval : ∀ M, GRRetraction_Mirror (F (F M)) (F M)
  /-- Coherence: eval ∘ lift = id. -/
  roundtrip : ∀ M t, (eval M).map ((lift M).map t) = t
  /-- Meta-collapse: F(M) always has selfApp = id.
      This is the D∞ fixed-point property. -/
  collapse : ∀ M (t : (F M).carrier), (F M).selfApp t = t

-- ============================================================
-- Endofunctor theorems (mirrored from OmegaChainCompletion Sections 2-4)
-- ============================================================

/-- F(M) is in the P=NP regime (immediate from meta-collapse).
    Mirror of GRMEndofunctor.F_PEqNP. -/
theorem GRMEndofunctor_Mirror.F_PEqNP (E : GRMEndofunctor_Mirror)
    (M : GradedReflModel_Mirror) : PEqNP_Mirror (E.F M) := by
  refine ⟨0, fun t ht => ?_⟩
  rw [E.collapse M t]
  exact ht

/-- F(F(M)) also has selfApp = id (meta-collapse applied to F(M)).
    Mirror of GRMEndofunctor.FF_collapse. -/
theorem GRMEndofunctor_Mirror.FF_collapse (E : GRMEndofunctor_Mirror)
    (M : GradedReflModel_Mirror) :
    ∀ t : (E.F (E.F M)).carrier, (E.F (E.F M)).selfApp t = t :=
  E.collapse (E.F M)

/-- The regime match between F(M) and F(F(M)) is forced by the
    morphism structure: the lift reflects PEqNP from F(F(M)) to F(M).
    Mirror of GRMEndofunctor.regime_forced. -/
theorem GRMEndofunctor_Mirror.regime_forced (E : GRMEndofunctor_Mirror)
    (M : GradedReflModel_Mirror) : PEqNP_Mirror (E.F M) := by
  have hff : PEqNP_Mirror (E.F (E.F M)) := E.F_PEqNP (E.F M)
  exact (E.lift M).reflects_PEqNP hff

/-- The section-retraction pair is a structural retraction:
    F(M) is a grade-preserving retract of F(F(M)).
    Mirror of GRMEndofunctor.structural_retraction. -/
theorem GRMEndofunctor_Mirror.structural_retraction (E : GRMEndofunctor_Mirror)
    (M : GradedReflModel_Mirror) :
    (∃ φ : GRMorphism_Mirror (E.F M) (E.F (E.F M)),
      ∃ ψ : GRRetraction_Mirror (E.F (E.F M)) (E.F M),
        ∀ t, ψ.map (φ.map t) = t) :=
  ⟨E.lift M, E.eval M, E.roundtrip M⟩

/-- The GRM endofunctor always produces models with Lambek data.
    The meta-collapse axiom IS the cotrip condition.
    Mirror of GRMEndofunctor.lambekData. -/
def GRMEndofunctor_Mirror.lambekData (E : GRMEndofunctor_Mirror)
    (M : GradedReflModel_Mirror) : LambekData_Mirror (E.F M) where
  cotrip := E.collapse M

/-- BRIDGE FACTORY THEOREM (mirror).

    Any GRM endofunctor produces the full bridge infrastructure:
    (1) F(M) is in the collapse regime (selfApp = id, PEqNP)
    (2) F(M) ↪ F(F(M)) via a strict GRM morphism (section)
    (3) F(F(M)) ↠ F(M) via a GR retraction (projection)
    (4) The section and retraction compose to the identity
    (5) F(F(M)) also has selfApp = id

    Mirror of bridge_factory from OmegaChainCompletion.lean. -/
theorem bridge_factory_mirror (E : GRMEndofunctor_Mirror)
    (M : GradedReflModel_Mirror) :
    -- (1) Meta-collapse: selfApp = id
    (∀ t, (E.F M).selfApp t = t) ∧
    -- (2) P=NP at the meta-level
    PEqNP_Mirror (E.F M) ∧
    -- (3) Structural retraction: F(M) ↪ F(F(M)) ↞ F(M)
    (∃ φ : GRMorphism_Mirror (E.F M) (E.F (E.F M)),
      ∃ ψ : GRRetraction_Mirror (E.F (E.F M)) (E.F M),
        ∀ t, ψ.map (φ.map t) = t) ∧
    -- (4) Idempotence: F(F(M)) also has selfApp = id
    (∀ t, (E.F (E.F M)).selfApp t = t) :=
  ⟨E.collapse M,
   E.F_PEqNP M,
   E.structural_retraction M,
   E.FF_collapse M⟩

/-- LAMBEK FACTORY THEOREM (mirror).

    Any GRM endofunctor produces models with Lambek data, selfApp = id,
    PEqNP, and the full bridge infrastructure. The meta-collapse axiom
    IS the Lambek cotrip condition.

    Mirror of lambek_factory from OmegaChainCompletion.lean. -/
theorem lambek_factory_mirror (E : GRMEndofunctor_Mirror)
    (M : GradedReflModel_Mirror) :
    -- Lambek data exists
    (∃ _ : LambekData_Mirror (E.F M), True) ∧
    -- selfApp = id (from Lambek)
    (∀ t, (E.F M).selfApp t = t) ∧
    -- PEqNP (from Lambek)
    PEqNP_Mirror (E.F M) ∧
    -- Full bridge infrastructure
    (∃ φ : GRMorphism_Mirror (E.F M) (E.F (E.F M)),
      ∃ ψ : GRRetraction_Mirror (E.F (E.F M)) (E.F M),
        ∀ t, ψ.map (φ.map t) = t) :=
  ⟨⟨E.lambekData M, trivial⟩,
   E.collapse M,
   E.F_PEqNP M,
   E.structural_retraction M⟩

end ClassicalConstraints
