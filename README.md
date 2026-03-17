[![Lean Action CI](https://github.com/LarsenClose/classical-constraints/actions/workflows/ci.yml/badge.svg)](https://github.com/LarsenClose/classical-constraints/actions/workflows/ci.yml)
[![Documentation](https://img.shields.io/badge/docs-GitHub%20Pages-blue)](https://larsenclose.github.io/classical-constraints/)

# classical-constraints

Seven chains from seven mathematical domains (SAT, proof complexity, descriptive complexity, CSP/polymorphisms, algebraic proof systems, extension complexity, distributed protocols), each formalized through domain-specific structures to a shared lock theorem architecture. All seven chains have both lock theorems and direct bridge theorems. 84 Lean files, zero sorry.

## Build

```
lake build
```

Requires Lean 4.28.0 and Mathlib.

## Repository graph

```
witness-transport  (core definitions, carrier architecture, transport, invariance)
      |
pnp-integrated     (separation theorem, transport obstruction, anti-compression)
      |
classical-constraints  <-- you are here
      |
classical-bridge   (classical TM model, regime classification, not_P_eq_NP)
```

This repo mirrors `GradedReflModel` as `GradedReflModel_Mirror` (with `_Mirror` suffix on related types) from upstream repos. The repos cannot share imports; mirroring is for build isolation.

## Custom axioms

Exactly two custom axioms in this repo:

1. `sideA_bounded_selector_impossible` (Shared/SideAMirror.lean) -- mirror of a proved theorem. Proved as `selfApp_not_grade_bounded` in pnp-integrated and proved independently in classical-bridge. Mirrored here for import isolation. Used by six of seven lock theorems.

2. `resolution_feasible_interpolation` (Chain2_ProofComplexity/FeasibleInterpolationBridge.lean) -- external result (Krajicek 1997). Encodes feasible interpolation for resolution refutations. Used by Chain 2 only. Chain 2's lock theorem does NOT use sideA.

## Theorem inventory

See `CLAIMS.md` for the complete theorem inventory with machine-verified axiom profiles.
