# Canonical Proof Spine

This is the single canonical physics-path proof spine to cite in docs and imports.

Diagram surfaces:

- `Docs/CanonicalProofSpine.puml`
- `Docs/CanonicalProofSpine.svg`
- `Docs/RepoMetasystem.puml`
- `Docs/PhysicsUnificationMap.puml`

## Naming Standard

- `canonical`: authoritative export surface for current repo claims
- `strong`: strengthened theorem surface that carries explicit seam witnesses
- `minimal credible`: current closure milestone package
- `known limits`: downstream GR/QFT recovery bridge layer

## Canonical Spine (Real Stack -> Full Closure)

1. Real stack source:
   `DASHI/Physics/ConcreteClosureStack.agda`
2. Strong contraction->quadratic:
   `DASHI/Physics/Closure/ContractionForcesQuadraticStrong.agda`
3. Canonical contraction->signature:
   `DASHI/Physics/Closure/ContractionQuadraticToSignatureBridgeTheorem.agda`
4. Canonical quadratic->Clifford:
   `DASHI/Physics/Closure/QuadraticToCliffordBridgeTheorem.agda`
5. Canonical contraction->Clifford bundle:
   `DASHI/Physics/Closure/CanonicalContractionToCliffordBridgeTheorem.agda`
6. Canonical full closure instance:
   `DASHI/Physics/Closure/PhysicsClosureFullInstance.agda`
7. Canonical minimal-credible closure:
   `DASHI/Physics/Closure/MinimalCrediblePhysicsClosureShiftInstance.agda`
8. Known-limits GR bridge:
   `DASHI/Physics/Closure/KnownLimitsGRBridgeTheorem.agda`
9. Known-limits QFT bridge:
   `DASHI/Physics/Closure/KnownLimitsQFTBridgeTheorem.agda`

## Duplicate Surface Policy

- Canonical consumers should import the spine above.
- Compatibility wrappers (for example combined bridge bundles that duplicate
  intermediate fields) are allowed, but should be treated as non-authoritative
  forwarding surfaces.
- New theorem surfaces must state:
  assumptions, output, and classification (`abstract`, `concrete`, `canonical`)
  in a standardized header block.
