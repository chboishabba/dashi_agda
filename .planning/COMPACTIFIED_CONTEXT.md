# Compactified Context

- Physics bridge stubs were added under `DASHI/Physics/` to mirror the remaining “unproven” list with minimal records/postulates.
- A new `AdmissibleQuadratic` interface now bundles contraction, isotropy, involution, and finite-speed invariances; uniqueness is the intended bottleneck.
- Shared symmetry definitions (`Isotropy`, `PreservesQuadratic`) live in `DASHI/Physics/Core.agda`.
- Current milestone: remove remaining postulates in `DASHI/Physics/*` by providing concrete witnesses and wiring to existing bridge modules.
- Added concrete geometry helpers for isotropy and finite-speed with trivial instances for wiring: `DASHI/Geometry/Isotropy.agda`, `DASHI/Geometry/FiniteSpeed.agda`.
- Extended `Contraction.agda` with `StrictContraction` (contractive + unique fixed point).
- Repo fully typechecks against stdlib; ternary carrier + agreement ultrametric are concrete and postulate-free.
- Real operator stack now uses tail-zeroing projection `Pᵣ` and fine-agreement ultrametric; nontrivial isotropy (C₂ sign-flip) and finite-speed (ball locality) are wired.
- Strict contraction and fixed-point claims are now framed via **fiber/quotient contraction**: added `FiberContraction` and `RealClosureKitFiber`, and `TernaryRealInstance` provides observable fixed/unique on tail digit.
- Remaining global StrictContraction path is still available but not used for the real ternary instance; physics closure now uses the fiber kit.
- Next milestone focuses on canonicalization on the coarse core and a quadratic invariant; signature/orthogonality are introduced as named assumption targets.
2026-02-23:
- Removed nonexpCᵣ and nonexpR postulates. Added constructive proofs in:
  - `DASHI/Metric/FineAgreementUltrametric.agda`
  - `DASHI/Physics/CanonicalizationMinimal.agda`
  - `DASHI/Physics/RealOperatorStackShift.agda`
- Added supporting lemmas: agreement-depth monotonicity under map/append/shiftTail, dNatFine-++ and shiftTail ≤.
- `DASHI_Tests.agda` typechecks (warnings only).
Open: clean up pattern-shadow warnings in FineAgreementUltrametric if desired.
Added:
- `DASHI/Physics/QuadraticPolarization.agda` (ℤ embedding + B₂ℤ polarization seam).
- `DASHI/Physics/DimensionBoundAssumptions.agda` (orbit-profile dimension bound seam).
- `DASHI/Physics/SignatureAssumptions.agda` no longer exports Force-1+3.
2026-02-23:
- Level‑1/2/3 closure obligations progress:
  - Added `DASHI/Physics/MaskedQuadraticRenormalization.agda` with constructive Qσ‑R (masked quadratic under Rᵣ).
  - Added `DASHI/Physics/MaskedConeStructure.agda` (Timelike/Spacelike/Null, cone monotonicity seam, unique time direction seam).
  - Added `DASHI/Physics/OrbitFingerprintAssumptions.agda` (orbit fingerprint predicate, minimality/saturation seams).
  - `DASHI/Physics/ClosureOnAssumption.agda` now re-exports these modules.
- Agda checks pass for new modules; only remaining warnings are pattern-shadow in FineAgreementUltrametric.
