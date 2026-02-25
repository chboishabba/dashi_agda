# Postulate Sweep (2026-02-24)

Scope: closure-critical for the shift instance (TernaryRealInstanceShift + RealClosureKitFiber + mask kit).

## Findings (Physics)

Postulates remaining in `DASHI/Physics/*`:
- `DASHI/Physics/OrbitFingerprintAssumptions.agda`
  - `MinimalOrbit`, `StableSignature`, `Saturation` (dimension/signature seams only).
- `DASHI/Physics/DimensionBoundAssumptions.agda`
  - `isotropyShellProfile`, `OrbitProfile-24-6-2→m≡4`, `OrbitProfile-24-6-2→m≤4`, `m≡4→sig≡1+3-up-to-swap`.
- `DASHI/Physics/MaskedConeStructure.agda`
  - `coneMonotone` and `twoTimeLike→noUniqueFP` (generic cone/uniqueness seams).
- `DASHI/Physics/QuadraticPolarization.agda`
  - `B₂ℤ-Q̂core-dot2` (polarization seam for ℤ quadratic).
- `DASHI/Physics/SpinAssumptions.agda`, `DASHI/Physics/BianchiEinsteinAssumptions.agda`
  - High-level physics gates (not used in shift closure).

## Closure-critical status

For the shift instance path:
- No postulates are currently on the *operator closure spine* (R/P/C, nonexpansive, strict contraction, fiber closure).
- The remaining postulates are in higher-level “physics gates” and signature/uniqueness seams.

## Next removals (optional)

1. Replace `QuadraticPolarization.B₂ℤ-Q̂core-dot2` with the constructive proof if you want a fully earned bilinear form.
2. Replace `MaskedConeStructure.coneMonotone` with the concrete `RealCausalStructureNontrivial.coneMonotone-mask` in downstream uses (already done in shift instance).
3. If you want a theorem-level dimension bound, the `OrbitFingerprintAssumptions` and `DimensionBoundAssumptions` postulates are the next targets.
