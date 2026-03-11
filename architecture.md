# Architecture Notes for DashI Closure Path

## Canonical Spine (Authoritative)
The canonical closure dependency spine is:

1. `DASHI.Geometry.ProjectionDefect`
2. `DASHI.Energy.EnergySplitProof` (or `DASHI.Geometry.EnergySplitProof`)
3. `DASHI.Geometry.Parallelogram`
4. `DASHI.Geometry.QuadraticForm` via polarization from parallelogram law
5. `DASHI.Geometry.ConeTimeIsotropy`
6. `DASHI.Geometry.Signature31FromConeArrowIsotropy`
7. `DASHI.Geometry.Signature31Lock`

This is the only required theorem route for quadratic and signature emergence.

## Route Classification Policy
- `canonical`: required for Stage C theorem closure claims.
- `alternative`: mathematically valid alternate derivation; not required.
- `validation`: independent cross-check used to reduce proof-risk.
- `experimental`: speculative or partial scaffolding not used for closure claims.

Modules currently in the quadratic family
(`QuadraticFromNorm`, `QuadraticFromProjection`, `QuadraticFromParallelogram`,
`QuadraticEmergence`, `QuadraticFormEmergence`) should be classified under this
policy and consumed accordingly.

## Remaining Architecture Work
1. Keep `ProjectionDefectToParallelogram` and
   `ContractionForcesQuadraticStrong` as the active canonical bottleneck bridge
   surfaces.
2. Replace any raw seam placeholders with named seam packages on canonical
   modules only.
3. Thread signature/Clifford/gauge recovery from canonical spine exports
   instead of parallel emergence routes.
4. Keep signature and Clifford routes logically separate:
   - signature route:
     `ContractionForcesQuadraticStrong -> ContractionQuadraticToSignatureBridgeTheorem`
   - Clifford route:
     `ContractionForcesQuadraticStrong -> QuadraticToCliffordBridgeTheorem`
     (canonical bilinear from normalized quadratic, then Clifford presentation).

## WaveLift⇒Even Architecture Rule (2026-03-11)
1. `Quadratic⇒Clifford` is the sole upstream producer for
   `WaveLift⇒Even` on the canonical path.
2. `WaveLift⇒Even` is a factorization theorem, not a predicate-only claim:
   `State → Cl` must factor through `EvenSubalgebra.incl`.
3. Add explicit Clifford grading interface (`parity`, closure on multiplication,
   unit-even witness) at the canonical Clifford bridge layer.
4. Define canonical wave lift using even Clifford words so image-evenness is by
   construction.
5. Keep this independent from full Dirac operator semantics at this stage.

## Performance Intent
Reducing parallel dependency paths lowers normalization and transport overhead.
Expected effect: lower compile pressure without changing theorem content.
