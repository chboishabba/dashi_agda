# Clay Navier-Stokes Proof Roadmap

Status: lemma roadmap; non-promoting.

This document is a dependency graph for what a DASHI-based proof of the
three-dimensional incompressible Navier-Stokes global regularity problem would
have to prove. It is not a proof, and it does not promote any Clay,
smooth-solution, or terminal claim.

The current tower contains receipts for finite energy/BKM targets, ultrametric
Aubin-Lions compactness, a failed 2/3/5 Haar-frame bridge, a carrier weak-form
interface, and a replacement Littlewood-Paley/Besov/parabolic-smoothing target.
Those receipts name blockers. The roadmap below decomposes the blocker into
lemmas.

## Dependency Graph

```text
N1 Leray energy inequality
  -> N2 local smooth solution authority
  -> N3 enstrophy/vorticity evolution control
  -> N4 BKM continuation criterion
  -> N5 L-infinity vorticity control from carrier estimates
  -> N6 global smooth continuation

N1 + frame/Archimedean bridge
  -> W1 coefficient compactness
  -> W2 L2(R3) compactness
  -> W3 nonlinear term passage
  -> W4 Leray weak solution

W4 is not N6. The weak-solution branch is complete only as a non-promoting
carrier/conditional branch audit; weak Navier-Stokes is not Clay
Navier-Stokes. The Clay regularity branch remains open on N3-N5 and the
continuum analytic lift.
```

## Lemma Status

| Lemma | Required mathematical content | Current carrier status | Existing receipt surface | Gap |
|---|---|---|---|---|
| N1 | Prove the global Leray energy inequality in the Archimedean `R3` setting. | Partial/conditional. Finite and ultrametric energy controls exist, but the Archimedean bridge is not proved. | `NavierStokesWeakSolutionInterface`, `UltrametricSobolevUniformBound`, `NSCarrierContinuumLimitReceipt` | Need transfer from carrier/ultrametric coefficients to standard `L2(R3)` energy. |
| N2 | Bind standard local smooth existence for smooth divergence-free initial data. | External authority target only. The carrier does not need to reprove Kato-style local existence, but it must bind the hypotheses. | `NavierStokesRegularityTowerReceipt`, `ClayMillenniumClosureTargetReceipt` | Need explicit authority boundary and matching initial-data class. |
| N3 | Control enstrophy/vorticity growth for all time. | Uninhabited. Finite vorticity/BKM rungs exist as targets, not a continuum estimate. | `CarrierBKMControlTargetReceipt`, `EllipticBootstrapReceipt` | Need a global estimate for `||omega(t)||_2` or stronger norms that survives nonlinear stretching. |
| N4 | Apply the Beale-Kato-Majda continuation criterion. | Named blocker only. | `CarrierNSSmoothConvergenceReceipt`, `ClayBlockerUpdateReceipt` | Need `int_0^T ||omega||_infty dt < infinity` for every finite `T`. |
| N5 | Bound `||omega||_infty` from carrier-controlled quantities. | Uninhabited. This is the main blowup barrier. | `UltrametricSobolevUniformBound`, `WaveletFrameBoundRevisionReceipt` | Need Archimedean Sobolev/Biot-Savart control at `s > 3/2`; current frame bounds are open. |
| N6 | Continue the local smooth solution globally. | Uninhabited. Requires N3-N5. | `NavierStokesRegularityTowerReceipt` | No global smooth regularity theorem is present. |
| W1 | Prove coefficientwise compactness in the carrier/wavelet representation. | Complete for the roadmap audit branch, not a Clay result. Aubin-Lions remains a receipt-level carrier/conditional route. | `UltrametricAubinLionsReceipt`, `AubinLionsBound3Full`, `UltrametricAubinLionsCompactness` | Does not supply continuum smoothness or BKM closure. |
| W2 | Decide whether the 2/3/5 wavelet/frame bridge gives compactness in `L2(R3)`. | Complete as a negative decision for the pure Haar-frame route. The unrestricted system fails on constants, and the zero-mean/off-diagonal route has divergent Hilbert-Schmidt control. | `NSWaveletRouteClosedReceipt`, `HilbertSchmidtBoundGramReceipt`, `NSFrameRestrictionReceipt` | Replacement analytic bridge is required; no frame lower bound or Clay regularity follows. |
| W3 | Pass the nonlinear term `(u . grad)u` to the limit. | Complete only as a fail-closed weak-branch ledger: the route is named and bounded by missing Archimedean/nonlinear hypotheses. | `NSCarrierContinuumLimitReceipt`, `NSWeakSolutionFinalReceipt`, `NSWaveletRouteClosedReceipt` | No unconditional continuum Leray theorem, no smoothness, and no BKM closure. |
| W4 | Construct or audit a Leray weak-solution branch from the carrier limit. | Complete as a non-promoting weak branch. | `NavierStokesWeakSolutionInterface`, `NSWeakSolutionFinalReceipt`, `ClayNSProofRoadmapReceipt` | Weak NS is not Clay NS; it does not imply global regularity and cannot promote N6. |

## Current Honest Position

Update after the second roadmap-execution tranche: the weak branch is complete
only in the fail-closed sense that its carrier interfaces, conditional route,
and negative frame decision are recorded. The unrestricted 2/3/5 Haar system
is not a frame for all of `L2`, because constant functions pair to zero with
pure Haar wavelets. The zero-mean restriction does not rescue the recorded
Gram route, since the off-diagonal Hilbert-Schmidt control diverges. The
pure Haar-frame path is therefore closed as a proof route.

This completion does not prove Clay Navier-Stokes. A Leray or carrier weak
solution is not a smooth global solution. Clay regularity still requires
global vorticity/enstrophy control, the BKM integrability bound, and a
continuum analytic mechanism that controls `||omega||_infty`.

The regularity branch remains open. The admissible next NS tranche is the
replacement analytic route: prime-band Littlewood-Paley/Besov/parabolic
smoothing estimates, especially a paraproduct estimate strong enough to feed
N5. It must not be described as a Clay NS proof until N3-N6 and the external
authority boundaries are discharged.

Phase 2 update: the pure 2/3/5 Haar-frame route is now recorded as closed
negatively by `NSWaveletRouteClosedReceipt`: constants obstruct the
unrestricted system and the zero-mean Gram/Hilbert-Schmidt route does not
produce the needed lower frame bound.  `NSAlternativeApproachSurveyReceipt`
and `NSLittlewoodPaleyCarrierReceipt` replace that route with a prime-band
Littlewood-Paley/Besov/paraproduct programme over the `p2`, `p3`, and `p5`
bands.

The prime-LP weak branch is now recorded through
`PrimeBandLPDefinitionReceipt`, `BernsteinInequalityPrimeBandReceipt`,
`ParaproductDecompositionReceipt`, `NSCarrierEnergyInequalityReceipt`,
`NSCarrierLerayCompactnessReceipt`, `NSW3NonlinearPassageReceipt`,
`NSW4WeakSolutionReceipt`, and `NSWeakSolutionSummaryReceipt`.  It inhabits
the Leray weak-solution branch at receipt scope.  `Phase2ProgrammeReceipt`
keeps the programme boundary explicit: weak existence is not uniqueness,
smooth continuation, BKM closure, Clay NS, or terminal promotion.

## Promotion Boundary

The following must remain false until the corresponding lemmas and authority
boundaries are discharged:

- Clay Navier-Stokes promotion
- unconditional smooth continuum limit
- global regularity
- smooth or unique Leray solution from the carrier
- BKM/enstrophy closure
- treating weak Navier-Stokes as Clay Navier-Stokes
- terminal/unification promotion
