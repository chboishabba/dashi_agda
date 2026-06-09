# Clay Navier-Stokes Proof Roadmap

Status: lemma roadmap; non-promoting.

This document is a dependency graph for what a DASHI-based proof of the
three-dimensional incompressible Navier-Stokes global regularity problem would
have to prove. It is not a proof, and it does not promote any Clay,
smooth-solution, or terminal claim.

Latest NS-to-EV5 boundary: DASHI may support a conditional NS regularity
theorem only if NS modes project into FRACTRAN-admissible EV5 with forward
simulation. This boundary is fail-closed. The exact open obligations are
forward simulation, quotient correctness, conditional lane7/lane2 preservation
witnesses, ultrametric preservation, and the hard theta < 1 maximum-principle
preservation gap. Until those are discharged, no unconditional Clay
Navier-Stokes claim, arbitrary-data theorem, or global smoothness promotion is
available.

Paper 1 target sidecar: `Docs/NSPaper1ClayTarget.md` now records the
Manager-B Clay-facing chain: fixed-`K` LP identity, theta as `Flux/Diss`,
conditional fixed-`K` tail decay under `theta < 1`, danger-shell locator,
EV5 projection up to an LP commutator defect, and the open danger-shell
maximum-principle/edge-leakage obligations. It is a target document, not a
regularity proof.

## 2026-06-02 Theta Comparison Correction

The current comparison correction is checked in:

```text
DASHI/Physics/Closure/NSThetaPressureMarginCorrectionReceipt.agda
```

The retracted wording is:

```text
H^{11/8} is weaker than H^{1/2}.
```

As a spatial Sobolev exponent this is false: `11/8 > 1/2`, so `H^{11/8}` is
spatially stronger.  The safe claim is instead:

```text
theta < 1 gives conditional, tail-localized L2 pressure-margin decay above K*.
```

That is not the same as global Serrin/BKM control.  The paraproduct split now
has the honest status:

- low-high is controlled by low-frequency gradient/Bernstein structure;
- high-high requires an `L3`/`H^{1/2}` route under standard tools;
- importing that route as an assumption is regularity input and is circular
  for Clay;
- the non-circular high-high estimate remains the wall.

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

## NS-Only Margin Roadmap

This section records the current NS-only use of the margin invariant. Other
lanes are out of scope here. The roadmap is obligation tracking only; it does
not prove global smoothness or the Clay Navier-Stokes statement.

| Stage | NS-only obligation | Status |
|---|---|---|
| L0 | Consume the shared margin grammar only as an NS tail-flux margin interface. | Available as bookkeeping. It does not by itself prove any NS estimate. |
| NS1 | Prove the fixed-`K` tail flux identity for the selected shell split. | Receipt surface recorded in `NSTailFluxAbsorptionMarginReceipt`: `K` is fixed during differentiation and moving cutoffs are excluded. `NSTailFluxIdentityAnalyticTargetReceipt` now names the exact Littlewood-Paley proof obligations; the analytic identity proof remains open. |
| NS2 | Make the theta profile computable across the relevant shells and times. | Implemented as an evidence-only finite cutoff/time diagnostic in dashiCFD. Computability of the profile is not monotonicity and is not regularity. |
| NS3 | Prove that a positive NS margin implies tail decay in the actual-flow variables. | Open. This is the first analytic consumption point for the margin. |
| NS4 | Bind a one-way BKM/Serrin continuation implication from the proved tail decay hypotheses. | Open and one-way only: continuation may follow from the right hypotheses, but the margin is not equivalent to BKM/Serrin control. |
| NS5 | Preserve theta under the NS evolution and projection interfaces. | Hard open problem. This is where phase, pressure, quotient, and forward-simulation losses must be controlled. |
| NS6 | Upgrade preserved theta and continuation to unconditional Clay-level Navier-Stokes regularity. | Uninhabited. Requires all earlier stages plus the external authority boundaries. |

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

## 2026-06-05 Fastest Honest Clay-NS Path

`DASHI/Physics/Closure/NSFastestClayPathReceipt.agda` records the current
route-selection decision after Sprints 56-58 and the negative-Sobolev
danger-shell receipts:

```text
retire packet-normalized action as a proof source
-> decide the H^{-1/2} high-high defect gate
-> if the gate passes, prove non-circular K* absorption and theta preservation
-> feed only a proved tail bound to BKM/Serrin
```

If the `H^{-1/2}` gate fails analytically, the correct next product is an
obstruction theorem plus a pivot, not Clay promotion. The exact next
mathematical decision is therefore to prove or analytically refute

```text
|| P_{>K*}(u . grad u) ||_{H^{-1/2}}
  <= epsilon * nu * || P_{>K*} u ||_{H^{3/2}}
```

without `H^{1/2}`, Serrin, BKM, or stronger regularity as inputs. Packet-local
normalized action remains useful as diagnostic anatomy only; Sprint 58
prevents it from being consumed as a vessel-additive proof source.

`DASHI/Physics/Closure/NSHminusHalfGateDecisionPivotReceipt.agda` records the
current gate decision: the repo has obstruction/divergence evidence and no
uniform absorption proof, so Path A is an obstruction-theorem output rather than
the Clay route.  The active Clay-facing Path B is now:

```text
H^{11/8} Bernoulli-band rigour
-> uniform regularity across dense prime-LP approximations
-> limit uniqueness/stability
-> NS-to-EV5 forward simulation and preservation
-> continuation only after those gates
```

The density gap is recorded as closed at receipt scope, but uniform regularity
across the approximating sequence remains open.  The `H^{11/8}` bound is still
candidate/pending Bernoulli rigour, and no arbitrary-data, smoothness, or Clay
promotion follows.

## Non-Circular K-Star Drift Obstruction

The next checked receipt is
`DASHI/Physics/Closure/NSNonCircularObstructionReceipt.agda`.
It records the current sharp obstruction:

```text
High-high paraproduct control at K*(t)
  through an H^{-1/2} nonlinear-defect estimate
  without assuming H^{1/2} velocity regularity, Serrin, BKM,
  or stronger regularity
```

The forbidden circular route is:

```text
Flux_{>K*} <= (1-c) Diss_{>K*}
  -> H^{1/2}-type velocity control
  -> Serrin/BKM-class regularity
  -> regularity assumption smuggled into the proof
```

The admissible replacement route is:

```text
||P_{>K*}(u.grad u)||_{H^{-1/2}}
  <= epsilon * nu * ||P_{>K*}u||_{H^{3/2}}
  -> dual pairing with P_{>K*}u in H^{1/2}
  -> high-high flux absorbed by tail dissipation
```

The admissible publication claim is weaker and cleaner:

```text
Theta < 1 is a computable seam criterion and danger-shell locator.
Preserving Theta < 1 is equivalent to controlling the high-high obstruction.
The non-circular high-high estimate is the Clay-level NS step.
```

This receipt therefore treats `NonCircularKStarDriftBound` as the open
structural obstruction, not as a partially proved lemma.
`DASHI/Physics/Closure/NSNonCircularKStarDriftBoundTargetReceipt.agda` records
the exact next theorem target after that obstruction receipt: at the danger
shell `K*(t)`, prove `Flux_{>K*(t)} <= (1-c) Diss_{>K*(t)}` or the equivalent
strict theta-preservation statement, while explicitly forbidding `H^{1/2}`,
velocity regularity, Serrin, BKM, or stronger regularity as proof inputs.
`DASHI/Physics/Closure/NSNegativeSobolevDangerShellReceipt.agda` now records
the sharpened H^{-1/2} nonlinear-defect theorem target.  The receipt keeps that
defect estimate, `K*(t)<=K*(nu)` drift containment, edge influx, theta
preservation, and tail-to-continuation bridge as open obligations.

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
- conditional NS regularity without an NS-to-EV5 projection into
  FRACTRAN-admissible EV5 with forward simulation
- treating EV5 lane dictionaries, dashiCFD diagnostics, or FRACTRAN
  admissibility alone as forward simulation
- treating the NS-to-EV5 frontier as closed before quotient correctness,
  conditional lane7/lane2 preservation witnesses, theta < 1
  maximum-principle preservation, and ultrametric preservation are proved
- smooth or unique Leray solution from the carrier
- BKM/enstrophy closure
- treating weak Navier-Stokes as Clay Navier-Stokes
- terminal/unification promotion
