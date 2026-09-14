# Clay Navier-Stokes Proof Roadmap

Status: lemma roadmap; non-promoting.

## Current control record (2026-09-15)

This is a historical and broad dependency ledger.  For the current active
proof-search objective, the C/D source-integration split, the R568/R571
priority, the independent R406 phase-production leaf, and the exact delivery
discipline, read `Docs/roadmaps/NSProofControl20260915.md` first.  Nothing in
this older roadmap promotes a Clay claim or supersedes that control record.

This document is a dependency graph for what a DASHI-based proof of the
three-dimensional incompressible Navier-Stokes global regularity problem would
have to prove. It is not a proof, and it does not promote any Clay,
smooth-solution, or terminal claim.

## 2026-09-13 current canonical reading

The live Clay-facing manuscript is
`Docs/papers/live/Paper1NavierStokesClayDraft.md`.  Its primary route is now the
modern same-object/direct-companion spine rather than the older A1-A9,
theta/ESS/Abel, Haar-frame, H^-1/2, or EV5 routes.

Current proof-critical chain:

```text
literal periodic Galerkin NS
  -> signed/helical commutator geometry
  -> P3 same-output physical separation
  -> R211 same-output residual payment
  -> literal R406 / C_direct same-object lineage
  -> R568 CommutatorOnlySpacetimeBudget568
  -> R572 direct leaf-A compiler
  -> R503/R415 critical-barrier consumer
```

Exact status:

```text
C_direct constructed                         yes
same-output debt identity/telescope          yes
P3 physical separation producer              open
R211 concrete same-output residual payment   open
R568 commutator-only spacetime producer      open
R572 compiler                                constructed given its receipts
R503 R500->R415 compiler surface             constructed
Clay/global regularity promotion             false
```

The immediate proof priority is therefore not broad archaeology.  It is:

```text
P3 fixed-output compressed-partner separation
  -> inhabit the existing R211 payment socket
  -> determine the shortest same-object transplant into the modern signed route
  -> prove R568
  -> consume through R572/R503
```

R214 remains an explicit negative control: even zero-width shell localization
can coexist with positive aligned between-partner debt.  Consequently shell
localization alone is not the missing producer.

The older routes below are retained deliberately.  They record serious earlier
proof attempts, diagnostics, theorem-bearing sub-results, falsifiers, and route
selection decisions.  They are no longer the freshest statement of the live
proof frontier, but they must remain visible so the construction history is not
rewritten after the fact.

## Historical A1-A9 / ESS / Abel packet

The 2026-06 Paper-1 route concentrated the claimed new mathematics around the
coupled `A1/A3` Abel-defect/quantitative-stationarity bootstrap and the `A4`
Lei-Ren-Tian-to-Fourier output-support transfer with a uniform constant across
Type-I rescalings.

The repo built exact candidate theorem grammar for `A1.1-A3.4`, `A4.1-A4.5`,
and the downstream `A5-A9` consumer ladder.  Candidate `epsilon = 1/6`,
candidate `delta_r = O(r^(1/12))`, and candidate coarea/Jacobian/strip-hitting
constants were recorded as inputs rather than accepted local proofs.

This route remains a historical/alternative reduction.  It was superseded as
the primary manuscript spine because the later R104/R406/direct-companion
archaeology exposed a shorter same-object chain with one live R568 spacetime
producer.  Its theorem-bearing pieces remain useful provenance and donor
material.

## Historical EV5 / theta / carrier programme

A separate fail-closed line explored NS-to-EV5 projection, forward simulation,
quotient correctness, conditional lane preservation, ultrametric preservation,
and theta < 1 maximum-principle preservation.  None of those historical
interfaces supplied the modern R568 producer, and none is silently promoted by
the current route.

Paper 1 target sidecar: `Docs/NSPaper1ClayTarget.md` records the earlier
Manager-B chain: fixed-K LP identity, theta as `Flux/Diss`, conditional fixed-K
tail decay, danger-shell locator, EV5 projection up to an LP commutator defect,
and open danger-shell maximum-principle/edge-leakage obligations.  It remains a
target document, not a regularity proof.

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
- the non-circular high-high estimate remains the wall for that historical
  route.

The current tower contains receipts for finite energy/BKM targets, ultrametric
Aubin-Lions compactness, a failed 2/3/5 Haar-frame bridge, a carrier weak-form
interface, and a replacement Littlewood-Paley/Besov/parabolic-smoothing target.
Those receipts name blockers. The roadmap below decomposes that historical
blocker into lemmas.

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

## Historical NS-Only Margin Roadmap

This section records the earlier NS-only use of the margin invariant. Other
lanes are out of scope here. The roadmap is obligation tracking only; it does
not prove global smoothness or the Clay Navier-Stokes statement.

| Stage | NS-only obligation | Status |
|---|---|---|
| L0 | Consume the shared margin grammar only as an NS tail-flux margin interface. | Available as bookkeeping. It does not by itself prove any NS estimate. |
| NS1 | Prove the fixed-`K` tail flux identity for the selected shell split. | Receipt surface recorded in `NSTailFluxAbsorptionMarginReceipt`: `K` is fixed during differentiation and moving cutoffs are excluded. `NSTailFluxIdentityAnalyticTargetReceipt` names the exact Littlewood-Paley proof obligations; the analytic identity proof remained open on that route. |
| NS2 | Make the theta profile computable across the relevant shells and times. | Implemented as an evidence-only finite cutoff/time diagnostic in dashiCFD. Computability of the profile is not monotonicity and is not regularity. |
| NS3 | Prove that a positive NS margin implies tail decay in the actual-flow variables. | Open on the historical route. |
| NS4 | Bind a one-way BKM/Serrin continuation implication from the proved tail decay hypotheses. | Open and one-way only. |
| NS5 | Preserve theta under the NS evolution and projection interfaces. | Historical hard open problem; phase, pressure, quotient, and forward-simulation losses were not closed. |
| NS6 | Upgrade preserved theta and continuation to unconditional Clay-level Navier-Stokes regularity. | Uninhabited. |

## Historical Lemma Status

| Lemma | Required mathematical content | Current carrier status | Existing receipt surface | Gap |
|---|---|---|---|---|
| N1 | Prove the global Leray energy inequality in the Archimedean `R3` setting. | Partial/conditional. Finite and ultrametric energy controls exist, but the Archimedean bridge is not proved. | `NavierStokesWeakSolutionInterface`, `UltrametricSobolevUniformBound`, `NSCarrierContinuumLimitReceipt` | Need transfer from carrier/ultrametric coefficients to standard `L2(R3)` energy. |
| N2 | Bind standard local smooth existence for smooth divergence-free initial data. | External authority target only. | `NavierStokesRegularityTowerReceipt`, `ClayMillenniumClosureTargetReceipt` | Need explicit authority boundary and matching initial-data class. |
| N3 | Control enstrophy/vorticity growth for all time. | Uninhabited on this route. | `CarrierBKMControlTargetReceipt`, `EllipticBootstrapReceipt` | Need a global estimate surviving nonlinear stretching. |
| N4 | Apply the Beale-Kato-Majda continuation criterion. | Named blocker only. | `CarrierNSSmoothConvergenceReceipt`, `ClayBlockerUpdateReceipt` | Need finite-time vorticity-integrability control. |
| N5 | Bound `||omega||_infty` from carrier-controlled quantities. | Uninhabited on this route. | `UltrametricSobolevUniformBound`, `WaveletFrameBoundRevisionReceipt` | Need the Archimedean Sobolev/Biot-Savart control consumed by continuation. |
| N6 | Continue the local smooth solution globally. | Uninhabited. | `NavierStokesRegularityTowerReceipt` | No global smooth regularity theorem follows from this route alone. |
| W1 | Prove coefficientwise compactness in the carrier/wavelet representation. | Complete for the roadmap audit branch, not a Clay result. | `UltrametricAubinLionsReceipt`, `AubinLionsBound3Full`, `UltrametricAubinLionsCompactness` | Does not supply continuum smoothness or BKM closure. |
| W2 | Decide whether the 2/3/5 wavelet/frame bridge gives compactness in `L2(R3)`. | Complete as a negative decision for the pure Haar-frame route. | `NSWaveletRouteClosedReceipt`, `HilbertSchmidtBoundGramReceipt`, `NSFrameRestrictionReceipt` | Replacement analytic bridge required. |
| W3 | Pass the nonlinear term `(u . grad)u` to the limit. | Complete only as a fail-closed weak-branch ledger. | `NSCarrierContinuumLimitReceipt`, `NSWeakSolutionFinalReceipt`, `NSWaveletRouteClosedReceipt` | No unconditional continuum Leray theorem or smoothness follows. |
| W4 | Construct or audit a Leray weak-solution branch from the carrier limit. | Complete as a non-promoting weak branch. | `NavierStokesWeakSolutionInterface`, `NSWeakSolutionFinalReceipt`, `ClayNSProofRoadmapReceipt` | Weak NS is not Clay NS. |

## Historical Honest Position

The weak branch was completed only in the fail-closed sense that its carrier
interfaces, conditional route, and negative frame decision were recorded. The
unrestricted 2/3/5 Haar system is not a frame for all of `L2`, because constant
functions pair to zero with pure Haar wavelets. The zero-mean restriction does
not rescue the recorded Gram route because the off-diagonal Hilbert-Schmidt
control diverges. The pure Haar-frame path was therefore closed as a proof
route.

This negative result did not prove or disprove the modern signed/direct route.
A Leray or carrier weak solution is not a smooth global solution.

## 2026-06-05 historical fastest-path selection

`DASHI/Physics/Closure/NSFastestClayPathReceipt.agda` recorded the route
selection after Sprints 56-58 and the negative-Sobolev danger-shell receipts:

```text
retire packet-normalized action as a proof source
-> decide the H^{-1/2} high-high defect gate
-> if the gate passes, prove non-circular K* absorption and theta preservation
-> feed only a proved tail bound to BKM/Serrin
```

If that H^-1/2 gate failed analytically, the correct product was an obstruction
theorem plus a pivot, not Clay promotion. The exact mathematical target was

```text
|| P_{>K*}(u . grad u) ||_{H^{-1/2}}
  <= epsilon * nu * || P_{>K*} u ||_{H^{3/2}}
```

without stronger regularity as input.

`NSHminusHalfGateDecisionPivotReceipt.agda` later recorded obstruction/divergence
evidence and no uniform absorption proof, so that path became an
obstruction-theorem output rather than the canonical Clay route.  A subsequent
historical Path B explored

```text
H^{11/8} Bernoulli-band rigour
-> uniform regularity across dense prime-LP approximations
-> limit uniqueness/stability
-> NS-to-EV5 forward simulation and preservation
-> continuation only after those gates
```

Those gates were not silently promoted and are not the current R568 path.

## Historical Non-Circular K-Star Drift Obstruction

`DASHI/Physics/Closure/NSNonCircularObstructionReceipt.agda` recorded the sharp
obstruction for that route:

```text
High-high paraproduct control at K*(t)
  through an H^{-1/2} nonlinear-defect estimate
  without assuming H^{1/2} velocity regularity, Serrin, BKM,
  or stronger regularity
```

The forbidden circular route was:

```text
Flux_{>K*} <= (1-c) Diss_{>K*}
  -> H^{1/2}-type velocity control
  -> Serrin/BKM-class regularity
  -> regularity assumption smuggled into the proof
```

The admissible replacement route was:

```text
||P_{>K*}(u.grad u)||_{H^{-1/2}}
  <= epsilon * nu * ||P_{>K*}u||_{H^{3/2}}
  -> dual pairing with P_{>K*}u in H^{1/2}
  -> high-high flux absorbed by tail dissipation
```

That receipt treated `NonCircularKStarDriftBound` as an open structural
obstruction, not as a partially proved lemma.  The later prime-LP weak branch
inhabited only a Leray weak-solution route at receipt scope; weak existence is
not uniqueness, smooth continuation, BKM closure, Clay NS, or terminal
promotion.

## Current promotion boundary

The following must remain false until the corresponding modern producers and
authority boundaries are discharged:

- P3 same-output physical separation producer;
- concrete R211 same-output residual payment;
- R568 cutoff-uniform commutator-only spacetime budget;
- unconditional smooth continuum/global regularity;
- Clay Navier-Stokes promotion;
- terminal/unification promotion.

Historical diagnostics that remain non-promoting include:

- theta/danger-shell computability;
- EV5 lane dictionaries or admissibility;
- dashiCFD coherence diagnostics;
- weak/carrier Navier-Stokes existence;
- the failed Haar-frame route;
- historical A1-A9 candidate packages without accepted proofs.

The roadmap operating rule is now:

```text
never restart broad archaeology as a proof step;
search forward from a named unpaid field while retaining old attempts as
historical/provenance evidence.
```
