# GR First-Order Gravity Scope

Status: typed G4 obligation surface; non-promoting.

Agda module:

```text
DASHI/Physics/Closure/GRFirstOrderGravityScope.agda
```

This scope records the first-order/BF/MacDowell-Mansouri route for G4. It does
not claim GR closure, an Einstein equation theorem, or a GR/QFT promotion
receipt.

## Why This Scope Exists

The current GR route has an explicit `F^2` versus `R` boundary:

- a Yang-Mills-style curvature-norm action naturally gives a quadratic
  curvature invariant;
- the Einstein-Hilbert action is linear in the Ricci scalar;
- therefore the GR lane needs a first-order route, not a silent promotion from
  a curvature-norm bridge.

The scoped route is first-order gravity: a structure group such as `E8`,
`SO(2,3)`, `SO(3,2)`, `ISO(1,3)`, or a typed substitute, together with a
vierbein, spin connection, curvature two-form, and a
Palatini/BF/MacDowell-Mansouri action restriction.

## Already Inhabited Inputs

The module records the current GR-facing surfaces under
`G4CurrentGRInputs`:

| Field | Source |
|---|---|
| `knownLimitsGRBridge` | `canonicalKnownLimitsGRBridgeTheorem` |
| `partialGRQFTConsumer` | `canonicalGRQFTPartialConsumerReceipt` |
| `einsteinEquationCandidate` | `canonicalEinsteinEquationCandidateObligationSurface` |
| `w4StressEnergyInternalBridge` | `canonicalW4MatterStressEnergyAdapterObstruction` |

These are useful inputs, but none is a first-order GR theorem.

## First-Order Geometry Obligations

`G4FirstOrderGeometryObligations` names the geometry and action fields a real
G4 theorem must supply:

| Obligation field | Purpose |
|---|---|
| `StructureGroupCarrier` | carrier for the first-order structure group |
| `selectedStructureGroupCandidate` | `E8`, `SO(2,3)`, `SO(3,2)`, `ISO(1,3)`, or substitute |
| `VierbeinCarrier` | vierbein/frame field carrier |
| `SpinConnectionCarrier` | spin connection carrier |
| `CurvatureTwoFormCarrier` | curvature of the spin connection |
| `BFActionCarrier` | BF presentation of the first-order action |
| `MacDowellMansouriActionCarrier` | MacDowell-Mansouri presentation after breaking/substitute |
| `CouplingCarrier` | coupling normalization carrier |
| `EmbeddingIndexCarrier` | embedding-index carrier for the selected structure-group embedding |
| `palatiniBFActionRestriction` | first-order action restriction from vierbein and curvature |
| `palatiniBFActionRestrictedFromSpine` | proof that the spine action restricts to that form |
| `macDowellMansouriBreakingOrScopedSubstitute` | symmetry breaking or bounded substitute needed by the route |
| `bfMacDowellMansouriActionEquivalent` | proof obligation equating BF and MacDowell-Mansouri action presentations |
| `couplingEmbeddingIndexCaveatDischarged` | proof obligation for coupling normalization and embedding-index caveat |

## Sourced Einstein Obligations

`G4FirstOrderSourcedEinsteinObligations` keeps the matter source separate from
the geometry route:

| Obligation field | Purpose |
|---|---|
| `MatterStressEnergyCarrier` | authority-backed physical stress-energy carrier |
| `CurvatureCarrier` | curvature consumer from first-order geometry |
| `EinsteinEquationCarrier` | Einstein-equation consumer carrier |
| `stressEnergyFromW4` | adapter from W4 stress-energy into the source carrier |
| `einsteinEquationConsumer` | sourced equation consumer |
| `sourcedEinsteinEquationLaw` | law for the consumer |

The current W4 MDL bridge is internal and dimensionless. It is not yet an
authority-backed physical stress-energy source.

## G6 Dependency

`G4FirstOrderSpinePreservationObligations` names the section required by G6:

```text
firstOrderGRSpineSection :
  embedFirstOrderGRInSpine (recoverFirstOrderGRFromSpine spine) == spine
```

This is the G6 `section-GR` dependency. It remains unsatisfied.

## W4-Gated Finite-r Bianchi / Matter Surface

The next admissible GR refinement is not a closure theorem. It is a typed
obligation surface that keeps finite-r Bianchi, W4 matter/stress-energy, and
the sourced Einstein consumer in one order:

```text
GRFiniteRTheoremKernel
-> W4MatterStressEnergyInterfaceReceipt
-> GRFiniteRW4BianchiMatterTheoremObligation
```

The theorem-facing obligation is parameterized by a future
`EinsteinEquationCandidate.W4MatterStressEnergyInterfaceReceipt`. The current
repo does not inhabit that receipt, because Candidate256 physical calibration
authority and accepted DY/PDF-backed W4 adequacy are still absent. Therefore
the canonical surface can only record:

- the existing finite-r theorem kernel as a prerequisite packet;
- the W4 matter/stress-energy diagnostic and first missing W4 anchor receipt;
- the finite-r Bianchi law obligation for the selected curvature carrier;
- the finite-r stress-energy compatibility/conservation obligation;
- the finite-r sourced Einstein-law obligation after Bianchi and W4 matter
  compatibility.

No finite-r Bianchi theorem, W4 stress-energy source, sourced Einstein equation,
GR closure, G4 closure, or GR/QFT promotion follows from this surface.

## Discrete Bianchi Finite-r Sidecar

`DASHI.Physics.Closure.GRDiscreteBianchiFiniteR` is a narrower sidecar scope for
the Jacobi-to-Bianchi bridge. It inspects the current GR, Einstein-equation,
discrete-curvature, CRT-connection, and carrier Lie algebra surfaces, then names
the bridge that is still missing:

```text
finite-r carrier Lie bracket + Jacobi witness
-> curvature-as-bracket-defect / covariant cyclic sum
-> finite-r Bianchi law
```

The current repo has abstract Jacobi vocabulary in
`DASHI.Combinatorics.String.LieAlgebra` and
`DASHI.Physics.Constraints.Bracket.LieLike`, plus GR-facing finite-r and
Einstein obligation surfaces. It does not yet bind those pieces to a finite-r
connection, curvature-as-commutator-defect construction, covariant exterior
derivative/cyclic-sum operator, or finite-r Bianchi witness.

The exact sidecar missing ingredients are:

- finite-r base carrier;
- finite-r neighborhood/cell complex;
- finite-r derivation carrier;
- finite-r carrier Lie bracket;
- Jacobi witness for that finite-r bracket;
- finite-r connection or shift law;
- curvature-as-bracket-defect construction;
- covariant exterior derivative or cyclic-sum Bianchi expression;
- Jacobi-to-Bianchi bridge;
- finite-r Bianchi law;
- curvature-to-Ricci/Einstein contraction boundary;
- metric contraction from finite-r curvature to Ricci;
- trace=4 reduction law for the selected metric/signature surface;
- stress-energy compatibility for any later contracted-Bianchi consumer.

The sidecar also names the next algebraic consequence surface:

```text
GRFiniteRRicciFromBianchiObligation.ricciFromBianchi
GRFiniteRRicciFromBianchiObligation.vacuumRicciZero
```

These are obligations, not inhabited theorems. `ricciFromBianchi` needs the
finite-r metric contraction from curvature to Ricci, and the vacuum Ricci-zero
surface additionally needs the trace=4 law that relates the selected
metric/signature contraction to the vacuum Einstein expression.

This sidecar does not claim vacuum Einstein closure. The flat-vacuum candidate
remains only the existing diagnostic surface, and no finite-r GR promotion,
curvature/Ricci contraction theorem, `ricciFromBianchi` proof, vacuum Ricci-zero
proof, sourced Einstein law, or GR/QFT receipt is constructed here.

## Postulate Boundary

The Agda file has three postulates, all explicitly named as obligations:

```text
obligationFirstOrderGeometryFields
obligationFirstOrderSourcedEinsteinFields
obligationFirstOrderSpinePreservationFields
```

They are not theorem witnesses. They keep the route typed while preserving the
promotion boundary.

## Residual G4 Blockers

The exact missing fields are:

- `missingStructureGroupTheorem`;
- `missingVierbeinCarrier`;
- `missingSpinConnectionCarrier`;
- `missingCurvatureTwoForm`;
- `missingPalatiniBFActionRestriction`;
- `missingMacDowellMansouriBreakingOrScopedSubstitute`;
- `missingBFMacDowellMansouriActionEquivalence`;
- `missingCouplingEmbeddingIndexCaveat`;
- `missingW4StressEnergySource`;
- `missingEinsteinEquationConsumer`;
- `missingFirstOrderSpinePreservationSection`.

## No-Promotion Boundary

`canonicalGRFirstOrderGravityScope` records:

- no G4 GR theorem is constructed;
- no Einstein equation theorem is constructed;
- no accepted first-order structure group is selected, including `E8` or
  `SO(2,3)`;
- no vierbein, spin connection, curvature, or first-order action restriction
  proofs are constructed;
- no BF/MacDowell-Mansouri action equivalence, coupling normalization, or
  embedding-index discharge is constructed;
- no internal MDL stress-energy bridge is promoted to physical stress-energy;
- no `GRQFTClosurePromotionReceipt` is constructed;
- G6 `section-GR` remains unsatisfied.
