# Theorem 3.1: Finite-Depth Non-Flat Yang-Mills Curvature Witness

## Theorem 3.1

The DASHI carrier produces a non-flat discrete Yang-Mills geometry at finite
depth.  More precisely, in the depth-9 finite carrier surface there is a
selected `SFGCSite2D` connection whose curvature 2-form has an inhabited
non-vacuum component on the reference plaquette:

```agda
DASHI.Physics.Closure.Depth9ConnectionAndCurvature.chainB1FiniteFANonzeroAtReference
```

This identifier states that the selected reference curvature evaluates to the
non-vacuum phase `φ1`:

```agda
SFGC.sfgcSite2DEvaluate2
  YMObs.sfgcReferenceNonFlatCurvature2Form
  YMObs.sfgcReferencePlaquette
≡
SPTI4.φ1
```

The companion identifier

```agda
DASHI.Physics.Closure.Depth9ConnectionAndCurvature.chainB1FiniteFANotVacuumAtReference
```

states that this same component cannot be identified with the vacuum phase
`φ0` without contradiction:

```agda
SFGC.sfgcSite2DEvaluate2
  YMObs.sfgcReferenceNonFlatCurvature2Form
  YMObs.sfgcReferencePlaquette
≡
SPTI4.φ0 →
YMObs.YMSFGCEmpty
```

Thus the finite carrier has a checked discrete curvature witness in the
literal sense needed here: a named finite field-strength/curvature component is
present, it computes to `φ1`, and it is separated from the vacuum component
`φ0`.  This is the precise formal substitute for the informal slogan
`F_A != 0` in the Paper 3 finite-depth setting.

The depth-9 receipt now packages this as a finite curvature 2-form on the full
available plaquette carrier, not merely as an isolated reference lookup.  The
record

```agda
DASHI.Physics.Closure.Depth9ConnectionAndCurvature.canonicalDepth9FiniteCarrierCurvature2Form
```

fixes `twoCellCarrier` to `SFGC.SFGCSite2DPlaquette`, `phaseCarrier` to
`SPTI4.Phase4`, and `curvatureComponent` to evaluation of
`YMObs.sfgcReferenceNonFlatCurvature2Form`.  The exported law

```agda
DASHI.Physics.Closure.Depth9ConnectionAndCurvature.depth9FiniteCurvatureComponentCoversEveryAvailable2Cell
```

states that this component function agrees with the finite 2-form evaluator
on every available plaquette.  The concrete numerical component used in the
theorem remains the reference value:

```agda
DASHI.Physics.Closure.Depth9ConnectionAndCurvature.depth9FiniteCurvatureAtReference
```

which computes to `SPTI4.φ1`.

## Formal Support

The theorem is backed by the following Agda surfaces.

- `DASHI.Physics.Closure.Depth9ConnectionAndCurvature`
  - `Depth9ConnectionAndCurvatureReceipt`
  - `canonicalDepth9ConnectionAndCurvatureReceipt`
  - `Depth9FiniteCarrierCurvature2Form`
  - `canonicalDepth9FiniteCarrierCurvature2Form`
  - `depth9FiniteCurvatureComponent`
  - `depth9FiniteCurvatureComponentCoversEveryAvailable2Cell`
  - `depth9FiniteCurvatureAtReference`
  - `ChainB1ExplicitNonzeroYMCurvatureFiniteComputation`
  - `canonicalChainB1ExplicitNonzeroYMCurvatureFiniteComputation`
  - `chainB1FiniteFANonzeroAtReference`
  - `chainB1FiniteFANotVacuumAtReference`

- `DASHI.Physics.Closure.YangMillsFieldEquationObstruction`
  - `sfgcReferenceNonFlat1Form`
  - `sfgcReferenceNonFlatCurvature2Form`
  - `sfgcReferenceNonFlatFieldStrengthBridge`
  - `sfgcReferencePlaquette`
  - `sfgcReferenceNonFlatCurvatureAtReference`
  - `sfgcReferenceNonFlatFieldStrengthAtReference`
  - `sfgcReferenceNonFlatCurvatureAtReferenceNotVacuum`
  - `localFiniteLie3BracketAntisymmetry`
  - `localFiniteLie3JacobiWitness`
  - `canonicalYMSFGCUpper6U2DASquaredBracketStrictReceipt`
  - `yangMillsUpper6U2DASquaredBracketStrictLocalReceiptIsCanonical`

The depth-9 receipt also records the finite algebra and operator staging used
by this theorem.  In particular,
`Depth9ConnectionAndCurvatureReceipt.localFiniteBracketAntisymmetryIsCanonical`
and
`Depth9ConnectionAndCurvatureReceipt.localFiniteJacobiWitnessIsCanonical`
identify the finite Lie-3 bracket witnesses with
`YMObs.localFiniteLie3BracketAntisymmetry` and
`YMObs.localFiniteLie3JacobiWitness`.  The field
`Depth9ConnectionAndCurvatureReceipt.localFiniteDASquaredEqualsBracketFIsCanonical`
identifies the staged finite `D_A^2 = [F_A,_]` receipt with
`YMObs.canonicalYMSFGCUpper6U2DASquaredBracketStrictReceipt`.

## Proof

The proof is by direct reference to the finite computation surface in
`DASHI.Physics.Closure.Depth9ConnectionAndCurvature`.

First, `canonicalDepth9FiniteCarrierCurvature2Form` fixes the available
two-cells to `SFGC.SFGCSite2DPlaquette`, fixes the phase carrier to
`SPTI4.Phase4`, and fixes the curvature 2-form to the already existing
reference curvature
`YMObs.sfgcReferenceNonFlatCurvature2Form`.  Its field
`curvature2FormIsDelta1ReferenceConnection` records that this 2-form is the
`δ1` curvature of the selected reference connection
`YMObs.sfgcReferenceNonFlat1Form`.

The same record includes the finite matrix and commutator evidence used by the
carrier lane: `finiteMatrixSymmetryIsCanonical` identifies the symmetry
package with `SFMS.shiftFiniteMatrixSymmetry`,
`localFiniteCommutatorIsCanonical` identifies the commutator with
`YMObs.localFiniteLie3Bracket`, and the antisymmetry/Jacobi fields identify
the bracket laws with the existing local finite witnesses.  Its
`curvatureComponentCoversEveryAvailable2Cell` and
`fieldStrengthCoversEveryAvailable2Cell` fields make the 2-form and
field-strength bridge total over the available finite plaquettes.

Second, the public theorem
`depth9FiniteCurvatureAtReference` specializes the finite curvature component
to the reference plaquette and returns the equality

```agda
depth9FiniteCurvatureComponent YMObs.sfgcReferencePlaquette
≡
SPTI4.φ1
```

Third, the more explicit Chain B1 surface packages the same computation under
the Yang-Mills curvature notation.  The record
`ChainB1ExplicitNonzeroYMCurvatureFiniteComputation` contains both
`finiteCurvatureComputesPhi1` and `finiteFieldStrengthComputesPhi1`, and its
canonical inhabitant exposes the public theorem
`chainB1FiniteFANonzeroAtReference`.  The companion
`chainB1FiniteFANotVacuumAtReference` supplies the non-vacuum separation from
`φ0`.

Therefore the finite carrier contains a non-flat discrete curvature witness:
the reference finite curvature is inhabited, evaluates to `φ1`, and cannot be
collapsed to `φ0`.

## Scope and Non-Promotion Boundary

Theorem 3.1 is a finite-depth discrete geometry theorem.  It is not the Clay
Yang-Mills existence and mass gap problem, and it does not assert continuum
Yang-Mills existence, a continuum mass gap, a physical Stone spectral lower
bound, or a strict real `SU(3)` Hodge Yang-Mills equation.

The fail-closed boundaries are explicit in the checked files:

- `DASHI.Physics.Closure.Depth9ConnectionAndCurvature`
  - `Depth9ConnectionAndCurvatureReceipt.gate3NonFlatPromotionClaimed`
  - `Depth9ConnectionAndCurvatureReceipt.gate3NonFlatPromotionClaimedIsFalse`
  - `Depth9FiniteCarrierCurvature2Form.finiteCarrierPromotedToStrictRealSU3HodgeYM`
  - `Depth9FiniteCarrierCurvature2Form.finiteCarrierPromotedToStrictRealSU3HodgeYMIsFalse`
  - `ChainB1ExplicitNonzeroYMCurvatureFiniteComputation.strictRealSU3HodgeYMPromoted`
  - `ChainB1ExplicitNonzeroYMCurvatureFiniteComputation.strictRealSU3HodgeYMPromotedIsFalse`

- `DASHI.Physics.Closure.YangMillsFieldEquationReceipt`
  - `YangMillsFieldEquationReceipt`
  - `canonicalYangMillsFieldEquationReceipt`
  - `yangMillsFieldEquationReceiptStatusIsObligationOnly`
  - `canonicalYangMillsFieldEquationUnsupportedClaims`
  - `routeBSelectedDStarFEqualsJLaw`
  - `canonicalYMSFGCRouteBLowerHodgeCurrentSurface`
  - `canonicalYMSFGCGate3M1U2M2WorkerReceipt`
  - `YMSFGCGate3M1U2M2WorkerReceipt.receiptPromotedIsFalse`
  - `YMSFGCGate3M1U2M2WorkerReceipt.m1ExactBlockerIsNonFlatCurvature`
  - `YMSFGCGate3M1U2M2WorkerReceipt.u2ExactTransportBlockerIsFieldStrengthAction`
  - `YMSFGCGate3M1U2M2WorkerReceipt.m2ExactBlockerIsVariationPairing`

- `DASHI.Physics.Closure.YangMillsFieldEquationObstruction`
  - `missingNonFlatSFGCSite2DConnectionCurvature`
  - `missingFieldStrengthTransportActionOnSelectedGaugeBundle`
  - `missingVariationPairingForSelectedHodgeStar`
  - `yangMillsUpper6U2DASquaredBracketStrictReceiptNonPromoting`
  - `yangMillsUpper6U2DASquaredBracketStrictNonFlatBlockerIsExact`
  - `yangMillsUpper6U2DASquaredBracketStrictTransportBlockerIsExact`
  - `yangMillsUpper6U2DASquaredBracketStrictVariationBlockerIsExact`

- `DASHI.Physics.Closure.YangMillsMassGapBoundary`
  - `YangMillsMassGapBoundaryReceipt.massGapTargetRecorded`
  - `YangMillsMassGapBoundaryReceipt.massGapTargetRecordedIsTrue`
  - `YangMillsMassGapBoundaryReceipt.massGapPromoted`
  - `YangMillsMassGapBoundaryReceipt.massGapPromotedIsFalse`
  - `YangMillsMassGapBoundaryReceipt.physicalStoneGeneratorEqualsYMHamiltonianPromoted`
  - `YangMillsMassGapBoundaryReceipt.physicalStoneGeneratorEqualsYMHamiltonianPromotedIsFalse`
  - `YangMillsMassGapBoundaryReceipt.physicalStoneSpectralLowerBoundPromoted`
  - `YangMillsMassGapBoundaryReceipt.physicalStoneSpectralLowerBoundPromotedIsFalse`
  - `canonicalYangMillsMassGapOpenObligations`
  - `canonicalYangMillsStoneHamiltonianGapOpenBlockers`
  - `yangMillsMassGapFirstOpenObligation`

The finite field-equation staging should therefore be read exactly as staging.
`DASHI.Physics.Closure.YangMillsFieldEquationReceipt` records lower and
selected finite surfaces for Hodge/current and definitional `D * F = J`
probes, including `routeBSelectedDStarFEqualsJLaw`, but its own boundary text
and promotion fields state that these are not a sourced variational
Yang-Mills equation, not a metric Hodge-star construction, and not a continuum
field equation theorem.

Consequently, Paper 3 may cite Theorem 3.1 for the finite-depth claim:

> the carrier supports a non-flat discrete Yang-Mills curvature witness at
> finite depth.

Paper 3 should not cite this theorem as a Clay problem result, a continuum
constructive Yang-Mills theory, a physical mass-gap theorem, or a completed
strict real `SU(3)` Hodge Yang-Mills equation.
