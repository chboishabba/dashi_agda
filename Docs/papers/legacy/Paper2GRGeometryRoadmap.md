# Paper 2 GR / Geometry Roadmap

Status: companion roadmap; non-promoting; created because no Paper 2 GR /
geometry draft is present in `Docs/` as of 2026-05-29.

This file is owned by the Paper 2 GR/geometry lane.  It audits the current
finite Lorentzian-geometry, discrete GR, sourced-Einstein, and Wald-authority
surfaces that can support a later Paper 2 draft.  It does not modify or depend
on Paper 1 claims.

## Claim Boundary

Paper 2 can safely be framed as a finite-geometry and GR-obligation paper, not
as a completed GR derivation.  The strongest current positive statements are:

- finite orbit-profile and causal-signature surfaces select the Lorentz
  signature class `(3,1)` in the current 4D realization;
- selected finite metric/Ricci/scalar/Einstein tensor shapes are staged locally;
- a contracted-Bianchi/stress-energy closure record composes existing
  fail-closed receipts;
- Wald's continuum GR authority is recorded as an external boundary for
  Levi-Civita uniqueness and the sourced Einstein equation, while continuum and
  sourced promotion bits remain false.

Paper 2 must not claim non-flat GR recovery, sourced Einstein closure,
Schwarzschild recovery, continuum convergence, GRQFT closure, or terminal
unification until the exact receipts below are inhabited.

## Finite Lorentzian Geometry Receipts

Use these as the geometry spine, in this order.

| Surface | Artifact | What it verifies | Boundary |
|---|---|---|---|
| Orbit signature discriminator | `DASHI.Physics.OrbitSignatureDiscriminant.MeasuredProfile`; `SignatureFromMeasuredProfileUnique` | The measured finite profile is the `sig31` profile, with orientation tag `31`; competing tags `40`, `22`, `13`, `04` are rejected at the profile head. | This is a finite profile discriminator, not a smooth Lorentzian manifold. |
| Shift instance | `DASHI.Physics.Signature31InstanceShiftZ.signature31` | The shift realization consumes the cone/arrow/isotropy signature axioms and returns the `sig31` signature in the current finite framework. | Solved for the present realization framework only. |
| Causal lock | `DASHI.Geometry.CausalForcesLorentz31.LorentzSignatureLock`; `quadraticConeIsotropyForces31`; `uniqueLorentz31`; `nonAdmissibleRival` | Packages cone nontriviality, arrow orientation, isotropy, finite speed, involution, nondegenerate quadratic data, and quotient contraction into the `(3,1)` choke point. | The package is a finite/theorem-shape lock; it is not a physical spacetime metric authority. |
| Current explanatory note | `Docs/OrbitShellProfilesAndLorentzSignature.md` | Records the safe language: an Agda-formalized 4D orbit-profile discriminator plus validation program. | Explicitly forbids "physics solved", "GR derived", and full closure language. |

Paper 2 geometry should say "finite Lorentzian signature selection" or
"Lorentz-signature finite geometry", not "continuum Lorentzian manifold" unless
a later continuum authority token is added.

## Discrete GR / Ricci / Einstein Staging

The current GR layer is useful but must be described as staging and receipts,
not as a completed Einstein theorem.

| Surface | Exact artifact | Current value |
|---|---|---|
| Flat/discrete Einstein candidate | `DASHI.Physics.Closure.EinsteinEquationCandidate.canonicalEinsteinEquationCandidateObligationSurface` | The flat-vacuum surface is correct, but the ordered first missing fields include `missingW4MatterCouplingReceipt`, `missingW4SourcedNonFlatConnection`, `missingW4StressEnergyTensor`, and `missingDiscreteEinsteinEquationLaw`. |
| W4 matter/stress diagnostic | `canonicalW4MatterStressEnergyInterfaceDiagnostic` | First missing field is `missingW4AnchorArtifactReceiptForMatterStress`; required receipt name is `DASHI.Physics.Closure.EinsteinEquationCandidate.W4MatterStressEnergyInterfaceReceipt`. |
| Local Ricci/Einstein fibre staging | `DASHI.Physics.Closure.GRDiscreteRicciCandidateFromCurvature.canonicalGRDiscreteRicciCandidateFromCurvature` | Provides local-site-indexed curvature/Riemann/Ricci/scalar/Einstein fibre decomposition sockets.  First missing proof remains `missingBianchiIdentityProof`. |
| Gate 4 local fibre contraction | `canonicalGRDiscreteRicciGate4LocalFibreContractionReceipt` | Stages selected Riemann, Ricci, scalar, and Einstein tensor zero-table components, including `selectedEinsteinTensorFromRicciScalar` and `selectedContractedBianchiDivergenceZero`. |
| Gate 4 selected chain | `canonicalGRDiscreteRicciGate4SelectedChainFailClosedReceipt` | Carries the selected-chain fail-closed handoff; sourced Einstein attachment is blocked. |
| Contracted Bianchi / matter closure | `DASHI.Physics.Closure.ContractedBianchiMatterClosure.canonicalContractedBianchiMatterClosureReceipt` | Composes the selected non-flat scalar algebra, Einstein tensor surface, GR stress-energy boundary, W4 authority obstruction, W4 conserved-source interface, and YM stress-energy substitution surface. `closurePromoted = false`. |

Important current blocker sequence:

1. `missingBianchiIdentityProof`
2. `missingMetricCompatibility`
3. `missingCarrierConnectionIsLeviCivita`
4. `missingW4AnchorArtifactReceiptForMatterStress`
5. `missingW4CalibrationAuthorityForMatterStress`
6. `missingAcceptedDYPDFBackedAdequacyForMatterStress`
7. `missingW4AuthorityBackedMatterField`
8. `missingW4AuthorityBackedStressEnergyTensor`

The local selected finite metric lane has progressed beyond older string-only
status, but the roadmap must preserve the distinction between:

- local finite shape/staging receipts, and
- an authority-backed non-flat sourced Einstein theorem.

## Sourced Einstein Boundary

The sourced equation target appears only as an obligation shape until the W4
source interface exists.

Required theorem-facing receipt:

```text
DASHI.Physics.Closure.EinsteinEquationCandidate.W4MatterStressEnergyInterfaceReceipt
```

Required consumer law after that receipt:

```text
DASHI.Physics.Closure.EinsteinEquationCandidate.W4DiscreteGREquationLawObligation
```

Required receipt tuple before `matterFieldFromW4` and
`stressEnergyTensorFromW4` can be consumed:

- `W4SameRecordZPeakT21T22ArtifactReceiptRequest`
- `Candidate256PhysicalCalibrationExternalReceipt`
- `W5PDFCarrierExternalIntakeRequest`
- `AcceptedDYLuminosityConvention`
- `AcceptedDYPDFBackedW4Adequacy`

Current impossibility guards:

- `w4MatterStressEnergyInterfaceReceiptImpossibleHere`
- `w4MatterStressEnergyInterfaceReceiptImpossibleWithoutAcceptedDYAdequacy`
- `stressEnergyPromotionImpossibleWithoutW4CalibrationAnchorAndAdequacy`

The target label `G_munu = 8pi T_munu` may be named only as the sourced
Einstein obligation boundary.  It must not be described as constructed by the
finite local zero-table receipts.

## Wald Authority Boundary

Exact repo receipt:

```text
DASHI.Physics.Closure.WaldGRAuthorityReceipt.canonicalWaldGRAuthorityReceipt
```

Recorded authority metadata in the receipt:

- title: `General Relativity`
- author: `Robert M. Wald`
- year: `1984`
- publisher: `University of Chicago Press`

Recorded scopes:

- `waldLeviCivitaUniquenessScope`
- `waldSourcedEinsteinEquationScope`
- `waldStressEnergyConservationBoundaryScope`
- `finiteGate4CompatibilityConsumptionScope`

Continuum-promotion blockers recorded by the receipt:

- `missingContinuumSmoothManifoldModel`
- `missingContinuumLorentzianMetricAuthority`
- `missingSelectedNonFlatLeviCivitaInternalProof`
- `missingAuthorityBackedStressEnergyTensor`
- `missingContinuumEinsteinEquationDerivation`

Receipt-level false promotion facts:

- `acceptedContinuumAuthorityConstructedHere = false`
- `continuumLeviCivitaPromoted = false`
- `continuumSourcedEinsteinPromoted = false`

Use Wald as an external authority boundary only: it tells the paper what a
continuum Levi-Civita and sourced Einstein theorem must match, but it does not
turn the finite receipts into continuum GR.  The companion paper bibliography
should cite Wald, `General Relativity`, University of Chicago Press, 1984, and
Einstein's 1915 field-equation source for the historical equation boundary.

## Friedmann Instability Authority Boundary

Exact repo receipt:

```text
DASHI.Physics.Closure.FriedmannInstabilitySaddleReceipt.canonicalFriedmannInstabilitySaddleReceipt
```

Recorded authority metadata in the receipt:

- title: `The instability of critical and underdense Friedmann spacetimes at
  the Big Bang as an alternative to dark energy`
- authors: `C. Alexander, B. Temple, and Z. Vogler`
- journal: `Proceedings of the Royal Society A 482:20250912`
- DOI: `10.1098/rspa.2025.0912`
- local PDF SHA256:
  `a105917e23d118c6c41004292c2ecb2a32f042dec738ccd2c380253e0eace6cf`

The receipt records the paper's Einstein-Euler self-similar variable
`xi = r/t` and the authority-backed statement that pressureless Friedmann
spacetimes are unstable to radial perturbation, with the critical Friedmann
solution an unstable saddle rest point.  It consumes the contracted-Bianchi
matter closure and Wald authority receipts, but it does not identify `xi` with
DASHI carrier depth internally.  The live blockers are
`missingEinsteinEulerCarrierODEDerivation`,
`missingSelfSimilarXiCarrierIdentificationProof`,
`missingContinuumExistenceTheoryCompletion`,
`missingCarrierPhasePortraitTransportMap`, and
`missingObservationalCosmologyModelComparison`.

Paper 2 may cite this result as a Gate 4 relevant external theorem about the
solution space of the Einstein-Euler equations.  It must not claim that DASHI
has removed dark energy or falsified LCDM: the receipt keeps
`darkEnergyRemoved = false`, `LCDMFalsified = false`, and
`cosmologyPromoted = false`.

## Paper 2 Section Map

1. Finite Lorentzian signature:
   `MeasuredProfile`, `SignatureFromMeasuredProfileUnique`,
   `signature31`, `LorentzSignatureLock`.
2. Finite metric and local curvature staging:
   `GRSelectedNonFlatMetricInstance.selectedGRNonFlatMetricDependency`,
   `canonicalGRDiscreteRicciCandidateFromCurvature`,
   `canonicalGRDiscreteRicciGate4LocalFibreContractionReceipt`.
3. Contracted Bianchi and source boundary:
   `canonicalContractedBianchiMatterClosureReceipt`,
   `canonicalW4MatterStressEnergyInterfaceDiagnostic`.
4. Wald/Einstein/Friedmann-instability authority boundary:
   `canonicalWaldGRAuthorityReceipt`,
   `canonicalFriedmannInstabilitySaddleReceipt`,
   `AcceptedContinuumGRAuthorityToken` as constructorless boundary,
   `W4DiscreteGREquationLawObligation` as downstream target.
5. Blocker ledger:
   exact missing fields above, with no prose-only "almost done" language.

## Remaining Blockers Before Stronger Paper 2 Claims

To promote from roadmap to theorem paper, the next workers must provide:

- finite-r Bianchi proof discharging `missingBianchiIdentityProof`;
- selected carrier connection proof discharging `missingCarrierConnectionIsLeviCivita`;
- a real `W4MatterStressEnergyInterfaceReceipt`;
- accepted DY/PDF-backed W4 adequacy and Candidate256 physical calibration;
- authority-backed `MatterField` and `StressEnergyTensor` values;
- a `W4DiscreteGREquationLawObligation` inhabitant with a law at the consumer;
- continuum smooth-manifold and Lorentzian metric authority, if continuum GR
  language is intended;
- metric/connection error bounds and Einstein-tensor continuity before any
  continuum-scaling or Schwarzschild language;
- an accepted continuum authority token before Wald authority is treated as
  more than a boundary record.

Until those artifacts exist, Paper 2 should be titled and abstracted around
finite Lorentzian geometry and fail-closed GR obligation surfaces, not sourced
GR recovery.
