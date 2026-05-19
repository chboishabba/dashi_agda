# Drosophila Candidate Physical Unit Carrier Audit

Date: `2026-05-12`
Owner: `Fermat / PhysicalUnitCarrier and dimensional-preservation lane`
Status: `negative compatibility audit; docs-only; non-promoting`

## Question

Can any existing unit carrier, dimensional-preservation law, or physical
calibration interface consume a Drosophila codon or Candidate256 witness as a
W4 physical-unit carrier?

## Decision

No current local interface can consume the Drosophila genome/codon witness or
the Candidate256 quotient/cross-band witness as a W4 physical-unit carrier.

There is a narrow structural path for Candidate256 only:

```text
AcceptedDYLuminosityConventionAuthority
-> W4ZAdequacyReceipt
-> Candidate256PhysicalCalibrationExternalReceipt
-> W4External.Candidate256PhysicalCalibrationExternalReceipt
-> Candidate256PhysicalUnitCalibration
-> physical scale-setting lane
```

That path is not inhabited locally. The Drosophila codon packet can at most be
candidate support for a future provider request. It does not supply the
physical unit carrier, calibration map, dimensional-preservation law, or
constructorless authority token required by W4.

## Interfaces Found

| Interface | Exact local surface | Can consume Drosophila/Candidate witness now? | Status |
|---|---|---:|---|
| Generic unit calibration receipt | `DASHI/Physics/Closure/HEPDataUnitCalibrationRequirementDiagnostic.agda` / `HEPDataUnitCalibrationRequirementReceipt` | No | Requires `PhysicalUnitCarrier`, `DimensionCarrier`, `dimensionOfUnit`, measured/internal carriers, calibration map, preservation/monotonicity boundary, and constructorless validation authority. |
| W4 physical calibration gate | `DASHI/Physics/Closure/W4PhysicalCalibrationGate.agda` / `Candidate256PhysicalUnitCalibration` | No | Requires `Candidate256PhysicalCalibrationAuthorityToken`, non-surrogate physical unit carrier, calibration map, quotient-scale map, and dimensional-preservation witness. |
| W4 external receipt obligation | `DASHI/Physics/Closure/W4PhysicalCalibrationExternalReceiptObligation.agda` / `Candidate256PhysicalCalibrationExternalReceipt` | No | Exposes the exact receipt shape but proves receipt construction impossible without the constructorless authority token. |
| Candidate256 preflight receipt | `DASHI/Physics/Closure/Candidate256PhysicalCalibrationExternalReceipt.agda` / `Candidate256PhysicalCalibrationExternalReceipt` | No | Adds required upstream `AcceptedDYLuminosityConventionAuthority` and `W4ZAdequacyReceipt`; neither can be supplied by Drosophila/codon data. |
| W4 physical obligation surface | `DASHI/Physics/Closure/W4PhysicalCalibrationObligationSurface.agda` | No | Queue remains `AcceptedDYLuminosityConventionAuthority -> W4ZAdequacy -> Candidate256PhysicalCalibrationExternalReceipt`. |
| Scale-setting obligation | `DASHI/Physics/Closure/W4StrictPhysicalScaleSettingLaneObligation.agda` / `Candidate256ScaleSettingLaneFields` | Partially, structurally only | Accepts a carrier/map/law shape, but W4 gate forbids treating the local `Nat` surrogate as physical calibration. |
| Surrogate scale boundary | `DASHI/Physics/Closure/W4SurrogateScaleSettingBoundary.agda` | No physical consumption | Provides `Nat` surrogate scale and trivial preservation over surrogate endpoints only; explicitly non-physical. |
| Drosophila genome candidate | `DASHI/Physics/Closure/DrosophilaGenomeW4CandidateAuthorityReceipt.agda` | No | Checksum-bound codon witness; flags calibration law, authority token, physical receipt, Brain handoff proof, and W4 promotion as false. |
| Brain atomic chemistry handoff | `Ontology/BrainDNA/BrainAtomicChemistryHandoff.agda` | No | Exposes `Nat` cross-band, Hamiltonian, and recovery-boundary handles; no physical units, calibration map, or dimensional law. |
| Candidate256 quotient/cross-band witness | `DASHI/Physics/Closure/ChemistryRightLimitsQuotientCrossBandCandidate256Witness.agda` | No physical consumption | Provides UV-coordinate quotient/cross-band separation law only; pre-scale-setting and not a physical calibration authority. |

## Drosophila Codon Witness Compatibility

The local Drosophila Release 6 packet records a checksum-bound CDS codon
non-uniformity witness:

| Field | Local value |
|---|---:|
| total ACGT codons | `20409720` |
| distinct ACGT codons | `64` |
| max codon | `GAG` |
| max codon count | `867771` |
| min nonzero codon | `TGA` |
| min nonzero codon count | `8978` |

Compatibility status: `negative`.

Reason: the packet records authority/checksum/codon statistics only. It
explicitly does not construct:

```text
Candidate256PhysicalCalibrationAuthorityToken
Candidate256PhysicalCalibrationExternalReceipt
BrainAtomicChemistryHandoffProof
W4 promotion
```

The codon counts are not a physical unit carrier. They do not define
`dimensionOfUnit`, a calibrated `Nat -> unitCarrier` map, a quotient-scale map,
or a dimensional-preservation inhabitant.

## Candidate256 Witness Compatibility

The Candidate256 quotient/cross-band witness is locally present and typed. It
provides:

```text
CanonicalQuotientCrossBandCouplingCandidate256
ChemistryRightLimitsQuotientCrossBandCouplingRequirement
ChemistryRightLimitsQuotientCrossBandCouplingTheorem
ChemistryRightLimitsLaw
ChemistryRightLimitsQuotientCrossBandLaw
```

Compatibility status: `structural prerequisite only; not consumable as
physical calibration`.

It can feed the W4 obligation surface as a pre-scale-setting witness, but only
after an external physical calibration receipt supplies units, calibration, and
dimensional preservation. Existing W4 docs and Agda surfaces state that the
Candidate256 witness must not be treated as physical calibration authority.

## Missing Field List

To become consumable by the current W4 physical-calibration interfaces, a
future provider payload must supply at least:

| Missing field | Required by |
|---|---|
| `AcceptedDYLuminosityConventionAuthority` | W4 queue before W4 adequacy |
| `W4ZAdequacyReceipt` | Candidate256 physical receipt precondition |
| `Candidate256PhysicalCalibrationAuthorityToken` | W4 physical calibration gate; constructorless locally |
| `PhysicalUnitCarrier` / `unitCarrier` distinct from dimensionless `Nat` | W4 gate and Candidate256 external receipt |
| `DimensionCarrier` and `dimensionOfUnit` if using generic HEPData unit receipt | HEPData unit calibration receipt |
| `natToUnitCalibrationMap` / `scaleMap : Nat -> unitCarrier` | Candidate256 external receipt |
| `calibratedQuotientScaleMap` / `quotientScaleMap : Candidate256QuotientClass -> unitCarrier` | Candidate256 external receipt |
| `candidate256CalibrationConstant : unitCarrier` | Candidate256 preflight receipt |
| factorization proof through `candidate256SurrogateScale` | Candidate256 external receipt |
| `dimensionalPreservationLaw : QuotientLawAtWitness canonicalCandidate256QuotientLaw -> Set` | W4 gate and Candidate256 receipt |
| `dimensionalPreservationAtWitness` inhabitant | W4 gate and Candidate256 receipt |
| source/provider citation and authority boundary | Candidate256 preflight receipt |
| validation payload with checksums/provenance/review | Candidate256 preflight receipt |

## Non-Promotion Boundary

This audit does not:

```text
promote a Drosophila codon count to physical units
promote Nat as a physical unit carrier
construct Candidate256PhysicalCalibrationAuthorityToken
construct Candidate256PhysicalCalibrationExternalReceipt
construct W4ZAdequacyReceipt
construct matterFieldFromW4
construct stressEnergyTensorFromW4
promote W4, Brain, physics, GR, or limited SM+GR closure
```

## Sources Inspected

- `DASHI/Physics/Closure/HEPDataUnitCalibrationRequirementDiagnostic.agda`
- `DASHI/Physics/Closure/W4PhysicalCalibrationGate.agda`
- `DASHI/Physics/Closure/W4PhysicalCalibrationExternalReceiptObligation.agda`
- `DASHI/Physics/Closure/Candidate256PhysicalCalibrationExternalReceipt.agda`
- `DASHI/Physics/Closure/W4PhysicalCalibrationExternalReceiptRequestPack.agda`
- `DASHI/Physics/Closure/W4PhysicalCalibrationObligationSurface.agda`
- `DASHI/Physics/Closure/W4StrictPhysicalScaleSettingLaneObligation.agda`
- `DASHI/Physics/Closure/W4SurrogateScaleSettingBoundary.agda`
- `DASHI/Physics/Closure/DrosophilaGenomeW4CandidateAuthorityReceipt.agda`
- `DASHI/Physics/Closure/ChemistryRightLimitsQuotientCrossBandCandidate256Witness.agda`
- `DASHI/Physics/Closure/ChemistryRightLimitsQuotientCrossBandCandidate256Shape.agda`
- `DASHI/Physics/Closure/ChemistryRightLimitsQuotientCrossBandCouplingRequirement.agda`
- `Ontology/Brain/DrosophilaHemibrainExternalRunReceipt.agda`
- `Ontology/Brain/DrosophilaCoarseGrainPersistenceObstruction.agda`
- `Ontology/BrainDNA/BrainAtomicChemistryHandoff.agda`
- `Docs/DrosophilaGenomeW4CandidateAuthority.md`
- `Docs/BrainPhysicsBoundaryHandles.md`
- `Docs/Candidate256CalibrationDependencyAudit.md`
- `Docs/Candidate256PhysicalCalibrationAuthorityRequest.md`
