# Candidate256 Physical Calibration Receipt Template

Status: preflight only. This template does not promote Candidate256 calibration.

## Dependency Skeleton

Exact queue:

```text
AcceptedDYLuminosityConventionAuthority
  + W4ZAdequacyReceipt
  -> Candidate256PhysicalCalibrationExternalReceipt
```

The receipt is admissible only when the accepted DY luminosity convention
authority and the W4 Z adequacy receipt already exist. A citation, local
diagnostic, Z-peak anchor label, or provider note is not a substitute for either
authority surface.

## Required Fields

Provider payload fields:

- `unitCarrier`: physical unit carrier, not the current dimensionless `Nat`
  surrogate by itself.
- `scaleMap`: map from Candidate256 surrogate `Nat` scale values into
  `unitCarrier`.
- `quotientScaleMap`: map from Candidate256 quotient classes into
  `unitCarrier`.
- `candidate256CalibrationConstant`: the calibrated Candidate256 physical
  constant in `unitCarrier`.
- `scaleMapFactorsThroughCandidate256Surrogate`: proof that the quotient scale
  map factors through `candidate256SurrogateScale`.
- `dimensionalPreservationLaw`: dimensional preservation law over
  `canonicalCandidate256QuotientLaw`.
- `dimensionalPreservationAtWitness`: inhabitant of the preservation law at each
  Candidate256 quotient-law witness.
- `externalAuthorityCitation`: external authority citation for the physical
  calibration boundary.
- `validationPayload`: checksum/provenance/measurement payload sufficient for
  later validation.
- `sourceW4ZAdequacyReceipt`: the source W4 adequacy receipt downstream of the
  accepted DY luminosity convention.

## External Boundary

- `AcceptedDYLuminosityConventionAuthority` is missing.
- `W4ZAdequacyReceipt` is missing because it depends on the accepted DY
  authority.
- `Candidate256PhysicalCalibrationAuthorityToken` remains constructorless in the
  W4 calibration gate.
- No Candidate256 physical calibration receipt is inhabited by this template.
- No matter-field or stress-energy handoff is made by this template.

## Remaining Gap

Exact gap: supply an accepted DY luminosity convention authority and a W4 Z
adequacy receipt, then provide the Candidate256 unit carrier, scale maps,
calibration constant, dimensional preservation law, external authority citation,
validation payload, and source W4 adequacy receipt as a single external receipt.
