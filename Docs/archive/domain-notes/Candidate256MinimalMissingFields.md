# Candidate256 Minimal Missing Fields

Date: `2026-05-06`
Owner: `Kelvin`
Status: `minimal blocker map; non-promoting`

## Scope

This note reduces the Candidate256 physical-calibration blocker to the smallest
field set still missing from
`DASHI.Physics.Closure.Candidate256PhysicalCalibrationExternalReceipt`.

It does not add a new skeleton, construct an authority token, inhabit a receipt,
promote the `Nat` surrogate to a physical unit carrier, or promote W4.

## Classification Key

| Class | Meaning |
|---|---|
| Available | Already named or mechanically present in the local repo and not itself a missing provider datum. |
| Derivable after W4 | Can be filled from the accepted W4 Z-adequacy receipt once W4 adequacy has landed. |
| External authority required | Requires a positive external authority artifact or provider payload; local labels, diagnostics, fits, and citations are not enough. |
| Unknown | Not currently determined by the local repo or by the W4 adequacy result. |

## Minimal Field Classification

| Receipt field | Class | Minimal reason |
|---|---|---|
| `acceptedDYLuminosityConventionAuthority` | Derivable after W4 | A valid W4 Z-adequacy receipt already depends on accepted DY authority, so this can be copied from the source W4 receipt after W4 exists. Before W4, it is still blocked. |
| `sourceW4ZAdequacyReceipt` | Derivable after W4 | This is the W4 receipt itself. It is unavailable now, but no separate Candidate256 provider field is needed after W4 adequacy lands. |
| `sourceW4AdequacyReceiptName` | Derivable after W4 | Name, digest, or path can be derived from the accepted W4 receipt artifact selected for intake. |
| `candidate256PhysicalCalibrationAuthority` | External authority required | The `Candidate256PhysicalCalibrationAuthorityToken` is constructorless in-repo. It must be supplied by a legitimate external physical-calibration authority. |
| `unitCarrier` | External authority required | The physical unit carrier is not the current dimensionless `Nat` surrogate. It must come with the physical-calibration authority payload. |
| `scaleMap` | External authority required | The `Nat -> unitCarrier` calibration map is a physical calibration datum, not derivable from W4 adequacy alone. |
| `quotientScaleMap` | External authority required | The quotient-class scale map must be supplied or accepted by the same calibration authority. |
| `candidate256CalibrationConstant` | External authority required | The calibrated Candidate256 constant in the external unit carrier is a provider datum. |
| `scaleMapFactorsThroughCandidate256Surrogate` | External authority required | The factorization proof is required to connect the quotient map to `candidate256SurrogateScale`; local surfaces name the obligation but do not inhabit it. |
| `dimensionalPreservationLaw` | External authority required | The law family over `canonicalCandidate256QuotientLaw` is part of the physical-calibration authority boundary. |
| `dimensionalPreservationAtWitness` | External authority required | The witness inhabitant for every quotient-law witness must accompany the dimensional law. |
| `externalAuthorityCitation` | External authority required | Citation/provenance must identify the authority artifact that supplied the calibration, but citation alone does not inhabit the token. |
| `validationPayload` | External authority required | Checksum, provenance, measurement, and review payload must validate the external calibration receipt, not just the W4 adequacy run. |
| `externalAuthorityBoundary` | External authority required | Boundary text must tie the accepted external authority artifact to the receipt and no-promotion limits. |

## Already Available Local Surfaces

These are not remaining missing fields:

- The dependency order:
  `AcceptedDYLuminosityConventionAuthority -> W4ZAdequacyReceipt -> Candidate256PhysicalCalibrationExternalReceipt`.
- The W4 adequacy formula and fail-closed runner surface.
- The Candidate256 quotient-law and surrogate-scale names consumed by the
  required factorization and dimensional-preservation fields.
- The adapter from the Candidate256 receipt to the older W4 external receipt
  shape.
- Provider-facing request text listing the required receipt fields.

## Minimal Blocker

After W4 adequacy lands, the Candidate256 calibration blocker reduces to one
external authority payload with these irreducible contents:

```text
Candidate256PhysicalCalibrationAuthorityToken
unitCarrier
scaleMap : Nat -> unitCarrier
quotientScaleMap : Candidate256QuotientClass -> unitCarrier
candidate256CalibrationConstant : unitCarrier
scaleMapFactorsThroughCandidate256Surrogate
dimensionalPreservationLaw
dimensionalPreservationAtWitness
externalAuthorityCitation
validationPayload
externalAuthorityBoundary
```

No field is currently classified as `Unknown`. The uncertainty is not field
shape; it is whether an acceptable external authority will provide the required
physical calibration payload.

## Non-Promotion Guard

This document does not:

```text
construct AcceptedDYLuminosityConventionAuthority
construct W4ZAdequacyReceipt
construct Candidate256PhysicalCalibrationAuthorityToken
construct Candidate256PhysicalCalibrationExternalReceipt
promote the Nat surrogate to a physical unit carrier
construct matterFieldFromW4
construct stressEnergyTensorFromW4
promote W4, GR, or limited SM/QFT+GR closure
```
