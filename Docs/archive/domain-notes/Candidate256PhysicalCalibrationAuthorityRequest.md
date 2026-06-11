# Candidate256 Physical Calibration Authority Request

Date: `2026-05-06`
Owner: `Kelvin`
Status: `provider-facing request; conditional on W4; non-promoting`

This request asks an external physical-calibration authority for the exact
Candidate256 calibration payload that could later be consumed by
`DASHI.Physics.Closure.Candidate256PhysicalCalibrationExternalReceipt`.

This is not a calibration claim. The request is explicitly conditional on a
prior accepted `W4ZAdequacyReceipt`. No Candidate256 physical-calibration
receipt can be inhabited until both the source W4 adequacy receipt and the
external Candidate256 authority payload exist.

## Required Queue

The required order is:

```text
AcceptedDYLuminosityConventionAuthority
-> W4ZAdequacyReceipt
-> Candidate256PhysicalCalibrationExternalReceipt
```

The provider response requested here is admissible only after the
`W4ZAdequacyReceipt` is already accepted and named. If W4 adequacy is absent,
failed, incomplete, or only represented by a template, this request remains a
blocked authority request and cannot be promoted to a receipt.

## Provider Action

Return exactly one response class:

1. `accepted-after-W4`: the provider accepts physical calibration for the named
   source `W4ZAdequacyReceipt` and supplies every required field below.
2. `rejected`: the provider rejects the calibration request and names the exact
   invalid or missing assumption.
3. `insufficient`: the provider cannot supply authority, W4 conditioning,
   provenance, dimensional law, validation payload, or any required calibration
   field.

Do not return `accepted-after-W4` unless an actual accepted
`W4ZAdequacyReceipt` is cited by name or digest and every required field is
nonempty.

## Required Accepted Fields

An `accepted-after-W4` response must include all fields below as provider
answers. Placeholders, labels, citations alone, and local diagnostics do not
count as field inhabitants.

| Field | Required provider answer |
|---|---|
| `status` | `accepted-after-W4` |
| `provider_name` | Person, collaboration, service, tool, review body, or governance body supplying the calibration authority |
| `provider_role` | Why the provider can attest Candidate256 physical calibration |
| `sourceW4ZAdequacyReceipt` | Exact W4 adequacy receipt name, path, digest, or authority trace id |
| `sourceW4AdequacyReceiptName` | Stable name for the accepted source W4 adequacy artifact |
| `Candidate256PhysicalCalibrationAuthorityToken` | External authority artifact that can inhabit the constructorless token boundary outside this repo |
| `unitCarrier` | Physical unit carrier; it must not be the current dimensionless `Nat` surrogate by itself |
| `scaleMap` | Calibration map `Nat -> unitCarrier` for Candidate256 surrogate scale values |
| `quotientScaleMap` | Calibration map `Candidate256QuotientClass -> unitCarrier` |
| `candidate256CalibrationConstant` | Calibrated Candidate256 constant in `unitCarrier` |
| `scaleMapFactorsThroughCandidate256Surrogate` | Factorization proof that `quotientScaleMap q == scaleMap (candidate256SurrogateScale q)` |
| `dimensionalPreservationLaw` | Law family over `QuotientLawAtWitness canonicalCandidate256QuotientLaw -> Set` |
| `dimensionalPreservationAtWitness` | Inhabitant of the preservation law for every Candidate256 quotient-law witness |
| `externalAuthorityCitation` | DOI, publication, provider document, review record, artifact id, or other source citation for the authority boundary |
| `validationPayload` | Checksums, provenance, measurement inputs, review notes, commands/API calls, timestamps, and any reproducibility data needed for later validation |
| `externalAuthorityBoundary` | Boundary statement tying the authority artifact to Candidate256 physical calibration and naming what it does not certify |

## Accepted Response Shape

Only a real external accepted response may use this packet shape:

```json
{
  "status": "accepted-after-W4",
  "provider_name": "",
  "provider_role": "",
  "sourceW4ZAdequacyReceipt": "",
  "sourceW4AdequacyReceiptName": "",
  "Candidate256PhysicalCalibrationAuthorityToken": "",
  "unitCarrier": "",
  "scaleMap": "",
  "quotientScaleMap": "",
  "candidate256CalibrationConstant": "",
  "scaleMapFactorsThroughCandidate256Surrogate": "",
  "dimensionalPreservationLaw": "",
  "dimensionalPreservationAtWitness": "",
  "externalAuthorityCitation": "",
  "validationPayload": [],
  "externalAuthorityBoundary": []
}
```

The empty strings and empty arrays above are shape placeholders only. They are
not authority, calibration, validation, or token evidence. A real accepted
response must replace every placeholder with provider-supplied content.

## Rejected Response Shape

Use this form when the provider rejects the request or rejects the named source
W4 adequacy receipt:

```json
{
  "status": "rejected",
  "provider_name": "",
  "provider_role": "",
  "sourceW4ZAdequacyReceipt": "",
  "rejection_reason": "",
  "invalid_or_missing_fields": [],
  "externalAuthorityCitation": "",
  "externalAuthorityBoundary": [
    "No Candidate256 physical calibration authority is accepted here."
  ]
}
```

## Insufficient Response Shape

Use this form when the provider cannot answer authoritatively, W4 adequacy is
not yet accepted, or the response lacks required calibration fields:

```json
{
  "status": "insufficient",
  "provider_name": "",
  "provider_role": "insufficient",
  "sourceW4ZAdequacyReceipt": "",
  "missing_fields": [],
  "insufficient_reason": "",
  "externalAuthorityCitation": "",
  "externalAuthorityBoundary": [
    "No Candidate256 physical calibration authority is supplied."
  ]
}
```

`insufficient` preserves the blocker. It must not be rewritten as partial
acceptance.

## Stop Conditions

Stop intake and leave Candidate256 physical calibration unpromoted when any of
these conditions holds:

- `W4ZAdequacyReceipt` is missing, failed, incomplete, or only templated.
- `status` is `rejected` or `insufficient`.
- Any required accepted field is missing, empty, placeholder-only, or supplied
  only as prose without an authority artifact.
- The provider asks DASHI to infer, repair, tune, or fabricate the authority
  token locally.
- `unitCarrier` is only the current dimensionless `Nat` surrogate.
- `scaleMap`, `quotientScaleMap`, or the factorization proof is absent.
- `candidate256CalibrationConstant` is absent or not expressed in
  `unitCarrier`.
- The dimensional preservation law or its witness inhabitant is absent.
- The validation payload lacks reproducible provenance, checksums, citation, or
  review boundary.

## No-Promotion Guard

This request cannot inhabit
`Candidate256PhysicalCalibrationExternalReceipt`. It only names the provider
payload needed after W4 adequacy exists.

This document does not:

```text
construct AcceptedDYLuminosityConventionAuthority
construct W4ZAdequacyReceipt
construct Candidate256PhysicalCalibrationAuthorityToken
construct Candidate256PhysicalCalibrationExternalReceipt
promote the Nat surrogate to a physical unit carrier
claim Candidate256 physical calibration
construct matterFieldFromW4
construct stressEnergyTensorFromW4
promote W4, GR, or limited SM/QFT+GR closure
```

## Local Typed Surfaces

The local non-promoting surfaces that mirror this request are:

```text
DASHI/Physics/Closure/Candidate256PhysicalCalibrationExternalReceipt.agda
DASHI/Physics/Closure/W4PhysicalCalibrationExternalReceiptRequestPack.agda
DASHI/Physics/Closure/W4PhysicalCalibrationExternalReceiptObligation.agda
DASHI/Physics/Closure/W4ZAdequacyReceipt.agda
```

They expose the receipt shape and impossibility boundaries only. They do not
construct the external authority token or any promoted calibration receipt.
