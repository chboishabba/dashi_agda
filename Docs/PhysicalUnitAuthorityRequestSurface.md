# Physical Unit Authority Request Surface

Date: `2026-05-13`
Owner: `Lane 3 chemistry/calibration authority / Lagrange+Fermat unified`
Status: `provider-facing request; non-promoting`

## Purpose

The Candidate256/TSFV trit calibration law is internally constructed in:

```text
DASHI.Physics.Closure.TSFVCandidate256CalibrationLawDiagnostic
```

That construction is still not W4 physical calibration. The remaining W4 gap is
external physical-unit authority: a physical unit carrier, base unit, dimension
carrier, conversion law, dimensional preservation statement, authority token,
and an external receipt that binds those fields to Candidate256/TSFV.

The unified W4 chemistry/TSFV lane names one shared provider obligation:

```text
TSFV.TSFVTritCalibrationLaw.baseUnit == W4PhysicalUnitAuthorityRequestSurface.requiredBaseUnit
```

In Agda this is now split into two levels:

- `baseUnitIsRequiredBaseUnit` / `baseUnitEqualsRequiredBaseUnit` are typed
  equality witnesses, currently `refl`, because the W4 request-level
  `requiredBaseUnit` witness is definitionally the TSFV trit calibration
  `baseUnit`.
- `W4PhysicalUnitAuthorityProviderRequest.requiredBaseUnit` remains a string
  naming the provider-facing obligation, not an authority-bearing unit.

This is not a proof of physical authority. It is the same missing external
base-unit obligation viewed from two sides: the chemistry/TSFV trit calibration
law and the W4 kill-matrix physical-calibration blocker.

This request surface asks a provider for exactly those fields. It does not
construct `Candidate256PhysicalCalibrationAuthorityToken`,
`Candidate256PhysicalCalibrationExternalReceipt`, W4 promotion, matter fields,
or stress-energy.

## Current Local State

Locally available:

| Surface | Local status |
|---|---|
| `TSFV.candidate256InternalTritCalibrationLaw` | Constructed internal diagnostic law |
| `quotientT` | Constructed as a total Candidate256 carrier involution |
| `integerAddress` | Constructed internally |
| `addressNegationCompatibility` | Constructed internally |
| `v3AddressDepth` calibration map | Constructed internally |
| `dimensionalInvarianceUnderT` | Constructed internally |
| `nontrivialSeparation` | Constructed internally for the canonical Candidate256 left/right witnesses |

Still external:

| Field | Status |
|---|---|
| `PhysicalUnitCarrier` | Missing external authority |
| `baseUnit` | Missing external authority |
| `DimensionCarrier` | Missing external authority |
| `dimensionOfUnit` | Missing external authority |
| conversion to SI or natural units | Missing external authority |
| dimensional preservation statement | Missing external authority |
| Candidate256/TSFV-to-W4 binding law | Missing external authority |
| `Candidate256PhysicalCalibrationAuthorityToken` | Constructorless locally |
| `Candidate256PhysicalCalibrationExternalReceipt` | Not constructed |

## Unified Base-Unit Bridge

The Agda bridge is:

```text
DASHI.Physics.Closure.W4PhysicalUnitAuthorityRequestSurface.canonicalW4TSFVPhysicalUnitAuthorityBridge
```

It records that the internal TSFV law field
`TSFV.TSFVTritCalibrationLaw.baseUnit` and the W4 request field
`W4PhysicalUnitAuthorityProviderRequest.requiredBaseUnit` are the same
provider-facing obligation. The bridge is diagnostic/request-level only: it
does not replace the internal diagnostic carrier with an external unit system
and it does not inhabit any W4 receipt.

## R-Chem Receipt Request Boundary

The conservative request skeleton is:

```text
DASHI.Physics.Closure.W4PhysicalUnitAuthorityRequestSurface.canonicalW4TSFVChemistryLawReceiptRequest
```

It records R-chem as an obligation over:

```text
Handoff.QuotientLawAtWitness Next.canonicalCandidate256QuotientLaw
```

R-chem is no longer an untyped placeholder. It is fixed in Agda as:

```text
DASHI.Physics.Closure.TSFVCandidate256CalibrationLawDiagnostic.Candidate256RchemRelationAtWitness
```

For a witness
`law : QuotientLawAtWitness Next.canonicalCandidate256QuotientLaw`, the
relation carries:

- the `L_chem` witness as the relation argument;
- TSFV compatibility, defined as preservation of the internal trit calibration
  under the Candidate256 involution `quotientT`;
- `nontrivialPositiveWitness`, the original Candidate256 left/right trit-scale
  separation;
- `nontrivialNegativeWitness`, the same non-collapse statement after applying
  `quotientT` to both sides.

The prior strict valuation-style witness attempt is therefore not promoted.
The adopted relation is the TSFV-invariant two-sided non-collapse relation. The
current request status is:

```text
providerChemistryLawReceiptRequiredBeforeSelection
```

That means no chemistry-law receipt is promoted from the current lane. A
provider still has to supply the witness selection rule, the chemistry-law
receipt/artifact, and the external physical-unit authority binding those
witnesses to the shared `baseUnit` / `requiredBaseUnit` obligation.

## Required Provider Payload

An accepted provider response must supply all of the following as typed or
artifact-backed content. Labels, prose, citations alone, and local diagnostics
are not enough.

| Required field | Required provider answer |
|---|---|
| `PhysicalUnitCarrier : Set` | The external physical unit carrier. It must not be only the current dimensionless `Nat` surrogate. |
| `baseUnit : PhysicalUnitCarrier` | The base physical unit used for Candidate256/TSFV calibration; this is the W4 `requiredBaseUnit` obligation. |
| `DimensionCarrier : Set` | The carrier for dimensions, e.g. SI base-dimension vectors or a named natural-unit dimension system. |
| `dimensionOfUnit : PhysicalUnitCarrier -> DimensionCarrier` | Function assigning dimensions to physical units. |
| `baseUnitDimension` | The declared dimension of `baseUnit`. |
| `conversionTarget` | SI unit target or explicitly named natural-unit convention. |
| `conversionLaw` | Law converting `baseUnit` and calibrated units to the conversion target. |
| `natToUnitCalibrationMap : Nat -> PhysicalUnitCarrier` | Unit calibration map for dimensionless internal scale values. |
| `calibratedQuotientScaleMap : Candidate256QuotientClass -> PhysicalUnitCarrier` | Physical-unit map over Candidate256 quotient classes. |
| `Candidate256TSFVBindingLaw` | Proof that `calibratedQuotientScaleMap q` agrees with the provider’s unit calibration of the internal TSFV trit value for `q`. |
| `calibratedScaleMapFactorsThroughNat` | If using the current W4 external receipt shape, proof that `calibratedQuotientScaleMap q == natToUnitCalibrationMap (candidate256SurrogateScale q)`. |
| `dimensionalPreservationLaw` | Law family over `QuotientLawAtWitness canonicalCandidate256QuotientLaw -> Set`. |
| `dimensionalPreservationAtWitness` | Inhabitant for every Candidate256 quotient-law witness. |
| `Candidate256PhysicalCalibrationAuthorityToken` | External authority artifact inhabiting the constructorless token boundary outside this repo. |
| `authorityCitation` | DOI, standards reference, provider document, review record, or artifact id. |
| `validationPayload` | Checksums, provenance, measurement inputs, commands/API calls, timestamps, and review boundary. |

## Accepted Response Shape

Only a real external accepted response may use this shape:

```json
{
  "status": "accepted",
  "provider_name": "",
  "provider_role": "",
  "PhysicalUnitCarrier": "",
  "baseUnit": "",
  "DimensionCarrier": "",
  "dimensionOfUnit": "",
  "baseUnitDimension": "",
  "conversionTarget": "",
  "conversionLaw": "",
  "natToUnitCalibrationMap": "",
  "calibratedQuotientScaleMap": "",
  "Candidate256TSFVBindingLaw": "",
  "calibratedScaleMapFactorsThroughNat": "",
  "dimensionalPreservationLaw": "",
  "dimensionalPreservationAtWitness": "",
  "Candidate256PhysicalCalibrationAuthorityToken": "",
  "authorityCitation": "",
  "validationPayload": [],
  "authorityBoundary": []
}
```

Empty values are placeholders only. A real accepted response must replace every
placeholder with provider-supplied authority content.

## Insufficient Or Rejected Response

Use this shape when any required field is missing:

```json
{
  "status": "insufficient",
  "provider_name": "",
  "missing_fields": [],
  "reason": "",
  "authorityBoundary": [
    "No Candidate256 physical-unit authority is supplied."
  ]
}
```

`insufficient` or `rejected` preserves the blocker.

## Rejected Substitutes

These do not satisfy the request:

- `TSFV.candidate256InternalTritCalibrationLaw` by itself.
- `TSFVDiagnosticPhysicalUnitCarrier` by itself.
- `TSFV.TSFVTritCalibrationLaw.baseUnit` by itself, because the current value
  is only the internal diagnostic base unit until a provider supplies the W4
  `requiredBaseUnit` payload.
- The dimensionless `Nat` surrogate by itself.
- Drosophila/codon candidate evidence without physical-unit authority.
- HEPData/Z-peak/PDF artifacts without unit authority and a typed binding law.
- Labels, citations, comments, or prose dimensional annotations without typed
  carrier, base unit, dimension, conversion, preservation, and token fields.

## Local Typed Surface

The matching non-promoting Agda request surface is:

```text
DASHI.Physics.Closure.W4PhysicalUnitAuthorityRequestSurface
```

It records the request and the exact missing fields only. It also imports the
current external receipt impossibility boundary, so this document cannot be
read as a receipt or authority-token construction.
