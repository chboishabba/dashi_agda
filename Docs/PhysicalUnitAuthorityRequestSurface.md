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
| provider-bound base-unit citation/checksum | Missing external authority |

## Candidate Base-Unit Routes

The request surface now exposes candidate routes for the shared `baseUnit`
obligation. These routes are provider-facing candidates only. They do not
select a base unit, construct physical authority, construct
`Candidate256PhysicalCalibrationAuthorityToken`, or promote W4.

The typed Agda surface is:

```text
DASHI.Physics.Closure.W4PhysicalUnitAuthorityRequestSurface.canonicalW4BaseUnitCandidateRoutes
```

Current candidate routes:

| Route | Candidate meaning | Required before acceptance |
|---|---|---|
| `protonMassCODATACandidate` | Use a proton-mass energy-equivalent as the W4 natural base-unit candidate. | Provider-bound value, uncertainty, unit convention, conversion target, immutable citation/checksum, and dimensional preservation binding. |
| `dyConventionNaturalUnitCandidate` | Inherit a base unit from an accepted DY luminosity/cross-section convention. | `AcceptedDYLuminosityConventionAuthorityReceipt` or replacement packet, normalisation preservation, conversion law, and statement that the selected DY base unit satisfies W4 physical-unit authority. |
| `providerSuppliedOtherBaseUnitCandidate` | Let the provider supply a replacement base unit. | Complete `PhysicalUnitCarrier`, `DimensionCarrier`, `dimensionOfUnit`, `conversionLaw`, `Candidate256TSFVBindingLaw`, and `dimensionalPreservationLaw`. |

The proton-mass/CODATA route is deliberately not written as an accepted
authority. A remembered value, DOI name, standards label, or prose citation is
insufficient. It becomes admissible only when the provider binds the exact
value, uncertainty, unit convention, conversion target, immutable citation or
checksum, and W4 dimensional-preservation statement.

Current value note: if the proton-mass candidate route is used, the provider
packet should bind the current CODATA 2022 proton mass energy equivalent:

```json
{
  "baseUnitName": "proton mass energy equivalent",
  "baseUnitValue": "938.27208943",
  "baseUnitUncertainty": "0.00000029",
  "baseUnitUnit": "MeV",
  "providerSource": "CODATA 2022"
}
```

Do not reuse the stale CODATA 2018 value `938.27208816` unless a compatibility
surface explicitly requires historical constants. This note is still
provider-facing and non-promoting; it does not choose the proton mass as W4
`baseUnit`.

Likewise, the DY route is not supplied by the local pressure decomposition
tool. The tool exiting `45` proves the opposite: attribution is blocked until
an accepted DY convention authority or replacement packet exists.

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

The quotient-sensitive witness is now exposed as a separate parameterized
surface:

```text
DASHI.Physics.Closure.W4PhysicalUnitAuthorityRequestSurface.canonicalW4QuotientSensitiveCrossBandWitnessSurface
```

It is parameterized by an existing:

```text
Handoff.QuotientLawAtWitness Next.canonicalCandidate256QuotientLaw
```

Given that witness, the surface records the internal `T` involution
`candidate256QuotientT`, its involution law, TSFV compatibility, the canonical
left/right non-collapse witness, and the `T`-flipped non-collapse witness. It
does not construct the `QuotientLawAtWitness`, a provider chemistry-law
receipt, a physical-unit authority token, or W4 promotion.

## Provider Receipt Surface

The provider response/receipt shape is now named in Agda as:

```text
DASHI.Physics.Closure.W4PhysicalUnitAuthorityRequestSurface.canonicalW4PhysicalUnitAuthorityProviderReceiptSurface
```

This is a receipt surface, not the external receipt itself. An accepted
provider response must bind the exact request it answers, the physical-unit
carrier/base-unit/dimension/conversion fields, provider-bound base-unit
citation/checksum/value/uncertainty, the Candidate256/TSFV binding law,
dimensional preservation, and an external
`Candidate256PhysicalCalibrationAuthorityToken` plus
`Candidate256PhysicalCalibrationExternalReceipt` payload. If the response
consumes the quotient-sensitive cross-band witness, it must also provide the
chemistry-law receipt and witness-selection rule.

An insufficient response preserves the blocker by naming missing typed fields.
The local surface keeps the same impossibility boundary: it does not construct
`Candidate256PhysicalCalibrationAuthorityToken`,
`Candidate256PhysicalCalibrationExternalReceipt`, or W4 promotion.

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
| provider-bound base-unit citation/checksum | Immutable citation, checksum, DOI/table/version, or replacement authority record for the chosen base unit. |
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
  "chosenBaseUnitCandidateRoute": "",
  "providerBoundBaseUnitCitation": "",
  "providerBoundBaseUnitChecksum": "",
  "providerBoundBaseUnitValue": "",
  "providerBoundBaseUnitUncertainty": "",
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
- Proton mass or CODATA named without provider-bound value, uncertainty, unit
  convention, checksum/citation, conversion law, and W4 dimensional
  preservation binding.
- DY luminosity or pressure-decomposition diagnostics without an accepted DY
  convention authority receipt or replacement packet.
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
