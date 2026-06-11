# Candidate256 Calibration Dependency Audit

Date: `2026-05-06`
Owner: `Kelvin`
Status: `not ready; non-promoting`

## Question

If W4 adequacy lands tomorrow, do we have every field needed to inhabit
`Candidate256PhysicalCalibrationExternalReceipt`?

## Conclusion

No. W4 adequacy is necessary but not sufficient.

The current dependency chain is:

```text
AcceptedDYLuminosityConventionAuthority
  -> W4ZAdequacyReceipt
  -> Candidate256PhysicalCalibrationExternalReceipt
  -> W4External.Candidate256PhysicalCalibrationExternalReceipt
  -> physical scale-setting lane
```

The Candidate256 receipt still requires an external physical-calibration
authority artifact and concrete calibration fields after W4 adequacy exists.
The local repo has the request/adapter surface, but not the positive receipt.

## Local Evidence

`DASHI/Physics/Closure/Candidate256PhysicalCalibrationExternalReceipt.agda`
defines the preflight dependency skeleton as
`AcceptedDYLuminosityConventionAuthority -> W4ZAdequacyReceipt ->
Candidate256PhysicalCalibrationExternalReceipt` at lines 22-24. It also states
that none of those positive dependencies are constructed in-repo at lines
26-29.

The receipt fields are explicit at
`DASHI/Physics/Closure/Candidate256PhysicalCalibrationExternalReceipt.agda:63`:

| Field | Status if W4 adequacy lands tomorrow | Exact source required |
|---|---|---|
| `acceptedDYLuminosityConventionAuthority` | Still required as an inhabited authority value | Provider response accepted into `AcceptedDYLuminosityConventionAuthorityReceipt`; local constructor is empty at lines 35-40. |
| `sourceW4ZAdequacyReceipt` | Could be supplied only after W4 adequacy is computed and typed | `DASHI/Physics/Closure/W4ZAdequacyReceipt.agda`; the receipt requires accepted authority at lines 144-178. |
| `candidate256PhysicalCalibrationAuthority` | Missing even if W4 adequacy lands | External artifact inhabiting `Gate.Candidate256PhysicalCalibrationAuthorityToken`; token has no constructor at `W4PhysicalCalibrationGate.agda:28`. |
| `unitCarrier` | Missing | External physical unit carrier, not the current dimensionless `Nat` surrogate; required at lines 74-79 and in template lines 24-27. |
| `scaleMap` | Missing | External map `Nat -> unitCarrier`; required at lines 77-79. |
| `quotientScaleMap` | Missing | External map `Candidate256QuotientClass -> unitCarrier`; required at lines 81-83. |
| `candidate256CalibrationConstant` | Missing | External calibrated Candidate256 constant in `unitCarrier`; required at lines 85-86. |
| `scaleMapFactorsThroughCandidate256Surrogate` | Missing | Proof that the quotient map factors through `candidate256SurrogateScale`; required at lines 88-92. |
| `dimensionalPreservationLaw` | Missing | Law family over `canonicalCandidate256QuotientLaw`; required at lines 94-97. |
| `dimensionalPreservationAtWitness` | Missing | Inhabitant of the preservation law for every quotient-law witness; required at lines 99-103. |
| `externalAuthorityCitation` | Missing | Citation for the external physical calibration authority; required at lines 105-106. |
| `validationPayload` | Missing | Checksum/provenance/measurement payload sufficient for later validation; required at lines 108-109. |
| `sourceW4AdequacyReceiptName` | Missing until W4 adequacy receipt exists | Name/digest of the actual W4 adequacy receipt; required at lines 111-112. |
| `externalAuthorityBoundary` | Missing until provider response is available | Boundary text tying the authority artifact to the external receipt; required at lines 114-115. |

The adapter to the older W4 external receipt shape exists at
`Candidate256PhysicalCalibrationExternalReceipt.agda:125`. That adapter is
useful, but it consumes a positive Candidate256 receipt; it does not construct
one.

## W4 Adequacy Dependency

`DASHI/Physics/Closure/W4ZAdequacyReceipt.agda` is also gated. Its local
status is `blockedAwaitingAcceptedDYLuminosityConventionAuthority` at lines
232-239. It requires:

```text
accepted DY authority
real m_i measurement vector
real d_i dirty Z-peak shape prediction vector
accepted ell_i Drell-Yan luminosity vector
real sigma_i per-bin uncertainty vector
typed adequacy threshold/review
```

The W4 adequacy template records that it does not construct
`Candidate256PhysicalCalibrationAuthorityToken` and does not promote W4 at
lines 260-276.

## Mismatches

No hard type mismatch was found between the new preflight surface and the older
W4 external receipt shape. The mapping in
`candidate256ReceiptToW4ExternalReceipt` covers:

```text
calibrationAuthority
physicalUnitCarrier
natToUnitCalibrationMap
calibratedQuotientScaleMap
factorization law
dimensional preservation law
dimensional preservation witness
labels
```

The mismatch is evidential, not structural: the fields are named, but most are
not inhabited.

The strongest blocker is the authority token boundary. The existing W4 external
status says a legitimate receipt must carry an already-inhabited
`Candidate256PhysicalCalibrationAuthorityToken`, and that local diagnostics,
HEPData anchor names, Z-peak shape fits, CT18 probes, labels, and prose
provenance do not inhabit that token
(`W4PhysicalCalibrationExternalReceiptObligation.agda:257-262`).

## No-Promotion Guard

This audit does not:

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

The no-promotion boundary is consistent with:

- `Candidate256PhysicalCalibrationExternalReceipt.agda:274-279`
- `W4PhysicalCalibrationExternalReceiptObligation.agda:263-268`
- `W4PhysicalCalibrationObligationSurface.agda:293-300`

## Next Action

After W4 adequacy lands, request one provider payload that supplies:

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
sourceW4ZAdequacyReceipt digest/name
externalAuthorityBoundary
```

Until that payload is accepted, Candidate256 physical calibration is not ready.
