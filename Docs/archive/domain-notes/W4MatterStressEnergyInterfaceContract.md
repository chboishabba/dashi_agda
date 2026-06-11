# W4 Matter / Stress-Energy Interface Contract

This is a human-facing contract for the W4 matter and stress-energy handoff.
It is a pre-GR interface surface, not a GR promotion, QFT promotion, GR/QFT
promotion, or stress-energy promotion receipt.

## Formal Model

O:
The owned surfaces for this lane are this document and
`DASHI.Physics.Closure.W4MatterStressEnergyInterfaceReceipt`. Upstream W4
calibration remains owned by the Candidate256 physical calibration lane.

R:
State exactly what Candidate256 physical calibration must provide before
`matterFieldFromW4` and `stressEnergyTensorFromW4` are admissible.

C:
The consumable contract is:

```agda
matterFieldFromW4 :
  Candidate256PhysicalCalibrationExternalReceipt ->
  MatterField

stressEnergyTensorFromW4 :
  MatterField ->
  T_mu_nu
```

The required receipt is:

```agda
DASHI.Physics.Closure.W4PhysicalCalibrationExternalReceiptObligation.Candidate256PhysicalCalibrationExternalReceipt
```

S:
`EinsteinEquationCandidate.agda` already blocks the downstream Einstein
equation path on W4 anchor, calibration authority, accepted adequacy, matter
field, and stress-energy tensor. The narrower W4 contract here isolates the
Candidate256 calibration preflight needed before W4 matter or stress-energy can
be treated as available.

L:
The ordered path is:

```text
Candidate256 physical calibration receipt
-> MatterField
-> T_mu_nu
-> discrete Einstein law obligation
```

This lane stops before `grEquationLaw`.

P:
Expose a typed preflight surface that accepts only
`Candidate256PhysicalCalibrationExternalReceipt` as the W4 calibration input,
then names the target matter and stress-energy shapes. The surface also carries
the guard:

```text
not Candidate256PhysicalCalibrationExternalReceipt
-> not W4MatterStressEnergyPromotion
```

G:
No GR law, no QFT law, no GR/QFT promotion, and no stress-energy promotion may
be claimed from this contract. A stress-energy promotion requires an actual
Candidate256 physical calibration receipt first; labels, diagnostics, anchor
names, provider attempts, and Nat surrogate values are not substitutes.

F:
The exact remaining gap is the missing
`Candidate256PhysicalCalibrationExternalReceipt`.

## Candidate256 Calibration Must Provide

A valid Candidate256 physical calibration receipt must carry the fields already
specified by
`W4PhysicalCalibrationExternalReceiptObligation.Candidate256PhysicalCalibrationExternalReceipt`:

- `calibrationAuthority : Candidate256PhysicalCalibrationAuthorityToken`
- `physicalUnitCarrier : Set`
- `natToUnitCalibrationMap : Nat -> physicalUnitCarrier`
- `calibratedQuotientScaleMap : Candidate256QuotientClass -> physicalUnitCarrier`
- factorization through `candidate256SurrogateScale`
- dimensional-preservation law and witnesses for the Candidate256 quotient law
- labels for the unit carrier, calibration map, quotient-scale map,
  factorization, and dimensional-preservation boundary

Until that receipt exists, this contract records only the interface shape and
the blocker.

## Non-Promotion Boundary

This contract does not:

- construct `Candidate256PhysicalCalibrationExternalReceipt`
- construct `MatterField`
- construct `T_mu_nu`
- construct `W4MatterStressEnergyPromotion`
- define or call `grEquationLaw`
- promote GR, QFT, GR/QFT, W4, or W5

