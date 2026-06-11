# W4 Matter / Stress-Energy Compatibility Audit

Date: 2026-05-06
Worker: Gauss
Lane: W4 matter/stress-energy compatibility audit

## Conclusion

Status: **preflight-compatible, not directly inhabitable**.

The current W4 matter/stress-energy surfaces are aligned with the Einstein
candidate and GRQFT consumer queues, so no large type redesign is indicated.
However, the standalone
`DASHI.Physics.Closure.W4MatterStressEnergyInterfaceReceipt` module cannot
directly feed the current Einstein candidate as-is. It is a minimal preflight
contract gated only on `Candidate256PhysicalCalibrationExternalReceipt`, while
`DASHI.Physics.Closure.EinsteinEquationCandidate.W4MatterStressEnergyInterfaceReceipt`
is the theorem-facing receipt and requires the full W4/W5/DY adequacy tuple.

Compatibility class: **syntactic/preflight compatibility**. The interfaces use
abstract carriers and string/governance boundaries; no mathematical stress-energy
law, non-flat connection, Einstein equation, GR recovery theorem, or GRQFT
promotion is constructed.

## Required Imports

The standalone preflight surface currently imports:

- `DASHI.Physics.Closure.W4PhysicalCalibrationExternalReceiptObligation`

The Einstein candidate matter/stress-energy receipt currently imports or
depends on:

- `DASHI.Physics.Closure.DiscreteEinsteinTensorCandidate`
- `DASHI.Physics.Closure.W4CalibrationRatioZPeakReceiptRequestSurface`
- `DASHI.Physics.Closure.W4PhysicalCalibrationExternalReceiptObligation`
- `DASHI.Physics.Closure.W4PhysicalCalibrationObligationSurface`
- `DASHI.Physics.Closure.W5PDFCarrierExternalIntakeRequest`

The GRQFT consumer surface currently imports or depends on:

- `DASHI.Physics.Closure.KnownLimitsGRBridgeTheorem`
- `DASHI.Physics.Closure.KnownLimitsInterpretableObservableConsumer`
- `DASHI.Physics.Closure.KnownLimitsQFTBridgeTheorem`
- `DASHI.Physics.Closure.KnownLimitsStatus`
- `DASHI.Physics.Closure.PDFCarrierLogRatioDiagnostic`
- `DASHI.Physics.Closure.W5PDFCarrierExternalIntakeRequest`

## Field Compatibility

### Standalone W4 Preflight Surface

`W4MatterStressEnergyPreflightSurface` provides:

- `MatterField : Set`
- `T_mu_nu : MatterField -> Set`
- `matterFieldFromW4 : Candidate256PhysicalCalibrationExternalReceipt -> MatterField`
- `stressEnergyTensorFromW4 : (matter : MatterField) -> T_mu_nu matter`
- `preflightBoundary : List String`

This is intentionally minimal. It is sufficient to record the intended
post-calibration shape, but it does not carry the W4 anchor, PDF intake, DY
convention, or W4 adequacy evidence required by the current Einstein candidate.

### Einstein Candidate Receipt

`EinsteinEquationCandidate.W4MatterStressEnergyInterfaceReceipt` requires:

- `w4AnchorReceipt`
- `w4CalibrationAuthorityReceipt`
- `mergedW4W5ExternalPDFIntake`
- `acceptedDYLuminosityConvention`
- `acceptedDYPDFBackedW4Adequacy`
- `MatterField`
- `StressEnergyTensor`
- `matterFieldFromW4` consuming all W4/W5/DY prerequisites
- `stressEnergyTensorFromW4` consuming the same prerequisites and a matter field
  definitionally tied to `matterFieldFromW4`
- `interfaceBoundary`

This is the correct receipt for the current Einstein candidate. It can feed
`W4StressEnergyConsumerCarrier` and then
`W4DiscreteGREquationLawObligation`, but it is impossible in the current repo
because `Candidate256PhysicalCalibrationExternalReceipt` and
`AcceptedDYPDFBackedW4Adequacy` are both impossible here.

### GRQFT Consumer Surface

`GRQFTDownstreamConsumerFields` does not consume W4 stress-energy directly. It
expects generic downstream carriers and maps:

- `spacetimeCarrier`
- `stressEnergyCarrier`
- `curvatureCarrier`
- `einsteinEquationCarrier`
- `stressEnergyMap : spacetimeCarrier -> stressEnergyCarrier`
- `curvatureMap : spacetimeCarrier -> curvatureCarrier`
- `einsteinEquationConsumer : stressEnergyCarrier -> curvatureCarrier -> einsteinEquationCarrier`

Therefore, a later bridge must map a W4 stress-energy carrier into
`GRQFTDownstreamConsumerFields.stressEnergyCarrier`. That bridge is not present
today. This is an adapter/theorem obligation, not evidence of a needed redesign.

## Field Mismatches

Direct mismatch:

- Standalone `W4MatterStressEnergyPreflightSurface.matterFieldFromW4` consumes
  only `Candidate256PhysicalCalibrationExternalReceipt`.
- Einstein candidate `matterFieldFromW4` consumes W4 anchor, Candidate256
  calibration, merged W4/W5 PDF intake, accepted DY convention, and accepted
  DY/PDF-backed W4 adequacy.

Naming mismatch:

- Standalone surface uses `T_mu_nu`.
- Einstein candidate uses `StressEnergyTensor`.
- This is only a naming/shape difference because both are `MatterField -> Set`.

Carrier mismatch:

- Einstein candidate wraps matter and stress-energy in
  `W4StressEnergyConsumerCarrier`.
- GRQFT downstream fields require generic `stressEnergyCarrier` and
  `einsteinEquationCarrier`.
- A later adapter must identify the W4 carrier with the GRQFT downstream carrier
  or provide a map between them.

Authority mismatch:

- Both W4 surfaces ultimately depend on
  `Candidate256PhysicalCalibrationExternalReceipt`.
- The current repo proves that receipt impossible here because its
  `Candidate256PhysicalCalibrationAuthorityToken` is constructorless.
- Einstein candidate additionally blocks on accepted DY/PDF-backed W4 adequacy,
  which is also impossible here.

## Downstream Theorem Obligations

The minimum downstream obligations are:

1. Inhabit `AcceptedDYLuminosityConventionAuthority` outside the current local
   diagnostic boundary.
2. Produce `W4ZAdequacyReceipt` under that accepted convention.
3. Inhabit `Candidate256PhysicalCalibrationExternalReceipt` with external
   authority, physical unit carrier, calibration map, factorization law, and
   dimensional preservation.
4. Inhabit the theorem-facing
   `EinsteinEquationCandidate.W4MatterStressEnergyInterfaceReceipt`.
5. Build `W4StressEnergyConsumerCarrier` from that receipt.
6. Provide a curvature carrier and `einsteinEquationConsumer`.
7. Prove `grEquationLawAtConsumer` for
   `W4DiscreteGREquationLawObligation`.
8. If promoting into GRQFT closure, provide `GRQFTDownstreamConsumerFields`
   that consume the same stress-energy/curvature laws.
9. Provide `qftInteractionLaw`, `qftInteractionLawAtConsumer`, and
   `EmpiricalGRQFTValidationReceipt` tied to the same downstream fields.
10. Provide `GRQFTClosurePromotionAuthorityToken` and the full
    `GRQFTClosurePromotionReceipt`.

## No-Promotion Guard

No GR promotion is available from the current W4 matter/stress-energy surfaces.

The current repo explicitly preserves these guards:

- `Candidate256PhysicalCalibrationExternalReceipt` is impossible here.
- `W4MatterStressEnergyPromotion` is impossible without Candidate256.
- `EinsteinEquationCandidate.W4MatterStressEnergyInterfaceReceipt` is impossible
  here through the Candidate256 authority boundary.
- The same receipt is impossible without accepted DY/PDF-backed W4 adequacy.
- `GRQFTClosurePromotionReceipt` is impossible here because
  `GRQFTClosurePromotionAuthorityToken` is constructorless.
- `LimitedSMQFTGRPromotionPrerequisiteGate` is impossible for the same authority
  reason.

Therefore the only supported claim is:

> The W4 matter/stress-energy lane is structurally prepared for a later
> Einstein-equation consumer once W4 authority, accepted DY/PDF-backed adequacy,
> Candidate256 physical calibration, matter, and stress-energy are supplied.

Forbidden claims:

- DASHI has constructed a W4 matter field.
- DASHI has constructed `T_mu_nu`.
- DASHI has proved `G_mu_nu = 8pi T_mu_nu`.
- DASHI has a non-flat sourced GR recovery theorem.
- DASHI has a GRQFT closure-promotion receipt.
- DASHI has a limited SM/QFT+GR promotion gate.

## Practical Next Step

No type redesign is required now. The next implementation step after W4
calibration lands should be a small adapter or receipt that populates the
theorem-facing
`EinsteinEquationCandidate.W4MatterStressEnergyInterfaceReceipt`, not another
abstract preflight surface.
