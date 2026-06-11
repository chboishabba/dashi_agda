# Einstein Candidate Interface Patch Plan

Date: 2026-05-06
Worker: Gauss-Noether
Source audit: `Docs/W4MatterStressEnergyCompatibilityAudit.md`

## Scope

This plan records the minimal interface patch needed to connect the current
W4 matter/stress-energy preflight surface to the theorem-facing Einstein
candidate queue. It is a patch plan only. It does not promote GR, does not
construct matter or stress-energy, and does not claim a non-flat sourced
Einstein equation.

## Patch Matrix

| Exact missing import or field | Expected source module | Target consumer field | Patch type | No-promotion guard |
| --- | --- | --- | --- | --- |
| `import DASHI.Physics.Closure.EinsteinEquationCandidate as Einstein` | `DASHI.Physics.Closure.EinsteinEquationCandidate` | Standalone adapter module or future receipt bridge that targets `Einstein.W4MatterStressEnergyInterfaceReceipt` | adapter | Importing the theorem-facing shape must not construct `Einstein.W4MatterStressEnergyInterfaceReceipt`; keep `Einstein.w4MatterStressEnergyInterfaceReceiptImpossibleHere` in scope as the guard. |
| `w4AnchorReceipt : W4SameRecordZPeakT21T22ArtifactReceiptRequest` | `DASHI.Physics.Closure.W4CalibrationRatioZPeakReceiptRequestSurface` | `Einstein.W4MatterStressEnergyInterfaceReceipt.w4AnchorReceipt` | theorem-bearing | A W4 anchor receipt is an input prerequisite only; absence keeps `missingW4AnchorArtifactReceiptForMatterStress` first in `Einstein.canonicalW4MatterStressEnergyInterfaceMissingFields`. |
| `w4CalibrationAuthorityReceipt : Candidate256PhysicalCalibrationExternalReceipt` | `DASHI.Physics.Closure.W4PhysicalCalibrationExternalReceiptObligation` | `Einstein.W4MatterStressEnergyInterfaceReceipt.w4CalibrationAuthorityReceipt` | theorem-bearing | Must remain blocked by `candidate256PhysicalCalibrationExternalReceiptImpossibleHere`; no W4 matter/stress-energy promotion without Candidate256 authority. |
| `mergedW4W5ExternalPDFIntake : W5PDFCarrierExternalIntakeRequest` | `DASHI.Physics.Closure.W5PDFCarrierExternalIntakeRequest` | `Einstein.W4MatterStressEnergyInterfaceReceipt.mergedW4W5ExternalPDFIntake` | adapter | PDF intake is a shared dependency, not GR evidence; it must not bypass Candidate256 or accepted DY/PDF-backed adequacy. |
| `acceptedDYLuminosityConvention : AcceptedDYLuminosityConvention` | `DASHI.Physics.Closure.W4PhysicalCalibrationObligationSurface` | `Einstein.W4MatterStressEnergyInterfaceReceipt.acceptedDYLuminosityConvention` | theorem-bearing | Convention acceptance is a prerequisite to W4 adequacy only; no `AcceptedDYPDFBackedW4Adequacy` is implied. |
| `acceptedDYPDFBackedW4Adequacy : AcceptedDYPDFBackedW4Adequacy` | `DASHI.Physics.Closure.EinsteinEquationCandidate` | `Einstein.W4MatterStressEnergyInterfaceReceipt.acceptedDYPDFBackedW4Adequacy` | theorem-bearing | Must remain blocked by `acceptedDYPDFBackedW4AdequacyImpossibleHere`; no GR source term can be consumed without this receipt. |
| Rename/align `T_mu_nu : MatterField -> Set` with `StressEnergyTensor : MatterField -> Set` | `DASHI.Physics.Closure.W4MatterStressEnergyInterfaceReceipt.W4MatterStressEnergyPreflightSurface` | `Einstein.W4MatterStressEnergyInterfaceReceipt.StressEnergyTensor` | definitional | This is only a naming/shape adapter; it must not create a stress-energy value or a law. |
| Lift `matterFieldFromW4 : Candidate256PhysicalCalibrationExternalReceipt -> MatterField` to the full five-argument receipt tuple | `DASHI.Physics.Closure.W4MatterStressEnergyInterfaceReceipt.W4MatterStressEnergyPreflightSurface` plus W4/W5/DY receipt sources above | `Einstein.W4MatterStressEnergyInterfaceReceipt.matterFieldFromW4` | adapter | The adapter can only re-express dependencies; it must require anchor, Candidate256, W4/W5 PDF intake, DY convention, and DY/PDF-backed adequacy before producing `MatterField`. |
| Lift `stressEnergyTensorFromW4 : (matter : MatterField) -> T_mu_nu matter` to the full receipt tuple plus definitional matter equality | `DASHI.Physics.Closure.W4MatterStressEnergyInterfaceReceipt.W4MatterStressEnergyPreflightSurface` plus `Agda.Builtin.Equality` | `Einstein.W4MatterStressEnergyInterfaceReceipt.stressEnergyTensorFromW4` | adapter | The adapter must require the `matter ≡ matterFieldFromW4 ...` witness; it must not supply an independent stress-energy tensor. |
| `matterFieldUsesReceiptFields` reflexivity witness | `Agda.Builtin.Equality` and `DASHI.Physics.Closure.EinsteinEquationCandidate` | `Einstein.W4MatterStressEnergyInterfaceReceipt.matterFieldUsesReceiptFields` | definitional | `refl`-level bookkeeping only; no new matter field or physical calibration receipt is introduced. |
| `stressEnergyTensorUsesW4MatterField` reflexivity witness | `Agda.Builtin.Equality` and `DASHI.Physics.Closure.EinsteinEquationCandidate` | `Einstein.W4MatterStressEnergyInterfaceReceipt.stressEnergyTensorUsesW4MatterField` | definitional | `refl`-level bookkeeping only; no Einstein equation law is introduced. |
| `W4StressEnergyConsumerCarrier receipt` construction from the theorem-facing receipt | `DASHI.Physics.Closure.EinsteinEquationCandidate` | `Einstein.W4DiscreteGREquationLawObligation.einsteinEquationConsumer` input | theorem-bearing | Consumer carrier construction is blocked until `Einstein.W4MatterStressEnergyInterfaceReceipt` exists; no standalone preflight value may be treated as this carrier. |
| `curvatureCarrier`, `einsteinEquationCarrier`, `einsteinEquationConsumer`, `grEquationLaw`, and `grEquationLawAtConsumer` | future theorem module downstream of `DASHI.Physics.Closure.EinsteinEquationCandidate` | `Einstein.W4DiscreteGREquationLawObligation` fields | theorem-bearing | These fields are the GR law obligation itself; they cannot be supplied by the W4 preflight surface or compatibility audit. |
| Optional bridge to `GRQFTDownstreamConsumerFields.stressEnergyCarrier` | `DASHI.Physics.Closure.GRQFTConsumerNextObligation` | `GRQFTDownstreamConsumerFields.stressEnergyCarrier` and `einsteinEquationConsumer` | adapter/theorem-bearing | Bridge must not construct `GRQFTClosurePromotionReceipt`; keep `GRQFTClosurePromotionAuthorityToken` constructorless and require empirical GRQFT validation before promotion. |

## Ordered Patch Route

1. Create a small adapter surface only after the W4 anchor, Candidate256
   external calibration receipt, merged W4/W5 PDF intake, accepted DY
   convention, and accepted DY/PDF-backed W4 adequacy are available.
2. Map the standalone preflight names into the theorem-facing names:
   `T_mu_nu` becomes `StressEnergyTensor`, and the two functions are lifted
   from Candidate256-only inputs to the full W4/W5/DY receipt tuple.
3. Populate only definitional equality witnesses with `refl` when the lifted
   functions are definitionally the same receipt-field applications.
4. Only after `Einstein.W4MatterStressEnergyInterfaceReceipt` is inhabited,
   construct `Einstein.W4StressEnergyConsumerCarrier`.
5. Treat `Einstein.W4DiscreteGREquationLawObligation` and any
   `GRQFTDownstreamConsumerFields` bridge as separate theorem-bearing work.

## No-Promotion Guard

The patch may align interfaces, but it must preserve all current blockers:

- `Candidate256PhysicalCalibrationExternalReceipt` is impossible here.
- `Einstein.AcceptedDYPDFBackedW4Adequacy` is impossible here.
- `Einstein.W4MatterStressEnergyInterfaceReceipt` is impossible here.
- `Einstein.W4DiscreteGREquationLawObligation` is not supplied by this plan.
- `GRQFTClosurePromotionAuthorityToken` remains constructorless.
- No `GRQFTClosurePromotionReceipt` or
  `LimitedSMQFTGRPromotionPrerequisiteGate` is constructed.

Allowed claim: the W4 matter/stress-energy preflight contract can be adapted to
the theorem-facing Einstein candidate interface after the named external
receipts exist.

Forbidden claim: DASHI has constructed `MatterField`, `T_mu_nu`, a sourced
non-flat connection, `G_mu_nu = 8pi T_mu_nu`, GR recovery, GRQFT closure, or a
limited SM/QFT+GR promotion.
