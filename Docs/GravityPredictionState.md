# Gravity Prediction State

Status: documentation artifact; fail-closed; no Agda edited.

This note defines the minimum surface that would be prediction-capable for a
gravity lane. It does not claim that DASHI currently derives gravity
predictions. In the current repo, weak-field GR may be used only as an
external baseline authority, while DASHI staging remains receipt-gated and
non-promoting.

## Minimum Prediction-Capable Surface

A gravity prediction is admissible only when the following packet is present:

1. Baseline model: a standard weak-field GR prediction formula selected from an
   external GR authority, with regime assumptions recorded.
2. Inputs: mass/source distribution, distance/geometry, units, uncertainty
   model, and observation protocol.
3. Calibration: physical unit authority, gravitational normalization where
   `G_N` or equivalent scale appears, and source/stress-energy calibration.
4. Projection: a frozen prediction artifact produced before empirical
   comparison.
5. Comparison: an authority-backed observation artifact, uncertainty handling,
   and a receipt that states pass/fail without promoting broader GR closure.

Absent any field above, the lane must report `insufficientAuthority` or the
local equivalent and must not emit a carrier-derived physical prediction.

## External GR Authority

The baseline GR authority is external. Local receipt names to cite:

- `canonicalWaldGRAuthorityReceipt`
- `waldGRAuthorityContinuumLeviCivitaStillFailClosed`
- `waldGRAuthorityContinuumSourcedEinsteinStillFailClosed`
- `canonicalFriedmannInstabilitySaddleReceipt`
- `friedmannInstabilityDoesNotRemoveDarkEnergyHere`
- `friedmannInstabilityDoesNotFalsifyLCDMHere`

These receipts record authority boundaries and fail-closed non-claims. They do
not construct a DASHI continuum Levi-Civita theorem, sourced Einstein theorem,
cosmology model comparison, dark-energy conclusion, or LCDM falsification.

## DASHI-Staged Surface

The DASHI side is currently staging and bridge vocabulary, not prediction
authority. Local receipt or theorem names to cite:

- `canonicalKnownLimitsGRBridgeTheorem`
- `canonicalGRFirstOrderGravityScope`
- `canonicalGRDiscreteBianchiFiniteRUnsupportedClaims`
- `unsupportedGRQFTPromotionClaim`
- `EinsteinEquationCandidate.W4MatterStressEnergyInterfaceReceipt`
- `W4MatterStressEnergyPreflightSurface`
- `Candidate256PhysicalCalibrationExternalReceipt`
- `Candidate256PhysicalCalibrationAuthorityToken`

The known-limits bridge records a bounded GR-like recovery surface. The
first-order scope records route obligations for vierbein, spin connection,
curvature two-form, BF/MacDowell-Mansouri action presentation, coupling
normalization, sourced Einstein consumer, and G6 spine preservation. The W4 and
Candidate256 names mark the missing physical matter/source calibration needed
before sourced predictions.

## Weak-Field Baseline Predictions

For baseline-only work, the allowed wording is:

> Compare a DASHI-staged candidate against an externally supplied weak-field GR
> baseline.

The forbidden wording is:

> DASHI predicts gravity, derives Newtonian gravity, derives Schwarzschild, or
> derives sourced GR.

Examples of weak-field baseline quantities that may be cited only as external
GR predictions are Newtonian potential/acceleration, perihelion correction,
light deflection, time dilation/redshift, and Shapiro delay. To become a DASHI
prediction, each would need a frozen DASHI projection receipt plus the
calibration/source receipts above.

## Current Blockers Before Carrier-Derived Predictions

The live blockers are:

- `missingCarrierConnectionIsLeviCivita`
- `missingCurvatureToRicciContraction`
- `missingFiniteRBianchiWitness`
- `missingDiscreteEinsteinTensorLaw`
- `missingW4MatterStressEnergyInterfaceReceipt`
- `missingMetricErrorBound`
- `missingConnectionErrorBound`
- `missingWeakFieldNewtonianPotential`
- `missingW4MassSource`
- `missingSchwarzschildMetricMatch`
- `missingEinsteinTensorContinuity`
- `missingW2BridgeOrObstructionResolution`
- `missingW4AnchorArtifactReceiptForMatterStress`
- `missingCandidate256CalibrationReceiptForMatterInterface`
- `firstMissingGRQFTClosurePromotionAuthorityToken`

Until these are discharged by exact receipts, the gravity prediction lane is a
comparison-and-staging lane only. It can cite external GR baselines, collect
inputs, and freeze candidate artifacts, but it cannot promote carrier-derived
physical gravity predictions.
