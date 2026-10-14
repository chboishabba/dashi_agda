{-# OPTIONS --safe #-}
module DASHI.Physics.ExoticGravity.AntigravityTerminalPhysicalPackageFrontierExact where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)

import DASHI.Physics.ExoticGravity.AntigravityPostNormalizationReuseMaxCutExact as Reuse
import DASHI.Physics.ExoticGravity.AntigravityDifferentialTTDonorMaxCutExact as TT
import DASHI.Physics.ExoticGravity.AntigravitySICalibrationDonorMaxCutExact as SI
import DASHI.Physics.ExoticGravity.AntigravityMatchedControlExperimentDonorMaxCutExact as Experiment

------------------------------------------------------------------------
-- TERMINAL PHYSICAL-PACKAGE FRONTIER
--
-- After the normalization-flow / Delta-V tranche and the current R136 reuse
-- compilers, the preferred source->response path should be scheduled by
-- PHYSICAL PACKAGES rather than by every field inside each package.
--
-- Mandatory for static and scalar differential response:
--
--   P1. one typed pinned Local-C terminal package
--       (same selected stress/vacuum, boost covariance, E->L trace);
--
--   P2. one common gravitational calibration/renormalization package
--       (affine source->rho map, cosmological convention, accepted kappa/G,
--        consumer-relevant stress*length^2 scale);
--
--   P3. one matched experimental package
--       (real controlled source switch, systematics budget, null/calibration,
--        preregistration and replication).
--
-- Optional only when a propagating Schuetzhold/GW claim is selected:
--
--   P4. one TT/device package
--       (GW tangent identity, EM Hilbert-stress identity, localized interaction,
--        plus physical reversal/conservation receipts).
--
-- What is NOT independently recharged after these packages are supplied:
--   * another static metric-response theorem;
--   * another Delta same-object theorem for a common calibrated pair;
--   * R109 finite-tail sign machinery merely to consume an already-produced
--     typed Local-C response;
--   * representation-only adapters.
------------------------------------------------------------------------

typedLocalCTerminalPhysicalPackageStillRequired : Bool
typedLocalCTerminalPhysicalPackageStillRequired =
  Reuse.typedPinnedLocalCTerminalStillRequiredForStaticReuse

commonGravityCalibrationPackageStillRequired : Bool
commonGravityCalibrationPackageStillRequired = true

matchedExperimentPackageStillRequired : Bool
matchedExperimentPackageStillRequired = true

ttDevicePackageRequiredForStaticOrScalarDifferentialRoute : Bool
ttDevicePackageRequiredForStaticOrScalarDifferentialRoute = false

ttDevicePackageRequiredWhenPropagatingGWRouteSelected : Bool
ttDevicePackageRequiredWhenPropagatingGWRouteSelected = true

independentStaticMetricResponseTheoremStillRequired : Bool
independentStaticMetricResponseTheoremStillRequired =
  Reuse.independentStaticMetricResponseReceiptRequiredAfterR136Promotion

independentDifferentialSameObjectTheoremStillRequired : Bool
independentDifferentialSameObjectTheoremStillRequired =
  Reuse.independentDeltaSameObjectTheoremRequiredAfterCommonR136Pair

r109SignMachineryRequiredForResponseReuse : Bool
r109SignMachineryRequiredForResponseReuse =
  Reuse.r136FiniteAnchorTailRequiredForStaticResponseReuse

representationOnlyAdapterDebtRemains : Bool
representationOnlyAdapterDebtRemains =
  Reuse.representationOnlyPromotionDebtRemainsAfterR136Reuse

------------------------------------------------------------------------
-- Internal subclaims remain visible but are not separately scheduled projects.
------------------------------------------------------------------------

typedTerminalInternallyNeedsBoostAndTraceContinuation : Bool
typedTerminalInternallyNeedsBoostAndTraceContinuation = true

gravityCalibrationInternallyNeedsAcceptedGAndStressLengthSquared : Bool
gravityCalibrationInternallyNeedsAcceptedGAndStressLengthSquared =
  SI.acceptedMeasuredGAuthorityStillRequired

matchedExperimentInternallyNeedsPhysicalSwitchAndSystematics : Bool
matchedExperimentInternallyNeedsPhysicalSwitchAndSystematics =
  Experiment.physicalMatchedSourceSwitchStillRequired

ttPackageInternallyNeedsThreeSameObjectWelds : Bool
ttPackageInternallyNeedsThreeSameObjectWelds =
  TT.sameGWMetricTangentStillRequired

------------------------------------------------------------------------
-- Package counts for the three preferred consumer modes.
------------------------------------------------------------------------

mandatoryStaticResponsePhysicalPackageCount : Nat
mandatoryStaticResponsePhysicalPackageCount = 3

mandatoryScalarDifferentialPhysicalPackageCount : Nat
mandatoryScalarDifferentialPhysicalPackageCount = 3

mandatoryPropagatingGWPhysicalPackageCount : Nat
mandatoryPropagatingGWPhysicalPackageCount = 4

record TerminalPhysicalPackageFrontier : Set where
  constructor terminal-physical-package-frontier
  field
    typedLocalCTerminalOpen : Bool
    commonGravityCalibrationOpen : Bool
    matchedExperimentOpen : Bool
    ttPackageOpenForScalarRoute : Bool
    ttPackageOpenForGWRoute : Bool
    extraStaticMetricResponseOpen : Bool
    extraDifferentialSameObjectOpen : Bool
    r109SignMachineryRechargedForResponseReuse : Bool
    representationAdapterDebtOpen : Bool
    staticPackageCount : Nat
    scalarDifferentialPackageCount : Nat
    propagatingGWPackageCount : Nat

canonicalTerminalPhysicalPackageFrontier : TerminalPhysicalPackageFrontier
canonicalTerminalPhysicalPackageFrontier =
  terminal-physical-package-frontier
    true true true false true false false false false
    3 3 4

independentStaticMetricResponseTheoremStillRequiredIsFalse :
  independentStaticMetricResponseTheoremStillRequired ≡ false
independentStaticMetricResponseTheoremStillRequiredIsFalse = refl

independentDifferentialSameObjectTheoremStillRequiredIsFalse :
  independentDifferentialSameObjectTheoremStillRequired ≡ false
independentDifferentialSameObjectTheoremStillRequiredIsFalse = refl

r109SignMachineryRequiredForResponseReuseIsFalse :
  r109SignMachineryRequiredForResponseReuse ≡ false
r109SignMachineryRequiredForResponseReuseIsFalse = refl

representationOnlyAdapterDebtRemainsIsFalse :
  representationOnlyAdapterDebtRemains ≡ false
representationOnlyAdapterDebtRemainsIsFalse = refl
