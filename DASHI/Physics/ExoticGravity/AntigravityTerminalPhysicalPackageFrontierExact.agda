{-# OPTIONS --safe #-}
module DASHI.Physics.ExoticGravity.AntigravityTerminalPhysicalPackageFrontierExact where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)

import DASHI.Physics.ExoticGravity.AntigravityPostNormalizationReuseMaxCutExact as Reuse
import DASHI.Physics.ExoticGravity.AntigravityDifferentialTTDonorMaxCutExact as TT
import DASHI.Physics.ExoticGravity.AntigravitySICalibrationDonorMaxCutExact as SI
import DASHI.Physics.ExoticGravity.AntigravityMatchedControlExperimentDonorMaxCutExact as Experiment
import DASHI.Physics.ExoticGravity.AntigravityP1MarkedOSParetoReuseMaxCutExact as P1
import DASHI.Physics.Foundations.CMP119AntigravityLocalCWightmanTerminalToStaticExact as Wightman

------------------------------------------------------------------------
-- TERMINAL PHYSICAL-PACKAGE FRONTIER
--
-- After the normalization-flow / Delta-V tranche and the current R136 reuse
-- compilers, the preferred source->response path is scheduled by PHYSICAL
-- PACKAGES rather than by every field inside each package.
--
-- Mandatory for static and scalar differential response:
--
--   P1. one typed Local-C/Wightman terminal package.
--       Current master Pareto-reduces this package to TWO source-facing
--       packages:
--         Q1  actual BC2 path-derivative semantics + B4-equivariant path;
--         E24 one shared pinned stress-cylinder encoding/admissibility package
--             reused definitionally for Round281 E4 clustering.
--       B0/B3 selected semantics, E4 stress selection/decay, primitive E1
--       covariance, and the downstream rest/boost/trace laws are not
--       separately recharged.
--
--   P2. one common gravitational calibration/renormalization package
--       (affine source->rho map, cosmological convention, and the
--        consumer-relevant source/device stress*length^2 scale).
--
--       Accepted measured G is no longer an open subleaf for this consumer:
--       the attributed NIST/CODATA 2022 authority admission instantiates the
--       accepted physical Einstein-coupling ABI while retaining G's quoted
--       uncertainty and the non-exactness firewall.
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
------------------------------------------------------------------------

typedLocalCTerminalPhysicalPackageStillRequired : Bool
typedLocalCTerminalPhysicalPackageStillRequired =
  Reuse.typedPinnedLocalCTerminalStillRequiredForStaticReuse

preferredSharedWightmanTerminalAvailable : Bool
preferredSharedWightmanTerminalAvailable =
  Wightman.selectedOperatorContinuationPackageAlreadyShared

independentPinnedBoostTraceSplitRequired : Bool
independentPinnedBoostTraceSplitRequired =
  Wightman.independentPinnedBoostTraceSplitRequired

------------------------------------------------------------------------
-- P1 current-master Pareto detail.
------------------------------------------------------------------------

p1OpaqueAnalyticEstimateCount : Nat
p1OpaqueAnalyticEstimateCount =
  P1.remainingOpaqueAnalyticEstimateCount

p1RemainingSameObjectResidualCount : Nat
p1RemainingSameObjectResidualCount =
  P1.remainingAntigravitySpecificP1ResidualCount

p1Q1PathDerivativeSemanticsAndEquivarianceStillRequired : Bool
p1Q1PathDerivativeSemanticsAndEquivarianceStillRequired =
  P1.q1PathDerivativeSemanticsAndEquivarianceStillRequired

p1PrimitiveE1DerivativeEquivarianceProjectRequired : Bool
p1PrimitiveE1DerivativeEquivarianceProjectRequired = false

p1SharedE2E4StressCylinderEncodingStillRequired : Bool
p1SharedE2E4StressCylinderEncodingStillRequired =
  P1.sharedE2E4StressCylinderEncodingStillRequired

p1IndependentE4StressSelectionRequired : Bool
p1IndependentE4StressSelectionRequired = false

p1IndependentE4DecayEstimateRequired : Bool
p1IndependentE4DecayEstimateRequired = false

p1IndependentTerminalLawProjectsRequired : Bool
p1IndependentTerminalLawProjectsRequired = false

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

acceptedMeasuredGAuthorityStillOpen : Bool
acceptedMeasuredGAuthorityStillOpen =
  SI.acceptedMeasuredGAuthorityStillRequired

acceptedMeasuredGAuthorityPaid : Bool
acceptedMeasuredGAuthorityPaid = true

stressLengthSquaredScaleStillOpen : Bool
stressLengthSquaredScaleStillOpen =
  SI.sourceStressLengthSquaredScaleStillRequired

gravityCalibrationInternallyNeedsAcceptedGAndStressLengthSquared : Bool
gravityCalibrationInternallyNeedsAcceptedGAndStressLengthSquared = false

matchedExperimentInternallyNeedsPhysicalSwitchAndSystematics : Bool
matchedExperimentInternallyNeedsPhysicalSwitchAndSystematics =
  Experiment.physicalMatchedSourceSwitchStillRequired

ttPackageInternallyNeedsThreeSameObjectWelds : Bool
ttPackageInternallyNeedsThreeSameObjectWelds =
  TT.sameGWMetricTangentStillRequired

------------------------------------------------------------------------
-- Package counts for the three preferred consumer modes.
--
-- P1 now contains two source-facing subpackages internally, but it remains one
-- terminal physical package at this consumer boundary.  Paying a P2 subleaf
-- likewise does not remove P2 itself.
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
    sharedWightmanTerminalPreferred : Bool
    splitBoostTraceRepresentationOpen : Bool
    acceptedMeasuredGOpen : Bool
    stressLengthSquaredProductOpen : Bool
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
    true true false false true true true false true false false false false
    3 3 4

acceptedMeasuredGAuthorityStillOpenIsFalse :
  acceptedMeasuredGAuthorityStillOpen ≡ false
acceptedMeasuredGAuthorityStillOpenIsFalse =
  SI.acceptedMeasuredGAuthorityStillRequiredIsFalse

independentPinnedBoostTraceSplitRequiredIsFalse :
  independentPinnedBoostTraceSplitRequired ≡ false
independentPinnedBoostTraceSplitRequiredIsFalse = refl

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
