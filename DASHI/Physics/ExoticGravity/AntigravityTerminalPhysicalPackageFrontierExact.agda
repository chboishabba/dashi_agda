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
import DASHI.Physics.ExoticGravity.AntigravitySameStateFourChannelDiscriminatorExact as FourChannel
import DASHI.Physics.Foundations.CMP119AntigravityLocalCWightmanTerminalToStaticExact as Wightman

------------------------------------------------------------------------
-- TERMINAL PHYSICAL-PACKAGE FRONTIER
--
-- Mandatory for static and scalar differential response:
--
--   P1. one typed Local-C/Wightman terminal package.  Current master reduces
--       its antigravity-specific source content to TWO subpackages:
--
--       Q1  actual BC2 path-derivative semantics + B4-equivariant path;
--       E24 one literal selected R109 real cylinder observable together with
--           positive-time and gauge-invariance proofs.
--
--       The selected R109 insertion identity is definitionally pinned.  No
--       arbitrary meaning predicate, all-stress encoding family, separate E4
--       observable/decay theorem, primitive E1 covariance project, B0/B3
--       antigravity-specific bridge, or downstream rest/boost/trace law is
--       independently scheduled.
--
--   P2. one common gravitational calibration/renormalization package
--       (affine source->rho map, cosmological convention, and the
--        consumer-relevant source/device stress*length^2 scale).  Accepted
--       measured G is already paid by the attributed CODATA-2022 admission.
--
--   P3. one matched experimental package.  The repository-internal experiment
--       compiler is now paid: one selected source compiles to one stress, one
--       metric and four consumers (weight, free-fall, clock, optical);
--       mechanism-signature templates are separated and nuisance closure is
--       candidate-bound.  What remains is physical: a real source switch, a
--       numerical systematic floor, and replication.
--
-- Optional only for a propagating Schuetzhold/GW claim:
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

p1E24ObservableAndTwoAdmissibilityProofsStillRequired : Bool
p1E24ObservableAndTwoAdmissibilityProofsStillRequired =
  P1.e24NovelDataAreOneObservableAndTwoAdmissibilityProofs

p1E24ArbitraryMeaningPredicateRequired : Bool
p1E24ArbitraryMeaningPredicateRequired = false

p1AllStressCylinderEncodingRequired : Bool
p1AllStressCylinderEncodingRequired = false

p1IndependentE4StressSelectionRequired : Bool
p1IndependentE4StressSelectionRequired = false

p1IndependentE4DecayEstimateRequired : Bool
p1IndependentE4DecayEstimateRequired = false

p1IndependentTerminalLawProjectsRequired : Bool
p1IndependentTerminalLawProjectsRequired = false

------------------------------------------------------------------------
-- P2 calibration frontier.
------------------------------------------------------------------------

commonGravityCalibrationPackageStillRequired : Bool
commonGravityCalibrationPackageStillRequired = true

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

------------------------------------------------------------------------
-- P3 four-channel experiment compiler: STRUCTURAL PART PAID.
------------------------------------------------------------------------

sameStateFourChannelCompilerConstructed : Bool
sameStateFourChannelCompilerConstructed = true

sameSourceStressMetricChainConstructed : Bool
sameSourceStressMetricChainConstructed = true

mechanismSignatureTemplatesConstructed : Bool
mechanismSignatureTemplatesConstructed = true

candidateBoundNuisanceClosureContractConstructed : Bool
candidateBoundNuisanceClosureContractConstructed = true

preferredSingleVacuumFixtureFeedsDiscriminator : Bool
preferredSingleVacuumFixtureFeedsDiscriminator = true

fourChannelStructureDoesNotPayExperiment : Bool
fourChannelStructureDoesNotPayExperiment = true

physicalMatchedSourceSwitchStillOpen : Bool
physicalMatchedSourceSwitchStillOpen =
  Experiment.physicalMatchedSourceSwitchStillRequired

numericalSystematicsBudgetStillOpen : Bool
numericalSystematicsBudgetStillOpen =
  Experiment.numericalSystematicsBudgetStillRequired

empiricalReplicationStillOpen : Bool
empiricalReplicationStillOpen =
  Experiment.empiricalReplicationStillRequired

matchedExperimentPackageStillRequired : Bool
matchedExperimentPackageStillRequired = true

matchedExperimentInternallyNeedsPhysicalSwitchAndSystematics : Bool
matchedExperimentInternallyNeedsPhysicalSwitchAndSystematics =
  physicalMatchedSourceSwitchStillOpen

------------------------------------------------------------------------
-- P4 optional propagating-wave package.
------------------------------------------------------------------------

ttDevicePackageRequiredForStaticOrScalarDifferentialRoute : Bool
ttDevicePackageRequiredForStaticOrScalarDifferentialRoute = false

ttDevicePackageRequiredWhenPropagatingGWRouteSelected : Bool
ttDevicePackageRequiredWhenPropagatingGWRouteSelected = true

ttPackageInternallyNeedsThreeSameObjectWelds : Bool
ttPackageInternallyNeedsThreeSameObjectWelds =
  TT.sameGWMetricTangentStillRequired

------------------------------------------------------------------------
-- Reuse firewalls.
------------------------------------------------------------------------

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

typedTerminalInternallyNeedsBoostAndTraceContinuation : Bool
typedTerminalInternallyNeedsBoostAndTraceContinuation = true

------------------------------------------------------------------------
-- Package counts for preferred consumer modes.
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
    fourChannelCompilerPaid : Bool
    sourceStressMetricChainPaid : Bool
    candidateBoundNuisanceContractPaid : Bool
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
    true true false false true true true true true true false true false false false false
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

weightOnlyMetricPromotionBlocked : Bool
weightOnlyMetricPromotionBlocked = FourChannel.weightOnlyCannotPromoteMetricClaim

scalarMetricToTTDirectPromotionBlocked : Bool
scalarMetricToTTDirectPromotionBlocked =
  FourChannel.scalarMetricPerturbationIsNotTTMode
