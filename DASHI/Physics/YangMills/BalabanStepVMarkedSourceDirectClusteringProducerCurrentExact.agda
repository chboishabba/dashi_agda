{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.BalabanStepVMarkedSourceDirectClusteringProducerCurrentExact where

------------------------------------------------------------------------
-- CURRENT STEP-V / MARKED-SOURCE DIRECT CLUSTERING PRODUCER
--
-- Archaeology-normalized producer view:
--
-- * historical Step-V/KP remains an OPTIONAL producer family;
-- * normalized mixed-log derivative = connected covariance is compiler-owned;
-- * CMP109/CMP116 already source-own differentiated marked exponential
--   localization on their declared analytic coordinates;
-- * common-radius construction and finite differentiation are compiler/source
--   consequences, not separate B-side research leaves;
-- * the single live source-facing payment is therefore the exact R296/R299/R295
--   theorem on the selected physical T5 carrier:
--
--       |D^2_{J_L,J_R} log Z| <= rooted connecting shell.
--
-- Equivalently: instantiate the published CMP116/CMP109 localization theorem on
-- the literal selected physical J directions, same active density, same root and
-- same physical support distance.  Once that same-object/application payment is
-- supplied, the rest of the finite-T5 correlation localization is compiler-owned.
--
-- This route remains below the canonical B consumer and does not identify
-- finite/RG spatial decay with continuum Euclidean-time spectral clustering.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanMarkedLogPartitionConnectedCorrelationCompilerExact as Marked
import DASHI.Physics.YangMills.BalabanLargeFieldStepV as StepV
import DASHI.Physics.YangMills.BalabanMarkedHessianPublishedDecayBoundaryExact as CMP109
import DASHI.Physics.YangMills.BalabanCMP116DifferentiatedLocalizationSourceExact as CMP116
import DASHI.Physics.YangMills.BalabanT5StateFamilySourceAlgebraRound295Exact as R295
import DASHI.Physics.YangMills.BalabanT5JMagnitudeDirectShellRound296Exact as R296
import DASHI.Physics.YangMills.BalabanAbsoluteTwoJSourceMinCutRound299Exact as R299
import DASHI.Physics.YangMills.BalabanCMP116SelectedJApplicabilityRound309Exact as R309

-- Generic marked-source representation compiler.
markedSourceDecayProducesConnectedCorrelation :
  ∀ {Observable Scalar Bound Distance}
    {response : Marked.MarkedTwoSourceResponse Observable Scalar}
    (producer : Marked.SeparationDecayProducer response)
    (A B : Observable) →
  Marked.LessEqual producer
    (Marked.absoluteValue producer (Marked.connectedCorrelation response A B))
    (Marked.decayEnvelope producer (Marked.distance producer A B))
markedSourceDecayProducesConnectedCorrelation =
  Marked.connectedCorrelationDecayFromMarkedSource

-- Historical Step-V abstract compiler retained only as a producer tactic.
stepVClusterWeightDecayToCorrelationCompiler :
  ∀ {Site Polymer Configuration Bound : Set}
    (estimates : StepV.LargeFieldStepVEstimates Site Polymer Configuration Bound) →
  StepV.LargeFieldStepVEstimates.ClusterWeightsExponentiallyDecay estimates →
  StepV.LargeFieldStepVEstimates.ConnectedCorrelationsClusterBound estimates
stepVClusterWeightDecayToCorrelationCompiler estimates =
  StepV.LargeFieldStepVEstimates.connectedCorrelationTheorem estimates

record CurrentStepVProducerBoundary : Set where
  constructor current-stepv-producer-boundary
  field
    kpToClusterConvergenceCompilerOwned : Bool
    kpToClusterConvergenceCompilerOwnedIsTrue :
      kpToClusterConvergenceCompilerOwned ≡ true

    clusterConvergenceToWeightDecayCompilerOwned : Bool
    clusterConvergenceToWeightDecayCompilerOwnedIsTrue :
      clusterConvergenceToWeightDecayCompilerOwned ≡ true

    mixedDerivativeMeaningCompilerOwned : Bool
    mixedDerivativeMeaningCompilerOwnedIsTrue :
      mixedDerivativeMeaningCompilerOwned ≡ true

    cmp109MarkedDerivativeDecaySourceOwned : Bool
    cmp109MarkedDerivativeDecaySourceOwnedIsTrue :
      cmp109MarkedDerivativeDecaySourceOwned ≡ true

    commonRadiusIndependentBLeaf : Bool
    commonRadiusIndependentBLeafIsFalse :
      commonRadiusIndependentBLeaf ≡ false

    literalAbsoluteTwoJLocalizationIsSingleLiveSourcePayment : Bool
    literalAbsoluteTwoJLocalizationIsSingleLiveSourcePaymentIsTrue :
      literalAbsoluteTwoJLocalizationIsSingleLiveSourcePayment ≡ true

    stepVRouteMandatoryForCanonicalB : Bool
    stepVRouteMandatoryForCanonicalBIsFalse :
      stepVRouteMandatoryForCanonicalB ≡ false

    finiteSpatialDecayEqualsContinuumTimeClustering : Bool
    finiteSpatialDecayEqualsContinuumTimeClusteringIsFalse :
      finiteSpatialDecayEqualsContinuumTimeClustering ≡ false

canonicalCurrentStepVProducerBoundary : CurrentStepVProducerBoundary
canonicalCurrentStepVProducerBoundary =
  current-stepv-producer-boundary
    true refl
    true refl
    true refl
    true refl
    false refl
    true refl
    false refl
    false refl

stepVAbstractAssemblyLevel : ProofLevel
stepVAbstractAssemblyLevel = machineChecked

markedSourceCorrelationCompilerLevel : ProofLevel
markedSourceCorrelationCompilerLevel = machineChecked

cmp109MarkedDerivativeDecayLevel : ProofLevel
cmp109MarkedDerivativeDecayLevel = CMP109.cmp109DifferentiatedMarkedActivityDecayLevel

cmp116FiniteDerivativeLocalizationLevel : ProofLevel
cmp116FiniteDerivativeLocalizationLevel = CMP116.cmp116DifferentiatedActivityLocalizationLevel

-- These are three historical/current names for the same live source-facing cut.
-- R296 is the literal theorem shape; R299 is the least-privilege source cut;
-- R295 is the exact finite-T5 source-algebra field consumed downstream.
literalAbsoluteTwoJLocalizationLevel : ProofLevel
literalAbsoluteTwoJLocalizationLevel = R296.round296LiteralAbsoluteTwoJLocalizationLevel

leastPrivilegeSelectedJSameObjectLocalizationLevel : ProofLevel
leastPrivilegeSelectedJSameObjectLocalizationLevel =
  R299.round299LiteralSelectedJSameObjectLocalizationLevel

exactT5SelectedJDirectionLocalizationLevel : ProofLevel
exactT5SelectedJDirectionLocalizationLevel =
  R295.round295LiteralT5JDirectionLocalizationLevel

-- R309 exposes the same payment as explicit source theorem + same-object
-- applicability coordinates.  The applicability half remains physical.
selectedJApplicabilityPhysicalLevel : ProofLevel
selectedJApplicabilityPhysicalLevel = R309.selectedJApplicabilityPhysicalLevel

selectedJApplicabilityCompilerLevel : ProofLevel
selectedJApplicabilityCompilerLevel = R309.selectedJApplicabilityCompilerLevel

clayPromotion : Bool
clayPromotion = false

clayPromotionIsFalse : clayPromotion ≡ false
clayPromotionIsFalse = refl
