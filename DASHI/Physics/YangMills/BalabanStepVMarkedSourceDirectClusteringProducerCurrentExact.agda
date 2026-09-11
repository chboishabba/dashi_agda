{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.BalabanStepVMarkedSourceDirectClusteringProducerCurrentExact where

------------------------------------------------------------------------
-- CURRENT STEP-V / MARKED-SOURCE DIRECT CLUSTERING PRODUCER
--
-- Archaeology correction:
--
-- * historical Step-V/KP remains an optional producer family;
-- * the marked log-partition mixed-derivative = connected-correlation identity
--   is compiler-owned;
-- * CMP109/CMP116 already source-own the differentiated marked exponential
--   decay/localisation theorem shape;
-- * the first live source-native physical seam is therefore SAME-OBJECT
--   APPLICABILITY: identify the published E^(2)/Pi / J-source magnitude,
--   connecting root and distance with the selected physical T5 two-J carrier.
--
-- Once that weld is supplied, R309 compiles directly into the exact current H1
-- localisation package.  This route remains OPTIONAL below the canonical B
-- consumer and does not identify finite/RG spatial decay with continuum
-- Euclidean-time spectral clustering.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanMarkedLogPartitionConnectedCorrelationCompilerExact as Marked
import DASHI.Physics.YangMills.BalabanLargeFieldStepV as StepV
import DASHI.Physics.YangMills.BalabanMarkedHessianPublishedDecayBoundaryExact as CMP109
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

-- Historical Step-V abstract compiler.  This is retained as a producer tactic,
-- not promoted to the canonical consumer cut.
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

    selectedJApplicabilityIsFirstLiveSourceSeam : Bool
    selectedJApplicabilityIsFirstLiveSourceSeamIsTrue :
      selectedJApplicabilityIsFirstLiveSourceSeam ≡ true

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
    true refl
    false refl
    false refl

stepVAbstractAssemblyLevel : ProofLevel
stepVAbstractAssemblyLevel = machineChecked

markedSourceCorrelationCompilerLevel : ProofLevel
markedSourceCorrelationCompilerLevel = machineChecked

cmp109MarkedDerivativeDecayLevel : ProofLevel
cmp109MarkedDerivativeDecayLevel = CMP109.cmp109DifferentiatedMarkedActivityDecayLevel

-- Current first physical/source seam on this producer route.
selectedJApplicabilityPhysicalLevel : ProofLevel
selectedJApplicabilityPhysicalLevel = R309.selectedJApplicabilityPhysicalLevel

-- Once applicability is paid, the source localization -> exact H1 adapter is
-- already compiler-owned in R309.
selectedJApplicabilityCompilerLevel : ProofLevel
selectedJApplicabilityCompilerLevel = R309.selectedJApplicabilityCompilerLevel

clayPromotion : Bool
clayPromotion = false

clayPromotionIsFalse : clayPromotion ≡ false
clayPromotionIsFalse = refl
