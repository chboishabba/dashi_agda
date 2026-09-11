{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.BalabanStepVMarkedSourceDirectClusteringProducerCurrentExact where

------------------------------------------------------------------------
-- CURRENT STEP-V / MARKED-SOURCE DIRECT CLUSTERING PRODUCER
--
-- This owner is intentionally smaller than the historical Step-V / KP / polymer
-- programme and smaller than the canonical B consumer cut.
--
-- Archaeology shows:
--
--   * KP -> cluster expansion convergence -> cluster-weight decay is already
--     compiler-owned once the physical Step-V hypotheses are supplied;
--   * d_A d_B log Z = <AB> - <A><B> is already a representation compiler on
--     one marked source carrier;
--   * the first theorem-bearing source-native clustering producer is therefore
--     the separation decay of the mixed marked log-partition derivative itself.
--
-- This is an OPTIONAL producer for the canonical B clustering/localisation
-- consumer.  It does not replace the current H1/H2/H3 cut and does not identify
-- finite/RG spatial decay with continuum Euclidean-time spectral clustering.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanMarkedLogPartitionConnectedCorrelationCompilerExact as Marked
import DASHI.Physics.YangMills.BalabanLargeFieldStepV as StepV

-- Re-export the literal compiler theorem under a proof-search-facing name.
stepVMarkedSourceDecayProducesConnectedCorrelation :
  ∀ {Observable Scalar Bound Distance}
    {response : Marked.MarkedTwoSourceResponse Observable Scalar}
    (producer : Marked.SeparationDecayProducer response)
    (A B : Observable) →
  Marked.LessEqual producer
    (Marked.absoluteValue producer (Marked.connectedCorrelation response A B))
    (Marked.decayEnvelope producer (Marked.distance producer A B))
stepVMarkedSourceDecayProducesConnectedCorrelation =
  Marked.connectedCorrelationDecayFromMarkedSource

-- The historical Step-V chain already exposes the abstract compiler from
-- exponential cluster-weight decay to a connected-correlation cluster bound.
-- This theorem does not create that implication: it records the exact existing
-- compiler shape so the current route can distinguish it from the physical
-- marked-source decay theorem above.
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

    markedMixedDerivativeSeparationDecayIsTheoremBearing : Bool
    markedMixedDerivativeSeparationDecayIsTheoremBearingIsTrue :
      markedMixedDerivativeSeparationDecayIsTheoremBearing ≡ true

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
    false refl

stepVAbstractAssemblyLevel : ProofLevel
stepVAbstractAssemblyLevel = machineChecked

markedSourceCorrelationCompilerLevel : ProofLevel
markedSourceCorrelationCompilerLevel = machineChecked

-- This label follows the existing repository proof-classification convention;
-- it does not assert that the physical mixed-derivative decay has been supplied.
markedMixedDerivativeSeparationDecayLevel : ProofLevel
markedMixedDerivativeSeparationDecayLevel = conditional

clayPromotion : Bool
clayPromotion = false

clayPromotionIsFalse : clayPromotion ≡ false
clayPromotionIsFalse = refl
