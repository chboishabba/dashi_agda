module DASHI.ComputerScience.RSA260BidiCandidateRobustnessExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.ComputerScience.RSA260BidiCandidateGeneratorKernelExact as CandidateLA
import DASHI.ComputerScience.RSA260BidiCandidateBWCShadowExact as CandidateBWC

------------------------------------------------------------------------
-- PYTHON ROBUSTNESS PASS FOR THE BIDI-DERIVED CANDIDATE
--
-- Re-runs the candidate projection -> shared generator -> shifted Krylov
-- relation -> nonzero kernel -> original A^T consumer under:
--   * eight independent X/Y projection seed pairs;
--   * four left-nullspace-preserving adapters A P A^T.
--
-- This is evidence that the declared candidate behaviour is not tied to one
-- projection seed or one square adapter.  It remains synthetic/candidate-side
-- evidence and does not identify the historical RSA-260 production matrix.
------------------------------------------------------------------------

record RobustnessRuntimeSource : Set where
  constructor robustness-runtime-source
  field
    repository : String
    branch : String
    path : String
    commit : String
    gitBlob : String
    language : String
    runtime : String
open RobustnessRuntimeSource public

currentRobustnessRuntimeSource : RobustnessRuntimeSource
currentRobustnessRuntimeSource = robustness-runtime-source
  "chboishabba/dashiRTX"
  "agent/triadic-u8-runtime-oracle"
  "rsa260_bidi_candidate_robustness.py"
  "9c17938c40fa68e313813eb172d7fe2bf499236c"
  "0f60c28f01b50c2337f2e5dec0016f918119371d"
  "Python"
  "Python 3.13.5 / NumPy 2.3.5"

record SeedRobustnessReceipt : Set where
  constructor seed-robustness-receipt
  field
    independentSeedPairs : Nat
    allRunsRecoveredHeldOutValidGenerator : Bool
    minimumGeneratorDegree : Nat
    maximumGeneratorDegree : Nat
    minimumRelationSpaceDimension : Nat
    maximumRelationSpaceDimension : Nat
    everyRunRecoveredNonzeroKernel : Bool
    everyRecoveredKernelSatisfiedPreparedOperator : Bool
    everyRecoveredKernelSatisfiedOriginalAT : Bool
open SeedRobustnessReceipt public

currentSeedRobustnessReceipt : SeedRobustnessReceipt
currentSeedRobustnessReceipt = seed-robustness-receipt
  8 true 16 17 8 16 true true true

record AdapterRobustnessReceipt : Set where
  constructor adapter-robustness-receipt
  field
    adapterCount : Nat
    identityAdapterPaid : Bool
    rotateOneAdapterPaid : Bool
    affinePermutationAdapterPaid : Bool
    bitReverseAdapterPaid : Bool
    allAdaptersRecoveredHeldOutValidGenerator : Bool
    minimumGeneratorDegree : Nat
    maximumGeneratorDegree : Nat
    minimumRelationSpaceDimension : Nat
    maximumRelationSpaceDimension : Nat
    adaptersWithRejectedZeroShiftRelation : Nat
    everyAdapterRecoveredAtLeastOneNonzeroKernel : Bool
    everyAcceptedKernelSatisfiedPreparedOperator : Bool
    everyAcceptedKernelSatisfiedOriginalAT : Bool
open AdapterRobustnessReceipt public

currentAdapterRobustnessReceipt : AdapterRobustnessReceipt
currentAdapterRobustnessReceipt = adapter-robustness-receipt
  4 true true true true true 16 17 8 17 1 true true true

record CandidateRobustnessBoundary : Set where
  constructor candidate-robustness-boundary
  field
    exactGitBlobExecuted : Bool
    candidateCarrierHeldFixedAcrossSeedSweep : Bool
    projectionSeedsVaried : Bool
    preparationAdaptersVaried : Bool
    adapterFamilyPreservesOriginalLeftKernelConsumer : Bool
    generatorDegreeExactlyInvariant : Bool
    generatorDegreeStableWithinObservedBand : Bool
    relationSpaceDimensionExactlyInvariant : Bool
    everyRunProducedAcceptedKernel : Bool
    historicalSameObjectIdentityPaid : Bool
    productionCADOAdapterIdentityPaid : Bool
open CandidateRobustnessBoundary public

canonicalCandidateRobustnessBoundary : CandidateRobustnessBoundary
canonicalCandidateRobustnessBoundary = candidate-robustness-boundary
  true true true true true false true false true false false

candidateLABoundary : CandidateLA.CandidateFullLAConsumerBoundary
candidateLABoundary = CandidateLA.canonicalCandidateFullLAConsumerBoundary

candidateBWCBoundary : CandidateBWC.PreparedShadowConsumerBoundary
candidateBWCBoundary = CandidateBWC.canonicalPreparedShadowConsumerBoundary

data SeedRobustnessImpliesHistoricalIdentity : Set where
data AdapterRobustnessImpliesProductionAdapter : Set where
data DegreeBandImpliesCanonicalMinimalGenerator : Set where

seedRobustnessDoesNotCreateHistoricalIdentity : SeedRobustnessImpliesHistoricalIdentity → ⊥
seedRobustnessDoesNotCreateHistoricalIdentity ()

adapterRobustnessDoesNotCreateProductionAdapter : AdapterRobustnessImpliesProductionAdapter → ⊥
adapterRobustnessDoesNotCreateProductionAdapter ()

degreeBandDoesNotCreateCanonicalMinimalGenerator : DegreeBandImpliesCanonicalMinimalGenerator → ⊥
degreeBandDoesNotCreateCanonicalMinimalGenerator ()
