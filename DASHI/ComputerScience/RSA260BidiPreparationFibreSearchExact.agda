module DASHI.ComputerScience.RSA260BidiPreparationFibreSearchExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.ComputerScience.RSA260BidiCandidateRobustnessExact as Robust
import DASHI.ComputerScience.RSA260BidiCandidateGeneratorKernelExact as CandidateLA

------------------------------------------------------------------------
-- PREPARATION-FIBRE SEARCH
--
-- Search over invertible permutation preparations B_P = A P A^T while holding
-- the original rectangular A and the exact declared consumer fixed:
--
--   exists nonzero y with B_P y = 0 and A^T y = 0.
--
-- Presentation costs are observed after consumer admission.  Lower generator
-- degree / relation dimension / rejected-zero count / kernel weight are ranking
-- coordinates only; none identifies the historical CADO preparation.
------------------------------------------------------------------------

record PreparationSearchRuntimeSource : Set where
  constructor preparation-search-runtime-source
  field
    repository : String
    branch : String
    path : String
    commit : String
    committedGitBlob : String
    locallyExecutedGitBlob : String
    language : String
    runtime : String
open PreparationSearchRuntimeSource public

currentPreparationSearchRuntimeSource : PreparationSearchRuntimeSource
currentPreparationSearchRuntimeSource = preparation-search-runtime-source
  "chboishabba/dashiRTX"
  "agent/triadic-u8-runtime-oracle"
  "rsa260_bidi_preparation_fibre_search.py"
  "a71c381a9c200af96ac1341be58d53a82383da85"
  "47cdf55ad6fa2ab27215c125b2ce3e0ba9c0991c"
  "95c449a98bafb267ba0d1a5f93b94d80f285c566"
  "Python"
  "Python 3.13.5 / NumPy 2.3.5"

record PreparationSearchReceipt : Set where
  constructor preparation-search-receipt
  field
    testedAdapters : Nat
    admittedAdapters : Nat
    everyTestedAdapterRecoveredConsumerKernel : Bool
    minimumObservedGeneratorDegree : Nat
    maximumObservedGeneratorDegree : Nat
    minimumObservedRelationSpaceDimension : Nat
    maximumObservedRelationSpaceDimension : Nat
    adaptersWithRejectedZeroShift : Nat
    structuralFrontierMembers : Nat
    sourceEquivalentExecutionPassed : Bool
    exactCommittedGitBlobExecuted : Bool
open PreparationSearchReceipt public

currentPreparationSearchReceipt : PreparationSearchReceipt
currentPreparationSearchReceipt = preparation-search-receipt
  20 20 true
  16 17
  8 17
  2
  2
  true false

record BestTestedPreparationReceipt : Set where
  constructor best-tested-preparation-receipt
  field
    adapterLabel : String
    generatorDegree : Nat
    relationSpaceDimension : Nat
    rejectedZeroShiftRelations : Nat
    minimumKernelWeight : Nat
    maximumKernelWeight : Nat
    consumerPassed : Bool
    globallyOptimalOverAllInvertiblePreparations : Bool
open BestTestedPreparationReceipt public

currentBestTestedPreparationReceipt : BestTestedPreparationReceipt
currentBestTestedPreparationReceipt = best-tested-preparation-receipt
  "affine_511_1 : i -> -i + 1 mod 512"
  16 8 0 12 416 true false

record AlternateFrontierPreparationReceipt : Set where
  constructor alternate-frontier-preparation-receipt
  field
    adapterLabel : String
    generatorDegree : Nat
    relationSpaceDimension : Nat
    minimumKernelWeight : Nat
    maximumKernelWeight : Nat
    consumerPassed : Bool
open AlternateFrontierPreparationReceipt public

currentAlternateFrontierPreparationReceipt : AlternateFrontierPreparationReceipt
currentAlternateFrontierPreparationReceipt = alternate-frontier-preparation-receipt
  "rotate31"
  16 8 52 180 true

record PreparationFibreInterpretationBoundary : Set where
  constructor preparation-fibre-interpretation-boundary
  field
    originalCarrierHeldFixed : Bool
    preparationPresentationVaried : Bool
    consumerHeldFixed : Bool
    allObservedPresentationsConsumerEquivalent : Bool
    generatorPresentationInvariant : Bool
    relationSpacePresentationInvariant : Bool
    kernelWeightPresentationInvariant : Bool
    rankingOccursOnlyAfterConsumerAdmission : Bool
    bestTestedEqualsGlobalOptimum : Bool
    bestTestedEqualsProductionCADOPreparation : Bool
    historicalIdentityPaid : Bool
open PreparationFibreInterpretationBoundary public

canonicalPreparationFibreInterpretationBoundary : PreparationFibreInterpretationBoundary
canonicalPreparationFibreInterpretationBoundary = preparation-fibre-interpretation-boundary
  true true true true
  false false false
  true
  false false false

robustnessBoundary : Robust.CandidateRobustnessBoundary
robustnessBoundary = Robust.canonicalCandidateRobustnessBoundary

candidateLABoundary : CandidateLA.CandidateFullLAConsumerBoundary
candidateLABoundary = CandidateLA.canonicalCandidateFullLAConsumerBoundary

------------------------------------------------------------------------
-- Next bidi residual: enlarge and adaptively search the preparation family,
-- while measuring real execution/storage cost and retaining held-out consumer
-- validation.  The present 20-point family is evidence, not exhaustive search.
------------------------------------------------------------------------

data PreparationFibreResidual : Set where
  exactByteExecuteCommittedSearch : PreparationFibreResidual
  enlargeInvertiblePreparationFamily : PreparationFibreResidual
  addMeasuredPreparationExecutionCosts : PreparationFibreResidual
  crossValidateBestPreparationsAcrossProjectionSeeds : PreparationFibreResidual
  testBestPreparationAtWidth256 : PreparationFibreResidual
  compareAgainstSameObjectProductionPreparation : PreparationFibreResidual

firstPreparationFibreResidual : PreparationFibreResidual
firstPreparationFibreResidual = exactByteExecuteCommittedSearch

------------------------------------------------------------------------
-- WrongType firewalls.
------------------------------------------------------------------------

data SparseKernelImpliesBetterFactoring : Set where
data LowDegreeImpliesCanonicalGenerator : Set where
data ParetoFrontierImpliesProductionIdentity : Set where
data TwentyAdaptersImpliesGlobalSearch : Set where

sparseKernelDoesNotImplyBetterFactoring : SparseKernelImpliesBetterFactoring → ⊥
sparseKernelDoesNotImplyBetterFactoring ()

lowDegreeDoesNotCreateCanonicalGenerator : LowDegreeImpliesCanonicalGenerator → ⊥
lowDegreeDoesNotCreateCanonicalGenerator ()

frontierDoesNotCreateProductionIdentity : ParetoFrontierImpliesProductionIdentity → ⊥
frontierDoesNotCreateProductionIdentity ()

twentyAdaptersDoNotCreateGlobalSearch : TwentyAdaptersImpliesGlobalSearch → ⊥
twentyAdaptersDoNotCreateGlobalSearch ()
