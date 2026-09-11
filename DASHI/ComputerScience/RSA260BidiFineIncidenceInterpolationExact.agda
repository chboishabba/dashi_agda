module DASHI.ComputerScience.RSA260BidiFineIncidenceInterpolationExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.ComputerScience.RSA260BidiFineIncidencePredictorExact as Predictor
import DASHI.ComputerScience.RSA260BlockWiedemannProductionScaleReconstructionExact as Scale

------------------------------------------------------------------------
-- FINE-INCIDENCE INTERPOLATION / LOCAL FRAGILITY
--
-- Starting from the cyclic executable shadow, retain the exact coarse carrier
-- contract (924x512, six degree-151 rows, 918 degree-150 rows, rank 512,
-- left-nullity 412) while progressively rewiring row incidences.
--
-- Under one fixed source-derived CADO-shaped 4x4 preparation analogue and one
-- fixed projection seed:
--   alpha = 0      -> first withheld-valid shared generator d=16
--   alpha >= .125  -> d=65..66 on the coarse interpolation
--
-- A nested transition zoom then shows that one degree-preserving support swap
-- in every row is already sufficient, on the tested path, to move d=16 -> 66.
-- Eight independently seeded one-swap-per-row interventions all recover the
-- declared consumer at d in {65,66}.
--
-- This establishes tested local fragility of the LOW-DEGREE PRESENTATION, not
-- consumer failure and not a universal or production threshold.
------------------------------------------------------------------------

predictorBoundary : Predictor.FineIncidencePredictorBoundary
predictorBoundary = Predictor.canonicalFineIncidencePredictorBoundary

snowballSourceAtlas : Scale.ProductionScaleSourceAtlas
snowballSourceAtlas = Scale.currentProductionScaleSourceAtlas

snowballIdentityCoordinates : Scale.ProductionScaleIdentityCoordinates
snowballIdentityCoordinates = Scale.currentProductionScaleIdentityCoordinates

------------------------------------------------------------------------
-- Runtime provenance.  The top-level files were exact-byte executed.  Their
-- local imported preparation-search dependency was source-equivalent but not
-- byte-identical to the committed dependency closure in that execution env.
------------------------------------------------------------------------

record FineIncidenceInterpolationRuntime : Set where
  constructor fine-incidence-interpolation-runtime
  field
    repository : String
    branch : String
    interpolationPath : String
    interpolationCommit : String
    interpolationBlob : String
    transitionPath : String
    transitionCommit : String
    transitionBlob : String
    oneSwapPath : String
    oneSwapCommit : String
    oneSwapBlob : String
    ensemblePath : String
    ensembleCommit : String
    ensembleBlob : String
    dependencyPath : String
    committedDependencyBlob : String
    exactTopLevelBlobsExecuted : Bool
    exactDependencyClosureExecuted : Bool
open FineIncidenceInterpolationRuntime public

currentFineIncidenceInterpolationRuntime : FineIncidenceInterpolationRuntime
currentFineIncidenceInterpolationRuntime = fine-incidence-interpolation-runtime
  "chboishabba/dashiRTX"
  "agent/triadic-u8-runtime-oracle"
  "rsa260_bidi_fine_incidence_interpolation.py"
  "21dccf8ff331a0ab28f5378d7c8aef04ebfb97de"
  "a6b3c8b9757592e84a45ddf4a29a0461b65a7918"
  "rsa260_bidi_fine_incidence_transition_zoom.py"
  "f7cea18ed4543fed32b04a8de66fe61c7a89b7f5"
  "99715d688ef98bde0623204258c08bf0b8ba6cc1"
  "rsa260_bidi_one_swap_per_row_fragility.py"
  "3a93b98ae99cb6c5ab9b020d89f0e527515ac9c6"
  "3f550c5d410b5aa6e6ad09ee1557ed8579c70bdb"
  "rsa260_bidi_one_swap_per_row_ensemble.py"
  "3de6e2fa1c0d7ef63a41fb0e307d3f9fa5950eef"
  "574a04d3e4b068921b94bd914c808b7ead7f3c52"
  "rsa260_bidi_preparation_fibre_search.py"
  "47cdf55ad6fa2ab27215c125b2ce3e0ba9c0991c"
  true false

------------------------------------------------------------------------
-- Experimental receipts.
------------------------------------------------------------------------

record CoarseInterpolationReceipt : Set where
  constructor coarse-interpolation-receipt
  field
    interpolationLevels : Nat
    allLevelsRank512 : Bool
    allLevelsLeftNullity412 : Bool
    allLevelsPreserveDegreeProfile : Bool
    allLevelsRecoverConsumer : Bool
    baseGeneratorDegree : Nat
    first125PercentGeneratorDegree : Nat
    fullyRewiredGeneratorDegree : Nat
    minimumPerturbedGeneratorDegree : Nat
    maximumPerturbedGeneratorDegree : Nat
open CoarseInterpolationReceipt public

currentCoarseInterpolationReceipt : CoarseInterpolationReceipt
currentCoarseInterpolationReceipt = coarse-interpolation-receipt
  6 true true true true
  16 65 66 65 66

record OneSwapFragilityReceipt : Set where
  constructor one-swap-fragility-receipt
  field
    rows : Nat
    columns : Nat
    swapsPerRow : Nat
    baseRank : Nat
    perturbedRank : Nat
    baseLeftNullity : Nat
    perturbedLeftNullity : Nat
    baseGeneratorDegree : Nat
    singlePathPerturbedGeneratorDegree : Nat
    ensembleRuns : Nat
    ensembleRunsAdmitted : Nat
    ensembleMinimumGeneratorDegree : Nat
    ensembleMaximumGeneratorDegree : Nat
    ensembleAllShiftedRank512 : Bool
    consumerLostByPerturbation : Bool
open OneSwapFragilityReceipt public

currentOneSwapFragilityReceipt : OneSwapFragilityReceipt
currentOneSwapFragilityReceipt = one-swap-fragility-receipt
  924 512 1
  512 512 412 412
  16 66
  8 8 65 66 true false

record FineIncidenceFragilityBoundary : Set where
  constructor fine-incidence-fragility-boundary
  field
    sameCoarseContractDeterminesLowDegreeRecurrence : Bool
    oneSwapPerRowPreservesLowDegreeRecurrenceOnTestedEnsemble : Bool
    oneSwapPerRowPreservesDeclaredKernelConsumerOnTestedEnsemble : Bool
    testedLowDegreePresentationIsLocallyFragile : Bool
    observedTransitionIsUniversalThreshold : Bool
    syntheticFragilityIsProductionMeasurement : Bool
    structuralAssociationIsCausalMechanismProof : Bool
    exactDependencyClosureExecutionPaid : Bool
open FineIncidenceFragilityBoundary public

canonicalFineIncidenceFragilityBoundary : FineIncidenceFragilityBoundary
canonicalFineIncidenceFragilityBoundary = fine-incidence-fragility-boundary
  false false true true false false false false

------------------------------------------------------------------------
-- Next bidi residual.
------------------------------------------------------------------------

data FineIncidenceInterpolationResidual : Set where
  repeatOneSwapEnsembleAcrossProjectionSeeds : FineIncidenceInterpolationResidual
  deriveTwoHopAndCommonNeighbourFibres : FineIncidenceInterpolationResidual
  fitRecurrenceComplexityFromStructuralFibrePortfolio : FineIncidenceInterpolationResidual
  acquireSameObjectFineIncidenceBearingArtifact : FineIncidenceInterpolationResidual

firstFineIncidenceInterpolationResidual : FineIncidenceInterpolationResidual
firstFineIncidenceInterpolationResidual = repeatOneSwapEnsembleAcrossProjectionSeeds

------------------------------------------------------------------------
-- WrongType firewalls.
------------------------------------------------------------------------

data LocalFragilityImpliesUniversalThreshold : Set where
data SyntheticFragilityImpliesProductionMeasurement : Set where
data RecurrenceFragilityImpliesConsumerFailure : Set where
data DOIOrQIDImpliesProof : Set where

localFragilityDoesNotCreateUniversalThreshold : LocalFragilityImpliesUniversalThreshold → ⊥
localFragilityDoesNotCreateUniversalThreshold ()

syntheticFragilityDoesNotCreateProductionMeasurement : SyntheticFragilityImpliesProductionMeasurement → ⊥
syntheticFragilityDoesNotCreateProductionMeasurement ()

recurrenceFragilityDoesNotCreateConsumerFailure : RecurrenceFragilityImpliesConsumerFailure → ⊥
recurrenceFragilityDoesNotCreateConsumerFailure ()

doiOrQidDoesNotCreateProof : DOIOrQIDImpliesProof → ⊥
doiOrQidDoesNotCreateProof ()
