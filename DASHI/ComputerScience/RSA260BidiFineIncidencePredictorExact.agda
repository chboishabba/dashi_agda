module DASHI.ComputerScience.RSA260BidiFineIncidencePredictorExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.ComputerScience.RSA260BidiCADOGridPermutationCrossValidationExact as CADOGrid
import DASHI.ComputerScience.RSA260BidiRandomIncidenceCarrierCrossValidationExact as RandomIncidence

------------------------------------------------------------------------
-- ENDOGENOUS FINE-INCIDENCE PREDICTOR PROBE
--
-- Hold preparation and projection fixed, then derive two local structural
-- fibres directly from A:
--
--   adjacency(A)   = mean_r |S_r intersect (S_r + 1)|
--   translation(A) = mean_r max_s |(S_r+s) intersect S_{r+1}|.
--
-- On the tested family these sharply separate the cyclic-interval carriers
-- (d=16..17 under fixed CADO-shaped 4x4 preparation) from the random exact-
-- degree carriers (d=65).  They do NOT distinguish degree 16 from 17 inside
-- the cyclic family, hence are family-level predictors, not a complete model.
------------------------------------------------------------------------

cadoGridBoundary : CADOGrid.CADOGridInterpretationBoundary
cadoGridBoundary = CADOGrid.canonicalCADOGridInterpretationBoundary

randomIncidenceBoundary : RandomIncidence.RandomIncidenceInterpretationBoundary
randomIncidenceBoundary = RandomIncidence.canonicalRandomIncidenceInterpretationBoundary

record FineIncidenceRuntimeSource : Set where
  constructor fine-incidence-runtime-source
  field
    repository : String
    branch : String
    path : String
    commit : String
    gitBlob : String
    dependencyPath : String
    dependencyGitBlob : String
    exactRuntimeBlobExecuted : Bool
    exactDependencyBlobExecuted : Bool
open FineIncidenceRuntimeSource public

currentFineIncidenceRuntimeSource : FineIncidenceRuntimeSource
currentFineIncidenceRuntimeSource = fine-incidence-runtime-source
  "chboishabba/dashiRTX"
  "agent/triadic-u8-runtime-oracle"
  "rsa260_bidi_fine_incidence_predictor.py"
  "f037ccc54d1c0a989e1758a3f3088840ddd63385"
  "34cb858752ce57510a58bcb46b1ba7aaa2073139"
  "rsa260_bidi_candidate_robustness.py"
  "0f60c28f01b50c2337f2e5dec0016f918119371d"
  true true

record FineIncidencePredictorReceipt : Set where
  constructor fine-incidence-predictor-receipt
  field
    fixedPreparation : String
    cyclicCarriers : Nat
    randomCarriers : Nat
    cyclicAdjacencyMean : String
    randomAdjacencyMinimum : String
    randomAdjacencyMaximum : String
    cyclicTranslationOverlapMean : String
    randomTranslationOverlapMinimum : String
    randomTranslationOverlapMaximum : String
    cyclicMinimumGeneratorDegree : Nat
    cyclicMaximumGeneratorDegree : Nat
    randomMinimumGeneratorDegree : Nat
    randomMaximumGeneratorDegree : Nat
    allConsumersPassed : Bool
open FineIncidencePredictorReceipt public

currentFineIncidencePredictorReceipt : FineIncidencePredictorReceipt
currentFineIncidencePredictorReceipt = fine-incidence-predictor-receipt
  "CADO-shaped 4x4 block-grid transpose analogue"
  4 4
  "149.0064935064935"
  "43.63203463203463" "43.892857142857146"
  "150.078125"
  "58.3125" "58.625"
  16 17
  65 65
  true

record FineIncidencePredictorBoundary : Set where
  constructor fine-incidence-predictor-boundary
  field
    endogenousFibresSeparateTestedFamilies : Bool
    coarseDegreeProfileAloneSeparatesFamilies : Bool
    adjacencyAlonePredictsExactGeneratorDegree : Bool
    translationOverlapAlonePredictsExactGeneratorDegree : Bool
    predictorIsCausalMechanismProof : Bool
    predictorMeasuredOnProductionMatrix : Bool
    predictorUsefulAsFutureProductionDiagnostic : Bool
open FineIncidencePredictorBoundary public

canonicalFineIncidencePredictorBoundary : FineIncidencePredictorBoundary
canonicalFineIncidencePredictorBoundary = fine-incidence-predictor-boundary
  true false false false false false true

------------------------------------------------------------------------
-- Next predictor residual.
------------------------------------------------------------------------

data FineIncidenceResidual : Set where
  interpolateBetweenCyclicAndRandomIncidence : FineIncidenceResidual
  addTwoHopAndCommonNeighbourFibres : FineIncidenceResidual
  fitRecurrenceComplexityFromStructuralFibrePortfolio : FineIncidenceResidual
  measureFibresOnSameObjectProductionMatrix : FineIncidenceResidual

firstFineIncidenceResidual : FineIncidenceResidual
firstFineIncidenceResidual = interpolateBetweenCyclicAndRandomIncidence

------------------------------------------------------------------------
-- WrongType firewalls.
------------------------------------------------------------------------

data FamilySeparationImpliesExactDegreePredictor : Set where
data StructuralCorrelationImpliesCausation : Set where
data SyntheticPredictorImpliesProductionMeasurement : Set where

familySeparationDoesNotCreateExactDegreePredictor : FamilySeparationImpliesExactDegreePredictor → ⊥
familySeparationDoesNotCreateExactDegreePredictor ()

structuralCorrelationDoesNotCreateCausation : StructuralCorrelationImpliesCausation → ⊥
structuralCorrelationDoesNotCreateCausation ()

syntheticPredictorDoesNotCreateProductionMeasurement : SyntheticPredictorImpliesProductionMeasurement → ⊥
syntheticPredictorDoesNotCreateProductionMeasurement ()
