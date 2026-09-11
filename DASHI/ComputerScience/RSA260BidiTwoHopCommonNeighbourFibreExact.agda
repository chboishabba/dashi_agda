module DASHI.ComputerScience.RSA260BidiTwoHopCommonNeighbourFibreExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.ComputerScience.RSA260BidiFineIncidenceInterpolationExact as Interpolation
import DASHI.ComputerScience.RSA260BlockWiedemannProductionScaleReconstructionExact as Scale

------------------------------------------------------------------------
-- TWO-HOP / COMMON-NEIGHBOUR STRUCTURAL FIBRES
--
-- The one-hop overlap fibres separate cyclic from fully random carriers, but a
-- one-swap-per-row perturbation changes those means only slightly while moving
-- the shared-generator degree from d=16 to d=65/66.
--
-- This owner therefore derives richer endogenous fibres from A alone:
--   RR = A A^T : row-row common-column counts
--   CC = A^T A : column-column common-row counts
-- together with distribution entropy, ordered distance-two overlap and local
-- two-hop profile-step variation.
--
-- On the base carrier versus eight one-swap carriers:
--   row-common entropy: 5.195... -> 5.758...5.765
--   row distance-2 overlap: 0 -> 0.798...0.834
--   col-common entropy: 5.685... -> 6.543...6.560
--   col two-hop profile-step L1: 541.6 -> 776.2...798.4
-- while the declared kernel consumer remains paid by the prior experiment.
--
-- This is a tested ensemble separation, not a causal mechanism or exact-degree
-- predictor and not a production RSA-260 measurement.
------------------------------------------------------------------------

interpolationBoundary : Interpolation.FineIncidenceFragilityBoundary
interpolationBoundary = Interpolation.canonicalFineIncidenceFragilityBoundary

snowballSourceAtlas : Scale.ProductionScaleSourceAtlas
snowballSourceAtlas = Scale.currentProductionScaleSourceAtlas

snowballIdentityCoordinates : Scale.ProductionScaleIdentityCoordinates
snowballIdentityCoordinates = Scale.currentProductionScaleIdentityCoordinates

record TwoHopRuntimeSource : Set where
  constructor two-hop-runtime-source
  field
    repository : String
    branch : String
    path : String
    commit : String
    gitBlob : String
    sourceEquivalentExecutionPassed : Bool
    exactGitBlobExecuted : Bool
open TwoHopRuntimeSource public

currentTwoHopRuntimeSource : TwoHopRuntimeSource
currentTwoHopRuntimeSource = two-hop-runtime-source
  "chboishabba/dashiRTX"
  "agent/triadic-u8-runtime-oracle"
  "rsa260_bidi_twohop_common_neighbour_fibres.py"
  "38dc39100f7772e47532381499f87d606eb9f9d6"
  "04f49a2094cb324538df9d206f1fb7465c634e8f"
  true false

record TwoHopCommonNeighbourReceipt : Set where
  constructor two-hop-common-neighbour-receipt
  field
    carrierRows : Nat
    carrierColumns : Nat
    baseGeneratorDegree : Nat
    perturbedCarriers : Nat
    perturbedMinimumGeneratorDegree : Nat
    perturbedMaximumGeneratorDegree : Nat
    baseRowCommonEntropy : String
    perturbedRowCommonEntropyMinimum : String
    perturbedRowCommonEntropyMaximum : String
    baseRowDistance2Overlap : String
    perturbedRowDistance2Minimum : String
    perturbedRowDistance2Maximum : String
    baseColumnCommonEntropy : String
    perturbedColumnCommonEntropyMinimum : String
    perturbedColumnCommonEntropyMaximum : String
    baseColumnProfileStepL1 : String
    perturbedColumnProfileStepL1Minimum : String
    perturbedColumnProfileStepL1Maximum : String
open TwoHopCommonNeighbourReceipt public

currentTwoHopCommonNeighbourReceipt : TwoHopCommonNeighbourReceipt
currentTwoHopCommonNeighbourReceipt = two-hop-common-neighbour-receipt
  924 512
  16 8 65 66
  "5.1951779790036365"
  "5.758739218273218" "5.765026574471191"
  "0.0"
  "0.7982646420824295" "0.834056399132321"
  "5.685789985790381"
  "6.543187659882742" "6.560284920562679"
  "541.6086105675147"
  "776.2035225048924" "798.3913894324853"

record TwoHopInterpretationBoundary : Set where
  constructor two-hop-interpretation-boundary
  field
    commonNeighbourFibresSeparateTestedBaseFromOneSwapEnsemble : Bool
    oneHopMeanOverlapWasSufficientForLocalTransition : Bool
    twoHopPortfolioIsExactGeneratorDegreePredictor : Bool
    structuralAssociationIsCausalMechanism : Bool
    fibresMeasuredOnProductionRSA260Matrix : Bool
    DOIOrQIDImportsProof : Bool
open TwoHopInterpretationBoundary public

canonicalTwoHopInterpretationBoundary : TwoHopInterpretationBoundary
canonicalTwoHopInterpretationBoundary = two-hop-interpretation-boundary
  true false false false false false

------------------------------------------------------------------------
-- Next residual.
------------------------------------------------------------------------

data TwoHopResidual : Set where
  fitRecurrenceComplexityFromStructuralFibrePortfolio : TwoHopResidual
  crossValidatePortfolioAcrossRandomAndInterpolatedCarriers : TwoHopResidual
  measurePortfolioOnSameObjectProductionCarrier : TwoHopResidual

firstTwoHopResidual : TwoHopResidual
firstTwoHopResidual = fitRecurrenceComplexityFromStructuralFibrePortfolio

------------------------------------------------------------------------
-- WrongType firewalls.
------------------------------------------------------------------------

data EnsembleSeparationImpliesExactPredictor : Set where
data StructuralAssociationImpliesMechanism : Set where
data SyntheticFibreImpliesProductionMeasurement : Set where

ensembleSeparationDoesNotCreateExactPredictor : EnsembleSeparationImpliesExactPredictor → ⊥
ensembleSeparationDoesNotCreateExactPredictor ()

structuralAssociationDoesNotCreateMechanism : StructuralAssociationImpliesMechanism → ⊥
structuralAssociationDoesNotCreateMechanism ()

syntheticFibreDoesNotCreateProductionMeasurement : SyntheticFibreImpliesProductionMeasurement → ⊥
syntheticFibreDoesNotCreateProductionMeasurement ()
