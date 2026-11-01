module DASHI.Physics.Materials.FangDainingInverseDesignHiddenProducerDebtExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.String using (String)

record FangHiddenProducerDebt : Set where
  constructor fang-hidden-producer-debt
  field
    sourceReference : String
    designObjectiveVisible : Bool
    negativeGroupVelocityValidationVisible : Bool
    exactEnergyFunctionalVisible : Bool
    unitCellGeometryVisible : Bool
    materialConstantsVisible : Bool
    computedBandArraysVisible : Bool
    experimentalBandArraysVisible : Bool
    runnableInverseDesignCodeVisible : Bool
    nextProducerLeaf : String

open FangHiddenProducerDebt public

fangHiddenProducerDebt : FangHiddenProducerDebt
fangHiddenProducerDebt = fang-hidden-producer-debt
  "DOI 10.1016/j.jmps.2025.106144"
  true
  true
  false
  false
  false
  false
  false
  false
  "acquire full numerical method/supplement/code: energy functional, cell geometry, constants and computed/experimental bands"

publisherMetadataPaysObjectiveAndValidation : Bool
publisherMetadataPaysObjectiveAndValidation = true

objectiveAndValidationPayExecutableSolver : Bool
objectiveAndValidationPayExecutableSolver = false

hiddenProducerDebtMayBeFilledByAnalogy : Bool
hiddenProducerDebtMayBeFilledByAnalogy = false
