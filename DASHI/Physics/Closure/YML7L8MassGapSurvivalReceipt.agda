module DASHI.Physics.Closure.YML7L8MassGapSurvivalReceipt where

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)
open import Data.List.Base using (List; _∷_; [])

import DASHI.Physics.Closure.LatticeMassGapFromTransferMatrixReceipt as Gap
import DASHI.Physics.Closure.StringTensionCarrierReceipt as StringTension
import DASHI.Physics.Closure.YML6WightmanReconstructionReceipt as L6
import DASHI.Physics.Closure.YML5OSAxiomsForGaugeSectorReceipt as L5
import DASHI.Physics.Closure.YML4ContinuumLimitReceipt as L4
import DASHI.Physics.Closure.YML3TightnessFromKRunningReceipt as L3

data YML7L8MassGapSurvivalStatus : Set where
  massGapSurvivalConditionallyReceiptedDiagnosticOnly :
    YML7L8MassGapSurvivalStatus

data YML7L8MassGapIngredient : Set where
  finiteTransferMatrixGap :
    YML7L8MassGapIngredient
  uniformSpectralGapSurvivalHypothesis :
    YML7L8MassGapIngredient
  wightmanCandidateHamiltonian :
    YML7L8MassGapIngredient
  lambdaCOnePointFiveNineGeV :
    YML7L8MassGapIngredient
  glueballOnePointSevenTwoZeroGeV :
    YML7L8MassGapIngredient
  eightPercentDiagnosticIngredient :
    YML7L8MassGapIngredient

canonicalYML7L8MassGapIngredients :
  List YML7L8MassGapIngredient
canonicalYML7L8MassGapIngredients =
  finiteTransferMatrixGap
  ∷ uniformSpectralGapSurvivalHypothesis
  ∷ wightmanCandidateHamiltonian
  ∷ lambdaCOnePointFiveNineGeV
  ∷ glueballOnePointSevenTwoZeroGeV
  ∷ eightPercentDiagnosticIngredient
  ∷ []

data YML7L8MassGapPromotion : Set where

yml7L8MassGapPromotionImpossibleHere : YML7L8MassGapPromotion → ⊥
yml7L8MassGapPromotionImpossibleHere ()

lambdaCGeVLabel : String
lambdaCGeVLabel = "Lambda_c = 1.59 GeV"

glueballGeVLabel : String
glueballGeVLabel = "0++ glueball = 1.720 GeV"

massGapDiagnosticLabel : String
massGapDiagnosticLabel =
  "relative diagnostic = (1.720 - 1.59) / 1.59 = 0.0818, about 8 percent"

yml7L8MassGapStatement : String
yml7L8MassGapStatement =
  "YML7/L8 records only candidate mass-gap survival for the conditional Wightman YM candidate, still conditional on candidate-only L3, plus an 8 percent scale diagnostic; Clay YM remains false."

record YML7L8MassGapSurvivalReceipt : Setω where
  field
    status :
      YML7L8MassGapSurvivalStatus

    wightmanReceipt :
      L6.YML6WightmanReconstructionReceipt

    wightmanCandidateAvailable :
      L6.wightmanYMCandidateConstructed wightmanReceipt ≡ true

    wightmanKeepsClayFalse :
      L6.clayYangMillsPromoted wightmanReceipt ≡ false

    wightmanPriorL3StillCandidateOnly :
      L3.ymL3TightnessConstructed
        (L4.priorL3Receipt
          (L5.continuumLimitReceipt
            (L6.osReceipt wightmanReceipt)))
        ≡ false

    latticeGapReceipt :
      Gap.LatticeMassGapFromTransferMatrixReceipt

    finiteLatticeGapPositive :
      Gap.finiteLatticeGapPositive latticeGapReceipt ≡ true

    finiteGapDoesNotProveUniformContinuumGap :
      Gap.uniformContinuumGapProved latticeGapReceipt ≡ false

    stringTensionReceipt :
      StringTension.StringTensionCarrierReceipt

    conditionalOnYML6WightmanCandidate :
      Bool
    conditionalOnYML6WightmanCandidateIsTrue :
      conditionalOnYML6WightmanCandidate ≡ true

    uniformSpectralGapSurvivalConditionallyRecorded :
      Bool
    uniformSpectralGapSurvivalConditionallyRecordedIsTrue :
      uniformSpectralGapSurvivalConditionallyRecorded ≡ true

    positiveMassGapForCandidate :
      Bool
    positiveMassGapForCandidateIsTrue :
      positiveMassGapForCandidate ≡ true

    lambdaCGeV :
      String
    lambdaCGeVIsCanonical :
      lambdaCGeV ≡ lambdaCGeVLabel

    glueballMassGeV :
      String
    glueballMassGeVIsCanonical :
      glueballMassGeV ≡ glueballGeVLabel

    eightPercentDiagnosticLabel :
      String
    eightPercentDiagnosticLabelIsCanonical :
      eightPercentDiagnosticLabel ≡ massGapDiagnosticLabel

    massScaleDiagnosticRecorded :
      Bool
    massScaleDiagnosticRecordedIsTrue :
      massScaleDiagnosticRecorded ≡ true

    unconditionalContinuumMassGapPromoted :
      Bool
    unconditionalContinuumMassGapPromotedIsFalse :
      unconditionalContinuumMassGapPromoted ≡ false

    clayYangMillsPromoted :
      Bool
    clayYangMillsPromotedIsFalse :
      clayYangMillsPromoted ≡ false

    terminalClayClaimPromoted :
      Bool
    terminalClayClaimPromotedIsFalse :
      terminalClayClaimPromoted ≡ false

    ingredients :
      List YML7L8MassGapIngredient
    ingredientsAreCanonical :
      ingredients ≡ canonicalYML7L8MassGapIngredients

    statement :
      String
    statementIsCanonical :
      statement ≡ yml7L8MassGapStatement

    promotionFlags :
      List YML7L8MassGapPromotion
    promotionFlagsAreEmpty :
      promotionFlags ≡ []

    receiptBoundary :
      List String

open YML7L8MassGapSurvivalReceipt public

canonicalYML7L8MassGapSurvivalReceipt :
  YML7L8MassGapSurvivalReceipt
canonicalYML7L8MassGapSurvivalReceipt =
  record
    { status = massGapSurvivalConditionallyReceiptedDiagnosticOnly
    ; wightmanReceipt = L6.canonicalYML6WightmanReconstructionReceipt
    ; wightmanCandidateAvailable = refl
    ; wightmanKeepsClayFalse = refl
    ; wightmanPriorL3StillCandidateOnly = refl
    ; latticeGapReceipt = Gap.canonicalLatticeMassGapFromTransferMatrixReceipt
    ; finiteLatticeGapPositive = refl
    ; finiteGapDoesNotProveUniformContinuumGap = refl
    ; stringTensionReceipt = StringTension.canonicalStringTensionCarrierReceipt
    ; conditionalOnYML6WightmanCandidate = true
    ; conditionalOnYML6WightmanCandidateIsTrue = refl
    ; uniformSpectralGapSurvivalConditionallyRecorded = true
    ; uniformSpectralGapSurvivalConditionallyRecordedIsTrue = refl
    ; positiveMassGapForCandidate = true
    ; positiveMassGapForCandidateIsTrue = refl
    ; lambdaCGeV = lambdaCGeVLabel
    ; lambdaCGeVIsCanonical = refl
    ; glueballMassGeV = glueballGeVLabel
    ; glueballMassGeVIsCanonical = refl
    ; eightPercentDiagnosticLabel = massGapDiagnosticLabel
    ; eightPercentDiagnosticLabelIsCanonical = refl
    ; massScaleDiagnosticRecorded = true
    ; massScaleDiagnosticRecordedIsTrue = refl
    ; unconditionalContinuumMassGapPromoted = false
    ; unconditionalContinuumMassGapPromotedIsFalse = refl
    ; clayYangMillsPromoted = false
    ; clayYangMillsPromotedIsFalse = refl
    ; terminalClayClaimPromoted = false
    ; terminalClayClaimPromotedIsFalse = refl
    ; ingredients = canonicalYML7L8MassGapIngredients
    ; ingredientsAreCanonical = refl
    ; statement = yml7L8MassGapStatement
    ; statementIsCanonical = refl
    ; promotionFlags = []
    ; promotionFlagsAreEmpty = refl
    ; receiptBoundary =
        "Finite transfer-matrix positivity is retained, but the existing lattice receipt still does not prove an unconditional continuum gap"
        ∷ "Mass-gap survival is recorded only over the candidate/conditional YML6 Wightman YM candidate"
        ∷ "The YML6 candidate still traces back to candidate-only/blocked L3 tightness"
        ∷ "Lambda_c = 1.59 GeV versus 1.720 GeV glueball is an 8 percent scale diagnostic, not a Clay proof"
        ∷ "No unconditional continuum mass gap, Clay YM, or terminal Clay promotion follows"
        ∷ []
    }

yml7L8MassGapKeepsClayFalse :
  clayYangMillsPromoted canonicalYML7L8MassGapSurvivalReceipt
  ≡ false
yml7L8MassGapKeepsClayFalse = refl

yml7L8MassGapKeepsTerminalFalse :
  terminalClayClaimPromoted canonicalYML7L8MassGapSurvivalReceipt
  ≡ false
yml7L8MassGapKeepsTerminalFalse = refl
