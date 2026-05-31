module DASHI.Physics.Closure.YML7L8MassGapInhabitedReceipt where

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)
open import Data.List.Base using (List; _∷_; [])

import DASHI.Physics.Closure.YML3TightnessFromKRunningReceipt as L3
import DASHI.Physics.Closure.YML7L8MassGapSurvivalReceipt as Survival

data YML7L8MassGapInhabitationStatus : Set where
  candidate :
    YML7L8MassGapInhabitationStatus

  conditionallyInhabited :
    YML7L8MassGapInhabitationStatus

data YML7L8MassGapInhabitationCondition : Set where
  conditionalOnL6 :
    YML7L8MassGapInhabitationCondition

  c3TightnessCandidateOnly :
    YML7L8MassGapInhabitationCondition

  survivalReceiptAvailable :
    YML7L8MassGapInhabitationCondition

  dimensionalTransmutationCarrierEstimateRecorded :
    YML7L8MassGapInhabitationCondition

canonicalYML7L8MassGapInhabitationConditions :
  List YML7L8MassGapInhabitationCondition
canonicalYML7L8MassGapInhabitationConditions =
  conditionalOnL6
  ∷ c3TightnessCandidateOnly
  ∷ survivalReceiptAvailable
  ∷ dimensionalTransmutationCarrierEstimateRecorded
  ∷ []

data YML7L8MassGapInhabitationPromotion : Set where

yml7L8MassGapInhabitationPromotionImpossibleHere :
  YML7L8MassGapInhabitationPromotion →
  ⊥
yml7L8MassGapInhabitationPromotionImpossibleHere ()

physicalMassGapFromDimensionalTransmutationLabel : String
physicalMassGapFromDimensionalTransmutationLabel =
  "1.59 GeV carrier estimate"

glueballMassPDGLabel : String
glueballMassPDGLabel =
  "1.72 GeV"

massGapErrorLabel : String
massGapErrorLabel =
  "7.5pct"

yml7L8MassGapInhabitedStatement : String
yml7L8MassGapInhabitedStatement =
  "YM L7/L8 mass-gap survival target is recorded as conditionalOnL6 and finite-carrier evidence only, with physicalMassGapFromDimensionalTransmutation = 1.59 GeV carrier estimate, glueballMassPDG = 1.72 GeV, and error = 7.5pct; the local L3 receipt remains uninhabited, no operator/infinite-volume convergence is proved, and Clay/terminal promotions remain false."

record YML7L8MassGapInhabitedReceipt : Setω where
  field
    l3TightnessReceipt :
      L3.YML3TightnessFromKRunningReceipt

    c3TightnessCurrentlyUninhabited :
      L3.ymL3TightnessConstructed l3TightnessReceipt ≡ false

    survivalReceipt :
      Survival.YML7L8MassGapSurvivalReceipt

    survivalWasConditionalOnYML6 :
      Survival.conditionalOnYML6WightmanCandidate survivalReceipt ≡ true

    survivalKeepsClayFalse :
      Survival.clayYangMillsPromoted survivalReceipt ≡ false

    survivalKeepsTerminalFalse :
      Survival.terminalClayClaimPromoted survivalReceipt ≡ false

    ymL7L8MassGapSurvival :
      YML7L8MassGapInhabitationCondition

    ymL7L8MassGapSurvivalIsConditionalOnL6 :
      ymL7L8MassGapSurvival ≡ conditionalOnL6

    statusBefore :
      YML7L8MassGapInhabitationStatus

    statusBeforeIsCandidate :
      statusBefore ≡ candidate

    statusAfterCorrection :
      YML7L8MassGapInhabitationStatus

    statusAfterCorrectionIsCandidate :
      statusAfterCorrection ≡ candidate

    physicalMassGapFromDimensionalTransmutation :
      String

    physicalMassGapFromDimensionalTransmutationIsCarrierEstimate :
      physicalMassGapFromDimensionalTransmutation
      ≡ physicalMassGapFromDimensionalTransmutationLabel

    glueballMassPDG :
      String

    glueballMassPDGIsCanonical :
      glueballMassPDG ≡ glueballMassPDGLabel

    error :
      String

    errorIsSevenPointFivePct :
      error ≡ massGapErrorLabel

    physicalMassGapEstimateRecorded :
      Bool

    physicalMassGapEstimateRecordedIsTrue :
      physicalMassGapEstimateRecorded ≡ true

    pdgGlueballComparisonRecorded :
      Bool

    pdgGlueballComparisonRecordedIsTrue :
      pdgGlueballComparisonRecorded ≡ true

    candidateOnly :
      Bool

    candidateOnlyIsTrue :
      candidateOnly ≡ true

    clayYangMillsPromoted :
      Bool

    clayYangMillsPromotedIsFalse :
      clayYangMillsPromoted ≡ false

    terminalClayClaimPromoted :
      Bool

    terminalClayClaimPromotedIsFalse :
      terminalClayClaimPromoted ≡ false

    conditions :
      List YML7L8MassGapInhabitationCondition

    conditionsAreCanonical :
      conditions ≡ canonicalYML7L8MassGapInhabitationConditions

    statement :
      String

    statementIsCanonical :
      statement ≡ yml7L8MassGapInhabitedStatement

    promotionFlags :
      List YML7L8MassGapInhabitationPromotion

    promotionFlagsAreEmpty :
      promotionFlags ≡ []

    receiptBoundary :
      List String

open YML7L8MassGapInhabitedReceipt public

canonicalYML7L8MassGapInhabitedReceipt :
  YML7L8MassGapInhabitedReceipt
canonicalYML7L8MassGapInhabitedReceipt =
  record
    { l3TightnessReceipt =
        L3.canonicalYML3TightnessFromKRunningReceipt
    ; c3TightnessCurrentlyUninhabited =
        refl
    ; survivalReceipt =
        Survival.canonicalYML7L8MassGapSurvivalReceipt
    ; survivalWasConditionalOnYML6 =
        refl
    ; survivalKeepsClayFalse =
        refl
    ; survivalKeepsTerminalFalse =
        refl
    ; ymL7L8MassGapSurvival =
        conditionalOnL6
    ; ymL7L8MassGapSurvivalIsConditionalOnL6 =
        refl
    ; statusBefore =
        candidate
    ; statusBeforeIsCandidate =
        refl
    ; statusAfterCorrection =
        candidate
    ; statusAfterCorrectionIsCandidate =
        refl
    ; physicalMassGapFromDimensionalTransmutation =
        physicalMassGapFromDimensionalTransmutationLabel
    ; physicalMassGapFromDimensionalTransmutationIsCarrierEstimate =
        refl
    ; glueballMassPDG =
        glueballMassPDGLabel
    ; glueballMassPDGIsCanonical =
        refl
    ; error =
        massGapErrorLabel
    ; errorIsSevenPointFivePct =
        refl
    ; physicalMassGapEstimateRecorded =
        true
    ; physicalMassGapEstimateRecordedIsTrue =
        refl
    ; pdgGlueballComparisonRecorded =
        true
    ; pdgGlueballComparisonRecordedIsTrue =
        refl
    ; candidateOnly =
        true
    ; candidateOnlyIsTrue =
        refl
    ; clayYangMillsPromoted =
        false
    ; clayYangMillsPromotedIsFalse =
        refl
    ; terminalClayClaimPromoted =
        false
    ; terminalClayClaimPromotedIsFalse =
        refl
    ; conditions =
        canonicalYML7L8MassGapInhabitationConditions
    ; conditionsAreCanonical =
        refl
    ; statement =
        yml7L8MassGapInhabitedStatement
    ; statementIsCanonical =
        refl
    ; promotionFlags =
        []
    ; promotionFlagsAreEmpty =
        refl
    ; receiptBoundary =
        "ymL7L8MassGapSurvival=conditionalOnL6"
        ∷ "physicalMassGapFromDimensionalTransmutation = 1.59 GeV carrier estimate"
        ∷ "glueballMassPDG = 1.72 GeV"
        ∷ "error = 7.5pct"
        ∷ "Finite carrier spectral gaps and mass-scale diagnostics are evidence only"
        ∷ "status remains candidate because L3 tightness is uninhabited"
        ∷ "No infinite-volume limit or operator/Hamiltonian convergence theorem is proved"
        ∷ "Clay and terminal promotions remain false"
        ∷ []
    }

yml7L8MassGapSurvivalIsConditionalOnL6 :
  ymL7L8MassGapSurvival canonicalYML7L8MassGapInhabitedReceipt
  ≡
  conditionalOnL6
yml7L8MassGapSurvivalIsConditionalOnL6 =
  refl

yml7L8MassGapStatusCandidate :
  statusAfterCorrection canonicalYML7L8MassGapInhabitedReceipt
  ≡
  candidate
yml7L8MassGapStatusCandidate =
  refl

yml7L8MassGapInhabitedKeepsClayFalse :
  clayYangMillsPromoted canonicalYML7L8MassGapInhabitedReceipt
  ≡
  false
yml7L8MassGapInhabitedKeepsClayFalse =
  refl

yml7L8MassGapInhabitedKeepsTerminalFalse :
  terminalClayClaimPromoted canonicalYML7L8MassGapInhabitedReceipt
  ≡
  false
yml7L8MassGapInhabitedKeepsTerminalFalse =
  refl
