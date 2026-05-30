module DASHI.Physics.Closure.NSClayDistanceFinalReceipt where

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)
open import Data.List.Base using (List; _∷_; [])

import DASHI.Physics.Closure.NSLargeDataContractionInputRequest as Input

------------------------------------------------------------------------
-- Final NS Clay distance receipt after H^{11/8}.
--
-- The H^{11/8} route has five inhabited conditional steps.  The only
-- remaining step is the strict large-data contraction inequality for the
-- selected Navier-Stokes iteration on carrier-structured large data:
-- contraction ratio r < 1.  If that input is supplied, the conditional chain
-- closes and implies the Clay Navier-Stokes target.  This receipt records the
-- distance only and keeps actual promotion false.

data NSClayDistance : Set where
  oneContraction :
    NSClayDistance

nsClayDistance : NSClayDistance
nsClayDistance =
  oneContraction

contractionStatement : String
contractionStatement =
  "precisely recorded in NSLargeDataContractionInputRequest"

promotion : Bool
promotion =
  false

data NSClayDistanceStep : Set where
  adjacentOnlyVortexControlInhabited :
    NSClayDistanceStep

  flowPreservationControlInhabited :
    NSClayDistanceStep

  hElevenEighthsDissipationControlInhabited :
    NSClayDistanceStep

  finiteLowFrequencyODESectorInhabited :
    NSClayDistanceStep

  carrierStructuredH118ChainInhabited :
    NSClayDistanceStep

  largeDataContractionRatioMissing :
    NSClayDistanceStep

canonicalConditionalChain :
  List NSClayDistanceStep
canonicalConditionalChain =
  adjacentOnlyVortexControlInhabited
  ∷ flowPreservationControlInhabited
  ∷ hElevenEighthsDissipationControlInhabited
  ∷ finiteLowFrequencyODESectorInhabited
  ∷ carrierStructuredH118ChainInhabited
  ∷ largeDataContractionRatioMissing
  ∷ []

canonicalInhabitedSteps :
  List NSClayDistanceStep
canonicalInhabitedSteps =
  adjacentOnlyVortexControlInhabited
  ∷ flowPreservationControlInhabited
  ∷ hElevenEighthsDissipationControlInhabited
  ∷ finiteLowFrequencyODESectorInhabited
  ∷ carrierStructuredH118ChainInhabited
  ∷ []

canonicalMissingSteps :
  List NSClayDistanceStep
canonicalMissingSteps =
  largeDataContractionRatioMissing
  ∷ []

data NSClayDistanceStatus : Set where
  fiveInhabitedOneContractionMissing :
    NSClayDistanceStatus

data NSClayConditionalImplication : Set where
  closesAndImpliesClayIfContractionSupplied :
    NSClayConditionalImplication

data NSClayDistancePromotion : Set where

nsClayDistancePromotionImpossibleHere :
  NSClayDistancePromotion →
  ⊥
nsClayDistancePromotionImpossibleHere ()

nsClayDistanceStatement : String
nsClayDistanceStatement =
  "After the H^{11/8} carrier chain, the NS Clay distance is oneContraction: five conditional steps are inhabited and one step is missing, namely the strict large-data NS iteration contraction ratio r < 1 for carrier-structured large data. If that inequality is supplied, the chain closes and implies Clay Navier-Stokes. Actual promotion remains false."

requiredContractionInequalityStatement : String
requiredContractionInequalityStatement =
  "Missing step: prove a specific contraction ratio r < 1 for the selected Navier-Stokes Picard/Stokes iteration in H^{11/8}, uniformly on carrier-structured large data."

record NSClayDistanceFinalReceipt : Setω where
  field
    status :
      NSClayDistanceStatus

    statusIsCanonical :
      status ≡ fiveInhabitedOneContractionMissing

    inputRequest :
      Input.NSLargeDataContractionInputRequest

    inputRequestKeepsClayFalse :
      Input.clayNavierStokesPromoted inputRequest ≡ false

    inputRequestContractionTheoremMissing :
      Input.largeDataContractionTheoremConstructed inputRequest ≡ false

    inputRequestH118TargetRecorded :
      Input.hElevenEighthsSobolevTargetRecorded inputRequest ≡ true

    nsClayDistanceField :
      NSClayDistance

    nsClayDistanceFieldIsOneContraction :
      nsClayDistanceField ≡ oneContraction

    nsClayDistanceMarker :
      nsClayDistance ≡ oneContraction

    contractionStatementField :
      String

    contractionStatementFieldIsMarker :
      contractionStatementField ≡ contractionStatement

    contractionStatementMarker :
      contractionStatement
      ≡
      "precisely recorded in NSLargeDataContractionInputRequest"

    conditionalChain :
      List NSClayDistanceStep

    conditionalChainIsCanonical :
      conditionalChain ≡ canonicalConditionalChain

    inhabitedSteps :
      List NSClayDistanceStep

    inhabitedStepsAreCanonical :
      inhabitedSteps ≡ canonicalInhabitedSteps

    inhabitedStepCount :
      Nat

    inhabitedStepCountIsFive :
      inhabitedStepCount ≡ 5

    step1Inhabited :
      Bool

    step1InhabitedIsTrue :
      step1Inhabited ≡ true

    step2Inhabited :
      Bool

    step2InhabitedIsTrue :
      step2Inhabited ≡ true

    step3Inhabited :
      Bool

    step3InhabitedIsTrue :
      step3Inhabited ≡ true

    step4Inhabited :
      Bool

    step4InhabitedIsTrue :
      step4Inhabited ≡ true

    step5Inhabited :
      Bool

    step5InhabitedIsTrue :
      step5Inhabited ≡ true

    missingSteps :
      List NSClayDistanceStep

    missingStepsAreCanonical :
      missingSteps ≡ canonicalMissingSteps

    missingStepCount :
      Nat

    missingStepCountIsOne :
      missingStepCount ≡ 1

    missingStepIsLargeDataContractionRatio :
      Bool

    missingStepIsLargeDataContractionRatioIsTrue :
      missingStepIsLargeDataContractionRatio ≡ true

    hElevenEighthsNumerator :
      Nat

    hElevenEighthsNumeratorIs11 :
      hElevenEighthsNumerator ≡ 11

    hElevenEighthsDenominator :
      Nat

    hElevenEighthsDenominatorIs8 :
      hElevenEighthsDenominator ≡ 8

    carrierStructuredLargeData :
      Bool

    carrierStructuredLargeDataIsTrue :
      carrierStructuredLargeData ≡ true

    selectedNSIteration :
      String

    selectedNSIterationIsPicardStokes :
      selectedNSIteration ≡ "Picard/Stokes"

    contractionRatioSymbol :
      String

    contractionRatioSymbolIsR :
      contractionRatioSymbol ≡ "r"

    contractionInequality :
      String

    contractionInequalityIsRLessThanOne :
      contractionInequality ≡ "r < 1"

    requiredContractionInequality :
      String

    requiredContractionInequalityIsCanonical :
      requiredContractionInequality
      ≡
      requiredContractionInequalityStatement

    largeDataContractionRatioSupplied :
      Bool

    largeDataContractionRatioSuppliedIsFalse :
      largeDataContractionRatioSupplied ≡ false

    conditionalImplication :
      NSClayConditionalImplication

    conditionalImplicationIsCanonical :
      conditionalImplication
      ≡
      closesAndImpliesClayIfContractionSupplied

    chainClosesIfContractionSupplied :
      Bool

    chainClosesIfContractionSuppliedIsTrue :
      chainClosesIfContractionSupplied ≡ true

    impliesClayNSIfChainClosed :
      Bool

    impliesClayNSIfChainClosedIsTrue :
      impliesClayNSIfChainClosed ≡ true

    clayNavierStokesPromoted :
      Bool

    clayNavierStokesPromotedIsFalse :
      clayNavierStokesPromoted ≡ false

    terminalPromotionClaimed :
      Bool

    terminalPromotionClaimedIsFalse :
      terminalPromotionClaimed ≡ false

    promotionField :
      Bool

    promotionFieldIsFalse :
      promotionField ≡ false

    statement :
      String

    statementIsCanonical :
      statement ≡ nsClayDistanceStatement

    promotionFlags :
      List NSClayDistancePromotion

    promotionFlagsAreEmpty :
      promotionFlags ≡ []

    receiptBoundary :
      List String

open NSClayDistanceFinalReceipt public

canonicalNSClayDistanceFinalReceipt :
  NSClayDistanceFinalReceipt
canonicalNSClayDistanceFinalReceipt =
  record
    { status =
        fiveInhabitedOneContractionMissing
    ; statusIsCanonical =
        refl
    ; inputRequest =
        Input.canonicalNSLargeDataContractionInputRequest
    ; inputRequestKeepsClayFalse =
        refl
    ; inputRequestContractionTheoremMissing =
        refl
    ; inputRequestH118TargetRecorded =
        refl
    ; nsClayDistanceField =
        oneContraction
    ; nsClayDistanceFieldIsOneContraction =
        refl
    ; nsClayDistanceMarker =
        refl
    ; contractionStatementField =
        contractionStatement
    ; contractionStatementFieldIsMarker =
        refl
    ; contractionStatementMarker =
        refl
    ; conditionalChain =
        canonicalConditionalChain
    ; conditionalChainIsCanonical =
        refl
    ; inhabitedSteps =
        canonicalInhabitedSteps
    ; inhabitedStepsAreCanonical =
        refl
    ; inhabitedStepCount =
        5
    ; inhabitedStepCountIsFive =
        refl
    ; step1Inhabited =
        true
    ; step1InhabitedIsTrue =
        refl
    ; step2Inhabited =
        true
    ; step2InhabitedIsTrue =
        refl
    ; step3Inhabited =
        true
    ; step3InhabitedIsTrue =
        refl
    ; step4Inhabited =
        true
    ; step4InhabitedIsTrue =
        refl
    ; step5Inhabited =
        true
    ; step5InhabitedIsTrue =
        refl
    ; missingSteps =
        canonicalMissingSteps
    ; missingStepsAreCanonical =
        refl
    ; missingStepCount =
        1
    ; missingStepCountIsOne =
        refl
    ; missingStepIsLargeDataContractionRatio =
        true
    ; missingStepIsLargeDataContractionRatioIsTrue =
        refl
    ; hElevenEighthsNumerator =
        11
    ; hElevenEighthsNumeratorIs11 =
        refl
    ; hElevenEighthsDenominator =
        8
    ; hElevenEighthsDenominatorIs8 =
        refl
    ; carrierStructuredLargeData =
        true
    ; carrierStructuredLargeDataIsTrue =
        refl
    ; selectedNSIteration =
        "Picard/Stokes"
    ; selectedNSIterationIsPicardStokes =
        refl
    ; contractionRatioSymbol =
        "r"
    ; contractionRatioSymbolIsR =
        refl
    ; contractionInequality =
        "r < 1"
    ; contractionInequalityIsRLessThanOne =
        refl
    ; requiredContractionInequality =
        requiredContractionInequalityStatement
    ; requiredContractionInequalityIsCanonical =
        refl
    ; largeDataContractionRatioSupplied =
        false
    ; largeDataContractionRatioSuppliedIsFalse =
        refl
    ; conditionalImplication =
        closesAndImpliesClayIfContractionSupplied
    ; conditionalImplicationIsCanonical =
        refl
    ; chainClosesIfContractionSupplied =
        true
    ; chainClosesIfContractionSuppliedIsTrue =
        refl
    ; impliesClayNSIfChainClosed =
        true
    ; impliesClayNSIfChainClosedIsTrue =
        refl
    ; clayNavierStokesPromoted =
        false
    ; clayNavierStokesPromotedIsFalse =
        refl
    ; terminalPromotionClaimed =
        false
    ; terminalPromotionClaimedIsFalse =
        refl
    ; promotionField =
        promotion
    ; promotionFieldIsFalse =
        refl
    ; statement =
        nsClayDistanceStatement
    ; statementIsCanonical =
        refl
    ; promotionFlags =
        []
    ; promotionFlagsAreEmpty =
        refl
    ; receiptBoundary =
        "NS Clay distance after H^{11/8}: nsClayDistance = oneContraction"
        ∷ "contractionStatement = precisely recorded in NSLargeDataContractionInputRequest"
        ∷ "The conditional chain has five inhabited steps"
        ∷ "The only missing step is the large-data contraction ratio r < 1"
        ∷ "The missing inequality is for the NS Picard/Stokes iteration in H^{11/8} on carrier-structured large data"
        ∷ "If supplied, the chain closes and implies Clay Navier-Stokes"
        ∷ "promotion false"
        ∷ []
    }

canonicalNSClayDistanceIsOneContraction :
  nsClayDistanceField canonicalNSClayDistanceFinalReceipt
  ≡
  oneContraction
canonicalNSClayDistanceIsOneContraction =
  refl

canonicalNSClayDistanceMarker :
  nsClayDistance ≡ oneContraction
canonicalNSClayDistanceMarker =
  refl

canonicalContractionStatementMarker :
  contractionStatement
  ≡
  "precisely recorded in NSLargeDataContractionInputRequest"
canonicalContractionStatementMarker =
  refl

canonicalNSClayDistanceMissingOnlyContraction :
  missingSteps canonicalNSClayDistanceFinalReceipt
  ≡
  largeDataContractionRatioMissing
  ∷ []
canonicalNSClayDistanceMissingOnlyContraction =
  refl

canonicalNSClayDistancePromotionFalse :
  clayNavierStokesPromoted canonicalNSClayDistanceFinalReceipt
  ≡
  false
canonicalNSClayDistancePromotionFalse =
  refl

canonicalNSClayDistanceNoPromotion :
  NSClayDistancePromotion →
  ⊥
canonicalNSClayDistanceNoPromotion =
  nsClayDistancePromotionImpossibleHere
