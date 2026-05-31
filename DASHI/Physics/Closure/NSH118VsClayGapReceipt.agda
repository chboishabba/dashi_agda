module DASHI.Physics.Closure.NSH118VsClayGapReceipt where

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)
open import Data.List.Base using (List; _∷_; [])

import DASHI.Physics.Closure.NSCarrierRegularityThresholdReceipt as Threshold
import DASHI.Physics.Closure.NSCarrierVsClayGapReceipt as Gap

------------------------------------------------------------------------
-- H^{1/18} carrier regularity versus Clay Navier-Stokes gap receipt.
--
-- This receipt records the honest A6 boundary.  A fully rigorous global
-- regularity theorem for all large H^{1/18} Navier-Stokes data would imply
-- the Clay Navier-Stokes smooth-data target, since smooth data is contained
-- in H^{1/18}.  The current A2 -> A3 -> A4 -> A5 carrier chain is still
-- conditional and carrier-structured; its distance to Clay is one rigorous
-- large-data contraction proof for carrier-structured H^{1/18} data.
--
-- No actual Clay promotion is made in this receipt.

data NSH118VsClayGapStatus : Set where
  h118ConditionalCarrierChainRecordedClayPromotionFalse :
    NSH118VsClayGapStatus

data NSH118ConditionalChainStep : Set where
  a2AdjacentOnlyVortexControl :
    NSH118ConditionalChainStep

  a3FlowPreservationControl :
    NSH118ConditionalChainStep

  a4HighFrequencyDissipationControl :
    NSH118ConditionalChainStep

  a5LowFrequencyODEControl :
    NSH118ConditionalChainStep

canonicalNSH118ConditionalChain :
  List NSH118ConditionalChainStep
canonicalNSH118ConditionalChain =
  a2AdjacentOnlyVortexControl
  ∷ a3FlowPreservationControl
  ∷ a4HighFrequencyDissipationControl
  ∷ a5LowFrequencyODEControl
  ∷ []

data NSH118ClayDistance : Set where
  oneProof :
    NSH118ClayDistance

data NSH118RegularityImplicationFlag : Set where
  trueIfProvedForLargeData :
    NSH118RegularityImplicationFlag

data NSH118VsClayPromotion : Set where

nsH118VsClayPromotionImpossibleHere :
  NSH118VsClayPromotion →
  ⊥
nsH118VsClayPromotionImpossibleHere ()

nsH118SobolevNumerator : Nat
nsH118SobolevNumerator =
  1

nsH118SobolevDenominator : Nat
nsH118SobolevDenominator =
  18

nsH118VsClayStatement : String
nsH118VsClayStatement =
  "If global regularity for all large H^{1/18} Navier-Stokes data is fully proved, then it implies Clay Navier-Stokes because smooth data is contained in H^{1/18}. The current A2->A3->A4->A5 carrier chain is conditional; the Clay distance is one rigorous large-data contraction proof for carrier-structured H^{1/18} data. Actual Clay promotion remains false."

record NSH118VsClayGapReceipt : Setω where
  field
    status :
      NSH118VsClayGapStatus

    thresholdReceipt :
      Threshold.NSCarrierRegularityThresholdReceipt

    thresholdReceiptKeepsClayFalse :
      Threshold.clayNavierStokesPromoted thresholdReceipt ≡ false

    thresholdReceiptClaimsNoArbitraryDataPromotion :
      Threshold.arbitraryDataPromotionClaimed thresholdReceipt ≡ false

    carrierVsClayGapReceipt :
      Gap.NSCarrierVsClayGapReceipt

    carrierVsClayGapKeepsClayFalse :
      Gap.clayNavierStokesPromoted carrierVsClayGapReceipt ≡ false

    carrierVsClayGapKeepsTerminalFalse :
      Gap.terminalClayClaimPromoted carrierVsClayGapReceipt ≡ false

    h118Numerator :
      Nat

    h118NumeratorIsOne :
      h118Numerator ≡ nsH118SobolevNumerator

    h118Denominator :
      Nat

    h118DenominatorIsEighteen :
      h118Denominator ≡ nsH118SobolevDenominator

    smoothDataContainedInH118 :
      Bool

    smoothDataContainedInH118IsTrue :
      smoothDataContainedInH118 ≡ true

    largeH118GlobalRegularityFullyProved :
      Bool

    largeH118GlobalRegularityFullyProvedIsFalseHere :
      largeH118GlobalRegularityFullyProved ≡ false

    h118RegularityImpliesClayNS :
      NSH118RegularityImplicationFlag

    h118RegularityImpliesClayNSIsTrueIfProvedForLargeData :
      h118RegularityImpliesClayNS ≡ trueIfProvedForLargeData

    a2ToA5ConditionalChain :
      List NSH118ConditionalChainStep

    a2ToA5ConditionalChainIsCanonical :
      a2ToA5ConditionalChain ≡ canonicalNSH118ConditionalChain

    currentA2ToA5ChainConditional :
      Bool

    currentA2ToA5ChainConditionalIsTrue :
      currentA2ToA5ChainConditional ≡ true

    carrierStructuredH118Data :
      Bool

    carrierStructuredH118DataIsTrue :
      carrierStructuredH118Data ≡ true

    clayDistance :
      NSH118ClayDistance

    nsClayDistance :
      NSH118ClayDistance

    nsClayDistanceIsOneProof :
      nsClayDistance ≡ oneProof

    clayDistanceIsOneProof :
      clayDistance ≡ oneProof

    missingLargeDataContractionProof :
      Bool

    missingLargeDataContractionProofIsTrue :
      missingLargeDataContractionProof ≡ true

    rigorousLargeDataContractionProofForCarrierH118 :
      Bool

    rigorousLargeDataContractionProofForCarrierH118IsFalseHere :
      rigorousLargeDataContractionProofForCarrierH118 ≡ false

    clayNavierStokesPromoted :
      Bool

    clayNavierStokesPromotedIsFalse :
      clayNavierStokesPromoted ≡ false

    terminalClayClaimPromoted :
      Bool

    terminalClayClaimPromotedIsFalse :
      terminalClayClaimPromoted ≡ false

    statement :
      String

    statementIsCanonical :
      statement ≡ nsH118VsClayStatement

    promotionFlags :
      List NSH118VsClayPromotion

    promotionFlagsAreEmpty :
      promotionFlags ≡ []

    receiptBoundary :
      List String

open NSH118VsClayGapReceipt public

canonicalNSH118VsClayGapReceipt :
  NSH118VsClayGapReceipt
canonicalNSH118VsClayGapReceipt =
  record
    { status =
        h118ConditionalCarrierChainRecordedClayPromotionFalse
    ; thresholdReceipt =
        Threshold.canonicalNSCarrierRegularityThresholdReceipt
    ; thresholdReceiptKeepsClayFalse =
        refl
    ; thresholdReceiptClaimsNoArbitraryDataPromotion =
        refl
    ; carrierVsClayGapReceipt =
        Gap.canonicalNSCarrierVsClayGapReceipt
    ; carrierVsClayGapKeepsClayFalse =
        refl
    ; carrierVsClayGapKeepsTerminalFalse =
        refl
    ; h118Numerator =
        nsH118SobolevNumerator
    ; h118NumeratorIsOne =
        refl
    ; h118Denominator =
        nsH118SobolevDenominator
    ; h118DenominatorIsEighteen =
        refl
    ; smoothDataContainedInH118 =
        true
    ; smoothDataContainedInH118IsTrue =
        refl
    ; largeH118GlobalRegularityFullyProved =
        false
    ; largeH118GlobalRegularityFullyProvedIsFalseHere =
        refl
    ; h118RegularityImpliesClayNS =
        trueIfProvedForLargeData
    ; h118RegularityImpliesClayNSIsTrueIfProvedForLargeData =
        refl
    ; a2ToA5ConditionalChain =
        canonicalNSH118ConditionalChain
    ; a2ToA5ConditionalChainIsCanonical =
        refl
    ; currentA2ToA5ChainConditional =
        true
    ; currentA2ToA5ChainConditionalIsTrue =
        refl
    ; carrierStructuredH118Data =
        true
    ; carrierStructuredH118DataIsTrue =
        refl
    ; clayDistance =
        oneProof
    ; nsClayDistance =
        oneProof
    ; nsClayDistanceIsOneProof =
        refl
    ; clayDistanceIsOneProof =
        refl
    ; missingLargeDataContractionProof =
        true
    ; missingLargeDataContractionProofIsTrue =
        refl
    ; rigorousLargeDataContractionProofForCarrierH118 =
        false
    ; rigorousLargeDataContractionProofForCarrierH118IsFalseHere =
        refl
    ; clayNavierStokesPromoted =
        false
    ; clayNavierStokesPromotedIsFalse =
        refl
    ; terminalClayClaimPromoted =
        false
    ; terminalClayClaimPromotedIsFalse =
        refl
    ; statement =
        nsH118VsClayStatement
    ; statementIsCanonical =
        refl
    ; promotionFlags =
        []
    ; promotionFlagsAreEmpty =
        refl
    ; receiptBoundary =
        "h118RegularityImpliesClayNS = true IF proved for large data"
        ∷ "smooth data is contained in H^{1/18}"
        ∷ "largeH118GlobalRegularityFullyProved = false in this receipt"
        ∷ "current A2->A3->A4->A5 chain is conditional"
        ∷ "nsClayDistance = oneProof"
        ∷ "oneProof means one rigorous large-data contraction proof for carrier-structured H^{1/18} data"
        ∷ "rigorousLargeDataContractionProofForCarrierH118 = false in this receipt"
        ∷ "actual Clay promotion remains false"
        ∷ []
    }

canonicalH118RegularityImpliesClayNSFlag :
  h118RegularityImpliesClayNS canonicalNSH118VsClayGapReceipt
  ≡
  trueIfProvedForLargeData
canonicalH118RegularityImpliesClayNSFlag =
  refl

canonicalNSClayDistanceOneProof :
  nsClayDistance canonicalNSH118VsClayGapReceipt ≡ oneProof
canonicalNSClayDistanceOneProof =
  refl

canonicalA2ToA5ChainConditional :
  currentA2ToA5ChainConditional canonicalNSH118VsClayGapReceipt ≡ true
canonicalA2ToA5ChainConditional =
  refl

canonicalNSH118VsClayKeepsClayFalse :
  clayNavierStokesPromoted canonicalNSH118VsClayGapReceipt ≡ false
canonicalNSH118VsClayKeepsClayFalse =
  refl

canonicalNSH118VsClayNoPromotion :
  NSH118VsClayPromotion →
  ⊥
canonicalNSH118VsClayNoPromotion =
  nsH118VsClayPromotionImpossibleHere
