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
-- H^{11/8} carrier regularity versus Clay Navier-Stokes gap receipt.
--
-- This receipt records the honest A6 boundary.  A fully rigorous global
-- regularity theorem for all large H^{11/8} Navier-Stokes data would imply
-- the Clay Navier-Stokes smooth-data target, since smooth data is contained
-- in H^{11/8}.  LargeDataContractionH11Over8 is recorded here as a
-- Clay-equivalent reformulation of the NS target, not as a subordinate
-- substep.  The current A2 -> A3 -> A4 -> A5 carrier chain is still
-- conditional and carrier-structured.
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
  clayEquivalentReformulation :
    NSH118ClayDistance

data NSH118RegularityImplicationFlag : Set where
  trueIfProvedForLargeData :
    NSH118RegularityImplicationFlag

data NSH118ClayReformulation : Set where
  LargeDataContractionH11Over8 :
    NSH118ClayReformulation

data NSH118EnergyNonClosureReason : Set where
  criticalSobolevH11Over8ToL24 :
    NSH118EnergyNonClosureReason

  serrinPair16Over7And24 :
    NSH118EnergyNonClosureReason

  missingLinftyKatoPonceClosure :
    NSH118EnergyNonClosureReason

canonicalNSH118EnergyNonClosureReasons :
  List NSH118EnergyNonClosureReason
canonicalNSH118EnergyNonClosureReasons =
  criticalSobolevH11Over8ToL24
  ∷ serrinPair16Over7And24
  ∷ missingLinftyKatoPonceClosure
  ∷ []

data NSH118VsClayPromotion : Set where

nsH118VsClayPromotionImpossibleHere :
  NSH118VsClayPromotion →
  ⊥
nsH118VsClayPromotionImpossibleHere ()

nsH118SobolevNumerator : Nat
nsH118SobolevNumerator =
  11

nsH118SobolevDenominator : Nat
nsH118SobolevDenominator =
  8

nsH118VsClayStatement : String
nsH118VsClayStatement =
  "LargeDataContractionH11Over8 is a Clay-equivalent reformulation of Navier-Stokes regularity, not a substep. Energy/H^{11/8} does not close here: H^{11/8}->L24 is critical, the Serrin pair is (16/7,24), and the missing endpoint is an L∞/Kato-Ponce closure. Actual Clay promotion remains false."

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

    h118NumeratorIs11 :
      h118Numerator ≡ nsH118SobolevNumerator

    h118Denominator :
      Nat

    h118DenominatorIs8 :
      h118Denominator ≡ nsH118SobolevDenominator

    clayReformulation :
      NSH118ClayReformulation

    clayReformulationIsLargeDataContractionH11Over8 :
      clayReformulation ≡ LargeDataContractionH11Over8

    largeDataContractionH11Over8IsClayEquivalent :
      Bool

    largeDataContractionH11Over8IsClayEquivalentIsTrue :
      largeDataContractionH11Over8IsClayEquivalent ≡ true

    largeDataContractionH11Over8IsSubstep :
      Bool

    largeDataContractionH11Over8IsSubstepIsFalse :
      largeDataContractionH11Over8IsSubstep ≡ false

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

    nsClayDistanceIsClayEquivalentReformulation :
      nsClayDistance ≡ clayEquivalentReformulation

    clayDistanceIsClayEquivalentReformulation :
      clayDistance ≡ clayEquivalentReformulation

    missingLargeDataContractionProof :
      Bool

    missingLargeDataContractionProofIsTrue :
      missingLargeDataContractionProof ≡ true

    rigorousLargeDataContractionProofForCarrierH118 :
      Bool

    rigorousLargeDataContractionProofForCarrierH118IsFalseHere :
      rigorousLargeDataContractionProofForCarrierH118 ≡ false

    energyH118Closes :
      Bool

    energyH118ClosesIsFalse :
      energyH118Closes ≡ false

    criticalSobolevEmbeddingSpatialExponent :
      Nat

    criticalSobolevEmbeddingSpatialExponentIs24 :
      criticalSobolevEmbeddingSpatialExponent ≡ 24

    serrinTimeNumerator :
      Nat

    serrinTimeNumeratorIs16 :
      serrinTimeNumerator ≡ 16

    serrinTimeDenominator :
      Nat

    serrinTimeDenominatorIs7 :
      serrinTimeDenominator ≡ 7

    serrinSpatialExponent :
      Nat

    serrinSpatialExponentIs24 :
      serrinSpatialExponent ≡ 24

    linftyKatoPonceClosureAvailable :
      Bool

    linftyKatoPonceClosureAvailableIsFalse :
      linftyKatoPonceClosureAvailable ≡ false

    energyNonClosureReasons :
      List NSH118EnergyNonClosureReason

    energyNonClosureReasonsAreCanonical :
      energyNonClosureReasons ≡ canonicalNSH118EnergyNonClosureReasons

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
    ; h118NumeratorIs11 =
        refl
    ; h118Denominator =
        nsH118SobolevDenominator
    ; h118DenominatorIs8 =
        refl
    ; clayReformulation =
        LargeDataContractionH11Over8
    ; clayReformulationIsLargeDataContractionH11Over8 =
        refl
    ; largeDataContractionH11Over8IsClayEquivalent =
        true
    ; largeDataContractionH11Over8IsClayEquivalentIsTrue =
        refl
    ; largeDataContractionH11Over8IsSubstep =
        false
    ; largeDataContractionH11Over8IsSubstepIsFalse =
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
        clayEquivalentReformulation
    ; nsClayDistance =
        clayEquivalentReformulation
    ; nsClayDistanceIsClayEquivalentReformulation =
        refl
    ; clayDistanceIsClayEquivalentReformulation =
        refl
    ; missingLargeDataContractionProof =
        true
    ; missingLargeDataContractionProofIsTrue =
        refl
    ; rigorousLargeDataContractionProofForCarrierH118 =
        false
    ; rigorousLargeDataContractionProofForCarrierH118IsFalseHere =
        refl
    ; energyH118Closes =
        false
    ; energyH118ClosesIsFalse =
        refl
    ; criticalSobolevEmbeddingSpatialExponent =
        24
    ; criticalSobolevEmbeddingSpatialExponentIs24 =
        refl
    ; serrinTimeNumerator =
        16
    ; serrinTimeNumeratorIs16 =
        refl
    ; serrinTimeDenominator =
        7
    ; serrinTimeDenominatorIs7 =
        refl
    ; serrinSpatialExponent =
        24
    ; serrinSpatialExponentIs24 =
        refl
    ; linftyKatoPonceClosureAvailable =
        false
    ; linftyKatoPonceClosureAvailableIsFalse =
        refl
    ; energyNonClosureReasons =
        canonicalNSH118EnergyNonClosureReasons
    ; energyNonClosureReasonsAreCanonical =
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
        ∷ "smooth data is contained in H^{11/8}"
        ∷ "largeH118GlobalRegularityFullyProved = false in this receipt"
        ∷ "current A2->A3->A4->A5 chain is conditional"
        ∷ "LargeDataContractionH11Over8 is Clay-equivalent reformulation, not a substep"
        ∷ "energy/H^{11/8} does not close: critical H^{11/8}->L24"
        ∷ "energy/H^{11/8} does not close: Serrin pair (16/7,24)"
        ∷ "energy/H^{11/8} does not close: missing L∞/Kato-Ponce closure"
        ∷ "nsClayDistance = clayEquivalentReformulation"
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

canonicalNSClayDistanceClayEquivalentReformulation :
  nsClayDistance canonicalNSH118VsClayGapReceipt
  ≡
  clayEquivalentReformulation
canonicalNSClayDistanceClayEquivalentReformulation =
  refl

canonicalLargeDataContractionH11Over8ClayEquivalent :
  largeDataContractionH11Over8IsClayEquivalent
    canonicalNSH118VsClayGapReceipt
  ≡
  true
canonicalLargeDataContractionH11Over8ClayEquivalent =
  refl

canonicalLargeDataContractionH11Over8NotSubstep :
  largeDataContractionH11Over8IsSubstep canonicalNSH118VsClayGapReceipt
  ≡
  false
canonicalLargeDataContractionH11Over8NotSubstep =
  refl

canonicalEnergyH118DoesNotClose :
  energyH118Closes canonicalNSH118VsClayGapReceipt ≡ false
canonicalEnergyH118DoesNotClose =
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
