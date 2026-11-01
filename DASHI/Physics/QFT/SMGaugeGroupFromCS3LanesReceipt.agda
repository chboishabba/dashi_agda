module DASHI.Physics.QFT.SMGaugeGroupFromCS3LanesReceipt where

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.List.Base using (List; _∷_; [])

import DASHI.Physics.QFT.LevelRankDualityReceipt as LevelRank
import DASHI.Physics.QFT.SMGaugeBosonsFromCSBoundaryReceipt as Bosons
import DASHI.Physics.QFT.SMGaugeGroupCandidateReceipt as GaugeGroup
import DASHI.Physics.QFT.SU3ColourFrom3LanesFusionReceipt as SU3
import DASHI.Physics.QFT.U1YFromCMCharacterReceipt as U1Y

------------------------------------------------------------------------
-- Standard Model gauge-group candidate from three CS lanes.
--
-- This receipt records the U(1)_Y, SU(2)_L, and SU(3)_c candidate sources
-- visible in the current CS-lane bookkeeping.  The SU(2) and SU(3) readings
-- are explicitly marked as arising from common level-rank CS data, so a direct
-- product gauge-group interpretation requires an additional decoupling receipt.
--
-- No exact direct product, exact physical gauge group, exact Standard Model,
-- G_DHR ~= G_SM, or terminal promotion is asserted here.

data SMGaugeCSLaneFactor : Set where
  u1YFromCMCharacter :
    SMGaugeCSLaneFactor

  su2LFromCSWZWBoundary :
    SMGaugeCSLaneFactor

  su3cFromThreeLaneFusion :
    SMGaugeCSLaneFactor

data GaugeLaneSourceStatus : Set where
  candidateSourceOnly :
    GaugeLaneSourceStatus

data DirectProductIndependenceStatus : Set where
  requiresLevelRankDecoupling :
    DirectProductIndependenceStatus

data ExactGaugePromotionStatus : Set where
  notPromoted :
    ExactGaugePromotionStatus

canonicalSMGaugeCSLaneFactors :
  List SMGaugeCSLaneFactor
canonicalSMGaugeCSLaneFactors =
  u1YFromCMCharacter
  ∷ su2LFromCSWZWBoundary
  ∷ su3cFromThreeLaneFusion
  ∷ []

u1YSourceLabel : String
u1YSourceLabel =
  "U(1)_Y candidate source: CM character / hypercharge lane"

su2LSourceLabel : String
su2LSourceLabel =
  "SU(2)_L candidate source: CS/WZW weak-current boundary lane"

su3cSourceLabel : String
su3cSourceLabel =
  "SU(3)_c candidate source: three-lane colour fusion / level-rank colour side"

sharedLevelRankSourceLabel : String
sharedLevelRankSourceLabel =
  "SU(2)_L and SU(3)_c arise from the same level-rank CS data in this receipt"

directProductIndependenceOpenLabel : String
directProductIndependenceOpenLabel =
  "Direct-product independence of SU(2)_L x SU(3)_c requires a decoupling argument not supplied here"

record SMGaugeGroupFromCS3LanesReceipt : Setω where
  field
    u1YReceipt :
      U1Y.U1YFromCMCharacterReceipt

    u1YCandidateFromSource :
      U1Y.U1YFromCMCharacterReceipt.discreteCharacterCandidate u1YReceipt
      ≡
      true

    su2GaugeBosonReceipt :
      Bosons.SMGaugeBosonsFromCSBoundaryReceipt

    su2CandidateFromSource :
      Bosons.SMGaugeBosonsFromCSBoundaryReceipt.wModesCandidate
        su2GaugeBosonReceipt
      ≡
      true

    su3Receipt :
      SU3.SU3ColourFrom3LanesFusionReceipt

    su3CandidateFromSource :
      SU3.SU3ColourFrom3LanesFusionReceipt.su3ColourFromLaneFusionCandidate
        su3Receipt
      ≡
      true

    aggregateGaugeGroupReceipt :
      GaugeGroup.SMGaugeGroupCandidateReceipt

    aggregateCandidateMapIsTrue :
      GaugeGroup.SMGaugeGroupCandidateReceipt.allGaugeFactorsCandidate
        aggregateGaugeGroupReceipt
      ≡
      true

    levelRankReceipt :
      LevelRank.LevelRankDualityReceipt

    sharedLevelRankCandidateIsTrue :
      LevelRank.LevelRankDualityReceipt.su2SpinAndSu3ColourFromSameCMRing
        levelRankReceipt
      ≡
      true

    factors :
      List SMGaugeCSLaneFactor

    factorsAreCanonical :
      factors ≡ canonicalSMGaugeCSLaneFactors

    sourceStatus :
      GaugeLaneSourceStatus

    sourceStatusIsCandidateOnly :
      sourceStatus ≡ candidateSourceOnly

    u1YSourceStatement :
      String

    u1YSourceStatementIsCanonical :
      u1YSourceStatement ≡ u1YSourceLabel

    su2LSourceStatement :
      String

    su2LSourceStatementIsCanonical :
      su2LSourceStatement ≡ su2LSourceLabel

    su3cSourceStatement :
      String

    su3cSourceStatementIsCanonical :
      su3cSourceStatement ≡ su3cSourceLabel

    su2AndSu3ShareLevelRankCSData :
      Bool

    su2AndSu3ShareLevelRankCSDataIsTrue :
      su2AndSu3ShareLevelRankCSData ≡ true

    sharedLevelRankSourceStatement :
      String

    sharedLevelRankSourceStatementIsCanonical :
      sharedLevelRankSourceStatement ≡ sharedLevelRankSourceLabel

    directProductIndependenceStatus :
      DirectProductIndependenceStatus

    directProductIndependenceStatusRequiresDecoupling :
      directProductIndependenceStatus ≡ requiresLevelRankDecoupling

    directProductIndependenceConstructed :
      Bool

    directProductIndependenceConstructedIsFalse :
      directProductIndependenceConstructed ≡ false

    directProductIndependenceBoundary :
      String

    directProductIndependenceBoundaryIsCanonical :
      directProductIndependenceBoundary ≡ directProductIndependenceOpenLabel

    exactDirectProductGaugeGroup :
      Bool

    exactDirectProductGaugeGroupIsFalse :
      exactDirectProductGaugeGroup ≡ false

    exactPhysicalGaugeGroup :
      Bool

    exactPhysicalGaugeGroupIsFalse :
      exactPhysicalGaugeGroup ≡ false

    exactGDHREqualsGSM :
      Bool

    exactGDHREqualsGSMIsFalse :
      exactGDHREqualsGSM ≡ false

    exactStandardModel :
      Bool

    exactStandardModelIsFalse :
      exactStandardModel ≡ false

    exactGaugePromotionStatus :
      ExactGaugePromotionStatus

    exactGaugePromotionStatusIsNotPromoted :
      exactGaugePromotionStatus ≡ notPromoted

    terminalPromotion :
      Bool

    terminalPromotionIsFalse :
      terminalPromotion ≡ false

    receiptBoundary :
      List String

open SMGaugeGroupFromCS3LanesReceipt public

canonicalSMGaugeGroupFromCS3LanesReceipt :
  SMGaugeGroupFromCS3LanesReceipt
canonicalSMGaugeGroupFromCS3LanesReceipt =
  record
    { u1YReceipt =
        U1Y.canonicalU1YFromCMCharacterReceipt
    ; u1YCandidateFromSource =
        refl
    ; su2GaugeBosonReceipt =
        Bosons.canonicalSMGaugeBosonsFromCSBoundaryReceipt
    ; su2CandidateFromSource =
        refl
    ; su3Receipt =
        SU3.canonicalSU3ColourFrom3LanesFusionReceipt
    ; su3CandidateFromSource =
        refl
    ; aggregateGaugeGroupReceipt =
        GaugeGroup.canonicalSMGaugeGroupCandidateReceipt
    ; aggregateCandidateMapIsTrue =
        refl
    ; levelRankReceipt =
        LevelRank.canonicalLevelRankDualityReceipt
    ; sharedLevelRankCandidateIsTrue =
        refl
    ; factors =
        canonicalSMGaugeCSLaneFactors
    ; factorsAreCanonical =
        refl
    ; sourceStatus =
        candidateSourceOnly
    ; sourceStatusIsCandidateOnly =
        refl
    ; u1YSourceStatement =
        u1YSourceLabel
    ; u1YSourceStatementIsCanonical =
        refl
    ; su2LSourceStatement =
        su2LSourceLabel
    ; su2LSourceStatementIsCanonical =
        refl
    ; su3cSourceStatement =
        su3cSourceLabel
    ; su3cSourceStatementIsCanonical =
        refl
    ; su2AndSu3ShareLevelRankCSData =
        true
    ; su2AndSu3ShareLevelRankCSDataIsTrue =
        refl
    ; sharedLevelRankSourceStatement =
        sharedLevelRankSourceLabel
    ; sharedLevelRankSourceStatementIsCanonical =
        refl
    ; directProductIndependenceStatus =
        requiresLevelRankDecoupling
    ; directProductIndependenceStatusRequiresDecoupling =
        refl
    ; directProductIndependenceConstructed =
        false
    ; directProductIndependenceConstructedIsFalse =
        refl
    ; directProductIndependenceBoundary =
        directProductIndependenceOpenLabel
    ; directProductIndependenceBoundaryIsCanonical =
        refl
    ; exactDirectProductGaugeGroup =
        false
    ; exactDirectProductGaugeGroupIsFalse =
        refl
    ; exactPhysicalGaugeGroup =
        false
    ; exactPhysicalGaugeGroupIsFalse =
        refl
    ; exactGDHREqualsGSM =
        false
    ; exactGDHREqualsGSMIsFalse =
        refl
    ; exactStandardModel =
        false
    ; exactStandardModelIsFalse =
        refl
    ; exactGaugePromotionStatus =
        notPromoted
    ; exactGaugePromotionStatusIsNotPromoted =
        refl
    ; terminalPromotion =
        false
    ; terminalPromotionIsFalse =
        refl
    ; receiptBoundary =
        "U1Y, SU2L, and SU3c sources are recorded as candidate gauge data"
        ∷ "SU2L and SU3c are marked as sharing level-rank CS data"
        ∷ "Direct-product independence requires a separate level-rank decoupling argument"
        ∷ "All exact gauge, Standard Model, G_DHR ~= G_SM, and terminal promotions remain false"
        ∷ []
    }

smGaugeCS3LanesSharedLevelRankTrue :
  su2AndSu3ShareLevelRankCSData canonicalSMGaugeGroupFromCS3LanesReceipt
  ≡
  true
smGaugeCS3LanesSharedLevelRankTrue =
  refl

smGaugeCS3LanesDirectProductIndependenceFalse :
  directProductIndependenceConstructed canonicalSMGaugeGroupFromCS3LanesReceipt
  ≡
  false
smGaugeCS3LanesDirectProductIndependenceFalse =
  refl

smGaugeCS3LanesExactDirectProductFalse :
  exactDirectProductGaugeGroup canonicalSMGaugeGroupFromCS3LanesReceipt
  ≡
  false
smGaugeCS3LanesExactDirectProductFalse =
  refl

smGaugeCS3LanesExactSMFalse :
  exactStandardModel canonicalSMGaugeGroupFromCS3LanesReceipt
  ≡
  false
smGaugeCS3LanesExactSMFalse =
  refl
