module DASHI.Physics.Closure.QuarkLeptonGeometricSplitReceipt where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)
open import Data.List.Base using (List; _∷_; [])

------------------------------------------------------------------------
-- Quark/lepton geometric split diagnostic.
--
-- This receipt records a geometric level criterion only.  The quark lane uses
-- the pairwise-coprime small CM levels D=-3 -> 3, D=-4 -> 4, D=-7 -> 7.
-- The lepton lane is recorded with D=-8 -> 8, D=-11 -> 11, and D=-12 with a
-- level-6/12 ambiguity.  The lepton lane overlaps the quark lane at D=-8
-- with level 4 and at D=-12 with level 3, while D=-11 is recorded as the
-- exception.  This is an audit diagnostic only, not a Standard Model matter
-- promotion.

data QuarkLeptonGeometricSplitStatus : Set where
  geometricLevelCriterionRecorded :
    QuarkLeptonGeometricSplitStatus

data QuarkLeptonGeometricSplitBlocker : Set where
  missingPhysicalMatterRepresentationDerivation :
    QuarkLeptonGeometricSplitBlocker

  missingLeptonLevelAmbiguityResolution :
    QuarkLeptonGeometricSplitBlocker

  missingDiscElevenBridge :
    QuarkLeptonGeometricSplitBlocker

canonicalQuarkLeptonGeometricSplitBlockers :
  List QuarkLeptonGeometricSplitBlocker
canonicalQuarkLeptonGeometricSplitBlockers =
  missingPhysicalMatterRepresentationDerivation
  ∷ missingLeptonLevelAmbiguityResolution
  ∷ missingDiscElevenBridge
  ∷ []

data QuarkLeptonGeometricSplitPromotion : Set where

quarkLeptonGeometricSplitPromotionImpossibleHere :
  QuarkLeptonGeometricSplitPromotion →
  ⊥
quarkLeptonGeometricSplitPromotionImpossibleHere ()

quarkLevelSummaryLabel : String
quarkLevelSummaryLabel =
  "quark levels: D=-3 -> 3, D=-4 -> 4, D=-7 -> 7; pairwise coprime"

leptonLevelSummaryLabel : String
leptonLevelSummaryLabel =
  "lepton levels: D=-8 -> 8, D=-11 -> 11, D=-12 -> level 6/12 ambiguity"

levelOverlapSummaryLabel : String
levelOverlapSummaryLabel =
  "lepton overlap diagnostic: D=-8 overlaps quark level 4, D=-12 overlaps quark level 3, D=-11 is the exception"

record QuarkLeptonGeometricSplitReceipt : Set where
  field
    status :
      QuarkLeptonGeometricSplitStatus

    statusIsGeometricLevelCriterionRecorded :
      status ≡ geometricLevelCriterionRecorded

    quarkDMinusThreeLevel :
      Nat

    quarkDMinusThreeLevelIsThree :
      quarkDMinusThreeLevel ≡ 3

    quarkDMinusFourLevel :
      Nat

    quarkDMinusFourLevelIsFour :
      quarkDMinusFourLevel ≡ 4

    quarkDMinusSevenLevel :
      Nat

    quarkDMinusSevenLevelIsSeven :
      quarkDMinusSevenLevel ≡ 7

    gcdThreeFour :
      Nat

    gcdThreeFourIsOne :
      gcdThreeFour ≡ 1

    gcdThreeSeven :
      Nat

    gcdThreeSevenIsOne :
      gcdThreeSeven ≡ 1

    gcdFourSeven :
      Nat

    gcdFourSevenIsOne :
      gcdFourSeven ≡ 1

    quarkLevelsPairwiseCoprime :
      Bool

    quarkLevelsPairwiseCoprimeIsTrue :
      quarkLevelsPairwiseCoprime ≡ true

    quarkLevelSummary :
      String

    quarkLevelSummaryIsCanonical :
      quarkLevelSummary ≡ quarkLevelSummaryLabel

    leptonDMinusEightLevel :
      Nat

    leptonDMinusEightLevelIsEight :
      leptonDMinusEightLevel ≡ 8

    leptonDMinusElevenLevel :
      Nat

    leptonDMinusElevenLevelIsEleven :
      leptonDMinusElevenLevel ≡ 11

    leptonDMinusTwelvePreferredLevel :
      Nat

    leptonDMinusTwelvePreferredLevelIsTwelve :
      leptonDMinusTwelvePreferredLevel ≡ 12

    leptonDMinusTwelveAmbiguousLevel :
      Nat

    leptonDMinusTwelveAmbiguousLevelIsSix :
      leptonDMinusTwelveAmbiguousLevel ≡ 6

    leptonDMinusTwelveAmbiguity :
      String

    leptonDMinusTwelveAmbiguityIsCanonical :
      leptonDMinusTwelveAmbiguity ≡ "D=-12 has level-6/12 ambiguity"

    leptonLevelSummary :
      String

    leptonLevelSummaryIsCanonical :
      leptonLevelSummary ≡ leptonLevelSummaryLabel

    dMinusEightOverlapsQuarkLevelFour :
      Bool

    dMinusEightOverlapsQuarkLevelFourIsTrue :
      dMinusEightOverlapsQuarkLevelFour ≡ true

    dMinusEightOverlapGcdWithFour :
      Nat

    dMinusEightOverlapGcdWithFourIsFour :
      dMinusEightOverlapGcdWithFour ≡ 4

    dMinusTwelveOverlapsQuarkLevelThree :
      Bool

    dMinusTwelveOverlapsQuarkLevelThreeIsTrue :
      dMinusTwelveOverlapsQuarkLevelThree ≡ true

    dMinusTwelveOverlapGcdWithThree :
      Nat

    dMinusTwelveOverlapGcdWithThreeIsThree :
      dMinusTwelveOverlapGcdWithThree ≡ 3

    disc11Exception :
      Bool

    disc11ExceptionIsTrue :
      disc11Exception ≡ true

    disc11ExceptionLevel :
      Nat

    disc11ExceptionLevelIsEleven :
      disc11ExceptionLevel ≡ 11

    levelOverlapSummary :
      String

    levelOverlapSummaryIsCanonical :
      levelOverlapSummary ≡ levelOverlapSummaryLabel

    quarkLeptonPhysicalPromotion :
      Bool

    quarkLeptonPhysicalPromotionIsFalse :
      quarkLeptonPhysicalPromotion ≡ false

    smMatterPromoted :
      Bool

    smMatterPromotedIsFalse :
      smMatterPromoted ≡ false

    blockers :
      List QuarkLeptonGeometricSplitBlocker

    blockersAreCanonical :
      blockers ≡ canonicalQuarkLeptonGeometricSplitBlockers

    promotionFlags :
      List QuarkLeptonGeometricSplitPromotion

    promotionFlagsAreEmpty :
      promotionFlags ≡ []

    auditBoundary :
      List String

open QuarkLeptonGeometricSplitReceipt public

canonicalQuarkLeptonGeometricSplitReceipt :
  QuarkLeptonGeometricSplitReceipt
canonicalQuarkLeptonGeometricSplitReceipt =
  record
    { status =
        geometricLevelCriterionRecorded
    ; statusIsGeometricLevelCriterionRecorded =
        refl
    ; quarkDMinusThreeLevel =
        3
    ; quarkDMinusThreeLevelIsThree =
        refl
    ; quarkDMinusFourLevel =
        4
    ; quarkDMinusFourLevelIsFour =
        refl
    ; quarkDMinusSevenLevel =
        7
    ; quarkDMinusSevenLevelIsSeven =
        refl
    ; gcdThreeFour =
        1
    ; gcdThreeFourIsOne =
        refl
    ; gcdThreeSeven =
        1
    ; gcdThreeSevenIsOne =
        refl
    ; gcdFourSeven =
        1
    ; gcdFourSevenIsOne =
        refl
    ; quarkLevelsPairwiseCoprime =
        true
    ; quarkLevelsPairwiseCoprimeIsTrue =
        refl
    ; quarkLevelSummary =
        quarkLevelSummaryLabel
    ; quarkLevelSummaryIsCanonical =
        refl
    ; leptonDMinusEightLevel =
        8
    ; leptonDMinusEightLevelIsEight =
        refl
    ; leptonDMinusElevenLevel =
        11
    ; leptonDMinusElevenLevelIsEleven =
        refl
    ; leptonDMinusTwelvePreferredLevel =
        12
    ; leptonDMinusTwelvePreferredLevelIsTwelve =
        refl
    ; leptonDMinusTwelveAmbiguousLevel =
        6
    ; leptonDMinusTwelveAmbiguousLevelIsSix =
        refl
    ; leptonDMinusTwelveAmbiguity =
        "D=-12 has level-6/12 ambiguity"
    ; leptonDMinusTwelveAmbiguityIsCanonical =
        refl
    ; leptonLevelSummary =
        leptonLevelSummaryLabel
    ; leptonLevelSummaryIsCanonical =
        refl
    ; dMinusEightOverlapsQuarkLevelFour =
        true
    ; dMinusEightOverlapsQuarkLevelFourIsTrue =
        refl
    ; dMinusEightOverlapGcdWithFour =
        4
    ; dMinusEightOverlapGcdWithFourIsFour =
        refl
    ; dMinusTwelveOverlapsQuarkLevelThree =
        true
    ; dMinusTwelveOverlapsQuarkLevelThreeIsTrue =
        refl
    ; dMinusTwelveOverlapGcdWithThree =
        3
    ; dMinusTwelveOverlapGcdWithThreeIsThree =
        refl
    ; disc11Exception =
        true
    ; disc11ExceptionIsTrue =
        refl
    ; disc11ExceptionLevel =
        11
    ; disc11ExceptionLevelIsEleven =
        refl
    ; levelOverlapSummary =
        levelOverlapSummaryLabel
    ; levelOverlapSummaryIsCanonical =
        refl
    ; quarkLeptonPhysicalPromotion =
        false
    ; quarkLeptonPhysicalPromotionIsFalse =
        refl
    ; smMatterPromoted =
        false
    ; smMatterPromotedIsFalse =
        refl
    ; blockers =
        canonicalQuarkLeptonGeometricSplitBlockers
    ; blockersAreCanonical =
        refl
    ; promotionFlags =
        []
    ; promotionFlagsAreEmpty =
        refl
    ; auditBoundary =
        "quark levels D=-3 -> 3, D=-4 -> 4, D=-7 -> 7 are pairwise coprime"
        ∷ "lepton levels record D=-8 -> 8, D=-11 -> 11, and D=-12 -> 12 with level-6/12 ambiguity"
        ∷ "D=-8 overlaps quark level 4 and D=-12 overlaps quark level 3"
        ∷ "D=-11 is recorded as the exception rather than a promoted matter derivation"
        ∷ "quark/lepton physical promotion and SM matter promotion remain false"
        ∷ []
    }

quarkLeptonGeometricSplitNoPhysicalPromotion :
  quarkLeptonPhysicalPromotion canonicalQuarkLeptonGeometricSplitReceipt
  ≡ false
quarkLeptonGeometricSplitNoPhysicalPromotion =
  refl

quarkLeptonGeometricSplitNoSMMatterPromotion :
  smMatterPromoted canonicalQuarkLeptonGeometricSplitReceipt ≡ false
quarkLeptonGeometricSplitNoSMMatterPromotion =
  refl
