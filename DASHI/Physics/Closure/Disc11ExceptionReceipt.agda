module DASHI.Physics.Closure.Disc11ExceptionReceipt where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)
open import Data.List.Base using (List; _∷_; [])

------------------------------------------------------------------------
-- D=-11 lepton-candidate exception receipt.
--
-- The D=-11 level is coprime to the first three quark candidate levels
-- 3, 4, and 7.  Therefore a level-overlap rule does not classify it as a
-- lepton.  This receipt keeps D=-11 as a lepton candidate only by Heegner
-- position/exhaustion: after the first three pairwise-coprime quark slots
-- are filled, D=-11 sits in the next Heegner candidate band.

data Disc11ExceptionStatus : Set where
  disc11ExceptionRecordedFailClosed :
    Disc11ExceptionStatus

data Disc11ExceptionBlocker : Set where
  levelOverlapDoesNotClassifyDisc11AsLepton :
    Disc11ExceptionBlocker

  leptonByExhaustionIsPositionalOnly :
    Disc11ExceptionBlocker

  noPhysicalLeptonAssignment :
    Disc11ExceptionBlocker

  noStandardModelMatterPromotion :
    Disc11ExceptionBlocker

canonicalDisc11ExceptionBlockers :
  List Disc11ExceptionBlocker
canonicalDisc11ExceptionBlockers =
  levelOverlapDoesNotClassifyDisc11AsLepton
  ∷ leptonByExhaustionIsPositionalOnly
  ∷ noPhysicalLeptonAssignment
  ∷ noStandardModelMatterPromotion
  ∷ []

data Disc11ExceptionPromotion : Set where

disc11ExceptionPromotionImpossibleHere :
  Disc11ExceptionPromotion →
  ⊥
disc11ExceptionPromotionImpossibleHere ()

disc11LevelOverlapAuditLabel : String
disc11LevelOverlapAuditLabel =
  "level 11 is coprime to quark levels 3, 4, and 7; level-overlap does not classify it as lepton"

disc11ExhaustionAuditLabel : String
disc11ExhaustionAuditLabel =
  "D=-11 is kept as a lepton candidate by Heegner position/exhaustion after the first three quark slots"

discMinusFiveAuditLabel : String
discMinusFiveAuditLabel =
  "D=-5 is not class-number-one, so it is not inserted as an intervening Heegner slot"

record Disc11ExceptionReceipt : Set where
  field
    status :
      Disc11ExceptionStatus

    disc11Level :
      Nat

    disc11LevelIsEleven :
      disc11Level ≡ 11

    firstQuarkLevel :
      Nat

    firstQuarkLevelIsThree :
      firstQuarkLevel ≡ 3

    secondQuarkLevel :
      Nat

    secondQuarkLevelIsFour :
      secondQuarkLevel ≡ 4

    thirdQuarkLevel :
      Nat

    thirdQuarkLevelIsSeven :
      thirdQuarkLevel ≡ 7

    gcd11And3 :
      Nat

    gcd11And3IsOne :
      gcd11And3 ≡ 1

    gcd11And4 :
      Nat

    gcd11And4IsOne :
      gcd11And4 ≡ 1

    gcd11And7 :
      Nat

    gcd11And7IsOne :
      gcd11And7 ≡ 1

    disc11CoprimeToAllQuarkLevels :
      Bool

    disc11CoprimeToAllQuarkLevelsIsTrue :
      disc11CoprimeToAllQuarkLevels ≡ true

    levelOverlapClassifiesDisc11AsLepton :
      Bool

    levelOverlapClassifiesDisc11AsLeptonIsFalse :
      levelOverlapClassifiesDisc11AsLepton ≡ false

    coprimeSlotsFilledByThreeQuarks :
      Bool

    coprimeSlotsFilledByThreeQuarksIsTrue :
      coprimeSlotsFilledByThreeQuarks ≡ true

    disc11Exception :
      Bool

    disc11ExceptionIsTrue :
      disc11Exception ≡ true

    disc11IsLeptonByExhaustion :
      Bool

    disc11IsLeptonByExhaustionIsTrue :
      disc11IsLeptonByExhaustion ≡ true

    discMinusFiveNotClassNumberOne :
      Bool

    discMinusFiveNotClassNumberOneIsTrue :
      discMinusFiveNotClassNumberOne ≡ true

    discMinusFiveAudit :
      String

    discMinusFiveAuditIsCanonical :
      discMinusFiveAudit ≡ discMinusFiveAuditLabel

    levelOverlapAudit :
      String

    levelOverlapAuditIsCanonical :
      levelOverlapAudit ≡ disc11LevelOverlapAuditLabel

    exhaustionAudit :
      String

    exhaustionAuditIsCanonical :
      exhaustionAudit ≡ disc11ExhaustionAuditLabel

    physicalLeptonDerived :
      Bool

    physicalLeptonDerivedIsFalse :
      physicalLeptonDerived ≡ false

    smMatterPromoted :
      Bool

    smMatterPromotedIsFalse :
      smMatterPromoted ≡ false

    promotionFlags :
      List Disc11ExceptionPromotion

    promotionFlagsAreEmpty :
      promotionFlags ≡ []

    blockers :
      List Disc11ExceptionBlocker

    blockersAreCanonical :
      blockers ≡ canonicalDisc11ExceptionBlockers

    receiptBoundary :
      List String

open Disc11ExceptionReceipt public

canonicalDisc11ExceptionReceipt :
  Disc11ExceptionReceipt
canonicalDisc11ExceptionReceipt =
  record
    { status =
        disc11ExceptionRecordedFailClosed
    ; disc11Level =
        11
    ; disc11LevelIsEleven =
        refl
    ; firstQuarkLevel =
        3
    ; firstQuarkLevelIsThree =
        refl
    ; secondQuarkLevel =
        4
    ; secondQuarkLevelIsFour =
        refl
    ; thirdQuarkLevel =
        7
    ; thirdQuarkLevelIsSeven =
        refl
    ; gcd11And3 =
        1
    ; gcd11And3IsOne =
        refl
    ; gcd11And4 =
        1
    ; gcd11And4IsOne =
        refl
    ; gcd11And7 =
        1
    ; gcd11And7IsOne =
        refl
    ; disc11CoprimeToAllQuarkLevels =
        true
    ; disc11CoprimeToAllQuarkLevelsIsTrue =
        refl
    ; levelOverlapClassifiesDisc11AsLepton =
        false
    ; levelOverlapClassifiesDisc11AsLeptonIsFalse =
        refl
    ; coprimeSlotsFilledByThreeQuarks =
        true
    ; coprimeSlotsFilledByThreeQuarksIsTrue =
        refl
    ; disc11Exception =
        true
    ; disc11ExceptionIsTrue =
        refl
    ; disc11IsLeptonByExhaustion =
        true
    ; disc11IsLeptonByExhaustionIsTrue =
        refl
    ; discMinusFiveNotClassNumberOne =
        true
    ; discMinusFiveNotClassNumberOneIsTrue =
        refl
    ; discMinusFiveAudit =
        discMinusFiveAuditLabel
    ; discMinusFiveAuditIsCanonical =
        refl
    ; levelOverlapAudit =
        disc11LevelOverlapAuditLabel
    ; levelOverlapAuditIsCanonical =
        refl
    ; exhaustionAudit =
        disc11ExhaustionAuditLabel
    ; exhaustionAuditIsCanonical =
        refl
    ; physicalLeptonDerived =
        false
    ; physicalLeptonDerivedIsFalse =
        refl
    ; smMatterPromoted =
        false
    ; smMatterPromotedIsFalse =
        refl
    ; promotionFlags =
        []
    ; promotionFlagsAreEmpty =
        refl
    ; blockers =
        canonicalDisc11ExceptionBlockers
    ; blockersAreCanonical =
        refl
    ; receiptBoundary =
        "gcd(11,3)=gcd(11,4)=gcd(11,7)=1"
        ∷ "Level-overlap does not classify D=-11 as a lepton candidate"
        ∷ "D=-11 is retained only by Heegner position/exhaustion after the first three pairwise-coprime quark slots"
        ∷ "D=-5 is audited as not class-number-one and is not an intervening Heegner slot"
        ∷ "No physical lepton, Standard Model matter, or promotion flag is constructed"
        ∷ []
    }

disc11ExceptionIsRecorded :
  disc11Exception canonicalDisc11ExceptionReceipt ≡ true
disc11ExceptionIsRecorded =
  refl

disc11LeptonByExhaustionOnly :
  disc11IsLeptonByExhaustion canonicalDisc11ExceptionReceipt ≡ true
disc11LeptonByExhaustionOnly =
  refl

disc11LevelOverlapDoesNotClassifyLepton :
  levelOverlapClassifiesDisc11AsLepton canonicalDisc11ExceptionReceipt
  ≡
  false
disc11LevelOverlapDoesNotClassifyLepton =
  refl

disc11ExceptionNoSMPromotion :
  smMatterPromoted canonicalDisc11ExceptionReceipt ≡ false
disc11ExceptionNoSMPromotion =
  refl
