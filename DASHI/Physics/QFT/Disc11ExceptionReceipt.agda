module DASHI.Physics.QFT.Disc11ExceptionReceipt where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)
open import Data.List.Base using (List; _∷_; [])

------------------------------------------------------------------------
-- D=-11 exception receipt.
--
-- D=-11 is not obtained by a level-overlap rule against the first three
-- quark candidate conductors 3, 4, and 7.  It is retained only by Heegner
-- positional exhaustion: the first three Heegner class-number-1 positions
-- are assigned to the quark candidate block, and the next three positions
-- 8, 11, and 12 form the lepton candidate block.  D=-5 is recorded as not
-- class-number-1 and therefore not an intervening slot.

data Disc11ExceptionStatus : Set where
  heegnerPositionalExhaustionExceptionRecorded :
    Disc11ExceptionStatus

data HeegnerSlotKind : Set where
  quarkCandidateSlot :
    HeegnerSlotKind

  leptonCandidateSlot :
    HeegnerSlotKind

  excludedNonHeegnerSlot :
    HeegnerSlotKind

data Disc11ExceptionBlocker : Set where
  levelOverlapDoesNotClassifyDiscEleven :
    Disc11ExceptionBlocker

  positionalExhaustionIsStructuralOnly :
    Disc11ExceptionBlocker

  exactLeptonSectorNotConstructed :
    Disc11ExceptionBlocker

  exactStandardModelNotConstructed :
    Disc11ExceptionBlocker

  exactGDHRStandardModelMatchNotConstructed :
    Disc11ExceptionBlocker

  terminalUnificationNotConstructed :
    Disc11ExceptionBlocker

canonicalFirstSixHeegnerPositions :
  List Nat
canonicalFirstSixHeegnerPositions =
  3 ∷ 4 ∷ 7 ∷ 8 ∷ 11 ∷ 12 ∷ []

canonicalFirstThreeQuarkPositions :
  List Nat
canonicalFirstThreeQuarkPositions =
  3 ∷ 4 ∷ 7 ∷ []

canonicalNextThreeLeptonPositions :
  List Nat
canonicalNextThreeLeptonPositions =
  8 ∷ 11 ∷ 12 ∷ []

canonicalDisc11ExceptionBlockers :
  List Disc11ExceptionBlocker
canonicalDisc11ExceptionBlockers =
  levelOverlapDoesNotClassifyDiscEleven
  ∷ positionalExhaustionIsStructuralOnly
  ∷ exactLeptonSectorNotConstructed
  ∷ exactStandardModelNotConstructed
  ∷ exactGDHRStandardModelMatchNotConstructed
  ∷ terminalUnificationNotConstructed
  ∷ []

data Disc11ExceptionPromotion : Set where

disc11ExceptionPromotionImpossibleHere :
  Disc11ExceptionPromotion →
  ⊥
disc11ExceptionPromotionImpossibleHere ()

disc11CoprimeAuditLabel : String
disc11CoprimeAuditLabel =
  "D=-11 has level 11 and gcd(11,3)=gcd(11,4)=gcd(11,7)=1, so level-overlap does not classify it"

disc11ExhaustionAuditLabel : String
disc11ExhaustionAuditLabel =
  "D=-11 is retained only by Heegner positional exhaustion as the middle slot of the next-three lepton candidate block 8,11,12"

discMinusFiveAuditLabel : String
discMinusFiveAuditLabel =
  "D=-5 is not class-number-one and is not an intervening Heegner slot"

record HeegnerPositionRow : Set where
  field
    absoluteDiscriminant :
      Nat

    position :
      Nat

    slotKind :
      HeegnerSlotKind

    rowStatement :
      String

open HeegnerPositionRow public

slotDMinusThree :
  HeegnerPositionRow
slotDMinusThree =
  record
    { absoluteDiscriminant =
        3
    ; position =
        1
    ; slotKind =
        quarkCandidateSlot
    ; rowStatement =
        "position 1: D=-3 quark candidate slot"
    }

slotDMinusFour :
  HeegnerPositionRow
slotDMinusFour =
  record
    { absoluteDiscriminant =
        4
    ; position =
        2
    ; slotKind =
        quarkCandidateSlot
    ; rowStatement =
        "position 2: D=-4 quark candidate slot"
    }

slotDMinusSeven :
  HeegnerPositionRow
slotDMinusSeven =
  record
    { absoluteDiscriminant =
        7
    ; position =
        3
    ; slotKind =
        quarkCandidateSlot
    ; rowStatement =
        "position 3: D=-7 quark candidate slot"
    }

slotDMinusEight :
  HeegnerPositionRow
slotDMinusEight =
  record
    { absoluteDiscriminant =
        8
    ; position =
        4
    ; slotKind =
        leptonCandidateSlot
    ; rowStatement =
        "position 4: D=-8 lepton candidate slot"
    }

slotDMinusEleven :
  HeegnerPositionRow
slotDMinusEleven =
  record
    { absoluteDiscriminant =
        11
    ; position =
        5
    ; slotKind =
        leptonCandidateSlot
    ; rowStatement =
        "position 5: D=-11 lepton candidate exception by exhaustion"
    }

slotDMinusTwelve :
  HeegnerPositionRow
slotDMinusTwelve =
  record
    { absoluteDiscriminant =
        12
    ; position =
        6
    ; slotKind =
        leptonCandidateSlot
    ; rowStatement =
        "position 6: D=-12 lepton candidate slot"
    }

discMinusFiveExcludedSlot :
  HeegnerPositionRow
discMinusFiveExcludedSlot =
  record
    { absoluteDiscriminant =
        5
    ; position =
        0
    ; slotKind =
        excludedNonHeegnerSlot
    ; rowStatement =
        "D=-5 excluded: not a class-number-one Heegner discriminant"
    }

canonicalFirstSixPositionRows :
  List HeegnerPositionRow
canonicalFirstSixPositionRows =
  slotDMinusThree
  ∷ slotDMinusFour
  ∷ slotDMinusSeven
  ∷ slotDMinusEight
  ∷ slotDMinusEleven
  ∷ slotDMinusTwelve
  ∷ []

record Disc11ExceptionReceipt : Set where
  field
    status :
      Disc11ExceptionStatus

    statusIsHeegnerPositionalExhaustionExceptionRecorded :
      status ≡ heegnerPositionalExhaustionExceptionRecorded

    firstSixPositionRows :
      List HeegnerPositionRow

    firstSixPositionRowsAreCanonical :
      firstSixPositionRows ≡ canonicalFirstSixPositionRows

    firstSixHeegnerPositions :
      List Nat

    firstSixHeegnerPositionsAreCanonical :
      firstSixHeegnerPositions ≡ canonicalFirstSixHeegnerPositions

    firstThreeQuarkPositions :
      List Nat

    firstThreeQuarkPositionsAreCanonical :
      firstThreeQuarkPositions ≡ canonicalFirstThreeQuarkPositions

    nextThreeLeptonPositions :
      List Nat

    nextThreeLeptonPositionsAreCanonical :
      nextThreeLeptonPositions ≡ canonicalNextThreeLeptonPositions

    discElevenPosition :
      Nat

    discElevenPositionIsFive :
      discElevenPosition ≡ 5

    discElevenLevel :
      Nat

    discElevenLevelIsEleven :
      discElevenLevel ≡ 11

    gcdElevenThree :
      Nat

    gcdElevenThreeIsOne :
      gcdElevenThree ≡ 1

    gcdElevenFour :
      Nat

    gcdElevenFourIsOne :
      gcdElevenFour ≡ 1

    gcdElevenSeven :
      Nat

    gcdElevenSevenIsOne :
      gcdElevenSeven ≡ 1

    discElevenCoprimeToQuarkConductors :
      Bool

    discElevenCoprimeToQuarkConductorsIsTrue :
      discElevenCoprimeToQuarkConductors ≡ true

    levelOverlapClassifiesDiscElevenAsLepton :
      Bool

    levelOverlapClassifiesDiscElevenAsLeptonIsFalse :
      levelOverlapClassifiesDiscElevenAsLepton ≡ false

    firstThreeQuarkSlotsExhausted :
      Bool

    firstThreeQuarkSlotsExhaustedIsTrue :
      firstThreeQuarkSlotsExhausted ≡ true

    nextThreeLeptonCandidateBlockSelected :
      Bool

    nextThreeLeptonCandidateBlockSelectedIsTrue :
      nextThreeLeptonCandidateBlockSelected ≡ true

    discElevenRetainedByPosition :
      Bool

    discElevenRetainedByPositionIsTrue :
      discElevenRetainedByPosition ≡ true

    discMinusFiveExcluded :
      HeegnerPositionRow

    discMinusFiveExcludedIsCanonical :
      discMinusFiveExcluded ≡ discMinusFiveExcludedSlot

    discMinusFiveClassNumberOne :
      Bool

    discMinusFiveClassNumberOneIsFalse :
      discMinusFiveClassNumberOne ≡ false

    coprimeAudit :
      String

    coprimeAuditIsCanonical :
      coprimeAudit ≡ disc11CoprimeAuditLabel

    exhaustionAudit :
      String

    exhaustionAuditIsCanonical :
      exhaustionAudit ≡ disc11ExhaustionAuditLabel

    discMinusFiveAudit :
      String

    discMinusFiveAuditIsCanonical :
      discMinusFiveAudit ≡ discMinusFiveAuditLabel

    structuralCandidateOnly :
      Bool

    structuralCandidateOnlyIsTrue :
      structuralCandidateOnly ≡ true

    exactQuarkSectorPromoted :
      Bool

    exactQuarkSectorPromotedIsFalse :
      exactQuarkSectorPromoted ≡ false

    exactLeptonSectorPromoted :
      Bool

    exactLeptonSectorPromotedIsFalse :
      exactLeptonSectorPromoted ≡ false

    exactStandardModelPromoted :
      Bool

    exactStandardModelPromotedIsFalse :
      exactStandardModelPromoted ≡ false

    gDHREqualsGSMPromoted :
      Bool

    gDHREqualsGSMPromotedIsFalse :
      gDHREqualsGSMPromoted ≡ false

    terminalClaimPromoted :
      Bool

    terminalClaimPromotedIsFalse :
      terminalClaimPromoted ≡ false

    promotionFlags :
      List Disc11ExceptionPromotion

    promotionFlagsAreEmpty :
      promotionFlags ≡ []

    blockers :
      List Disc11ExceptionBlocker

    blockersAreCanonical :
      blockers ≡ canonicalDisc11ExceptionBlockers

    auditTrail :
      List String

open Disc11ExceptionReceipt public

canonicalDisc11ExceptionReceipt :
  Disc11ExceptionReceipt
canonicalDisc11ExceptionReceipt =
  record
    { status =
        heegnerPositionalExhaustionExceptionRecorded
    ; statusIsHeegnerPositionalExhaustionExceptionRecorded =
        refl
    ; firstSixPositionRows =
        canonicalFirstSixPositionRows
    ; firstSixPositionRowsAreCanonical =
        refl
    ; firstSixHeegnerPositions =
        canonicalFirstSixHeegnerPositions
    ; firstSixHeegnerPositionsAreCanonical =
        refl
    ; firstThreeQuarkPositions =
        canonicalFirstThreeQuarkPositions
    ; firstThreeQuarkPositionsAreCanonical =
        refl
    ; nextThreeLeptonPositions =
        canonicalNextThreeLeptonPositions
    ; nextThreeLeptonPositionsAreCanonical =
        refl
    ; discElevenPosition =
        5
    ; discElevenPositionIsFive =
        refl
    ; discElevenLevel =
        11
    ; discElevenLevelIsEleven =
        refl
    ; gcdElevenThree =
        1
    ; gcdElevenThreeIsOne =
        refl
    ; gcdElevenFour =
        1
    ; gcdElevenFourIsOne =
        refl
    ; gcdElevenSeven =
        1
    ; gcdElevenSevenIsOne =
        refl
    ; discElevenCoprimeToQuarkConductors =
        true
    ; discElevenCoprimeToQuarkConductorsIsTrue =
        refl
    ; levelOverlapClassifiesDiscElevenAsLepton =
        false
    ; levelOverlapClassifiesDiscElevenAsLeptonIsFalse =
        refl
    ; firstThreeQuarkSlotsExhausted =
        true
    ; firstThreeQuarkSlotsExhaustedIsTrue =
        refl
    ; nextThreeLeptonCandidateBlockSelected =
        true
    ; nextThreeLeptonCandidateBlockSelectedIsTrue =
        refl
    ; discElevenRetainedByPosition =
        true
    ; discElevenRetainedByPositionIsTrue =
        refl
    ; discMinusFiveExcluded =
        discMinusFiveExcludedSlot
    ; discMinusFiveExcludedIsCanonical =
        refl
    ; discMinusFiveClassNumberOne =
        false
    ; discMinusFiveClassNumberOneIsFalse =
        refl
    ; coprimeAudit =
        disc11CoprimeAuditLabel
    ; coprimeAuditIsCanonical =
        refl
    ; exhaustionAudit =
        disc11ExhaustionAuditLabel
    ; exhaustionAuditIsCanonical =
        refl
    ; discMinusFiveAudit =
        discMinusFiveAuditLabel
    ; discMinusFiveAuditIsCanonical =
        refl
    ; structuralCandidateOnly =
        true
    ; structuralCandidateOnlyIsTrue =
        refl
    ; exactQuarkSectorPromoted =
        false
    ; exactQuarkSectorPromotedIsFalse =
        refl
    ; exactLeptonSectorPromoted =
        false
    ; exactLeptonSectorPromotedIsFalse =
        refl
    ; exactStandardModelPromoted =
        false
    ; exactStandardModelPromotedIsFalse =
        refl
    ; gDHREqualsGSMPromoted =
        false
    ; gDHREqualsGSMPromotedIsFalse =
        refl
    ; terminalClaimPromoted =
        false
    ; terminalClaimPromotedIsFalse =
        refl
    ; promotionFlags =
        []
    ; promotionFlagsAreEmpty =
        refl
    ; blockers =
        canonicalDisc11ExceptionBlockers
    ; blockersAreCanonical =
        refl
    ; auditTrail =
        "First six Heegner positions are 3,4,7,8,11,12"
        ∷ "First three positions 3,4,7 exhaust the quark candidate slots"
        ∷ "D=-11 is position 5, inside the next-three lepton candidate block 8,11,12"
        ∷ "Level overlap fails for D=-11 because gcd(11,3)=gcd(11,4)=gcd(11,7)=1"
        ∷ "D=-5 is not class-number-one and is not an intervening Heegner slot"
        ∷ "Exact quark, exact lepton, exact SM, G_DHR=G_SM, and terminal promotions remain false"
        ∷ []
    }

disc11ExceptionLevelOverlapFalse :
  levelOverlapClassifiesDiscElevenAsLepton canonicalDisc11ExceptionReceipt
  ≡
  false
disc11ExceptionLevelOverlapFalse =
  refl

disc11ExceptionRetainedByPosition :
  discElevenRetainedByPosition canonicalDisc11ExceptionReceipt
  ≡
  true
disc11ExceptionRetainedByPosition =
  refl

disc11ExceptionKeepsExactLeptonFalse :
  exactLeptonSectorPromoted canonicalDisc11ExceptionReceipt
  ≡
  false
disc11ExceptionKeepsExactLeptonFalse =
  refl

disc11ExceptionKeepsExactSMFalse :
  exactStandardModelPromoted canonicalDisc11ExceptionReceipt
  ≡
  false
disc11ExceptionKeepsExactSMFalse =
  refl

disc11ExceptionKeepsGDHRFalse :
  gDHREqualsGSMPromoted canonicalDisc11ExceptionReceipt
  ≡
  false
disc11ExceptionKeepsGDHRFalse =
  refl

disc11ExceptionKeepsTerminalFalse :
  terminalClaimPromoted canonicalDisc11ExceptionReceipt
  ≡
  false
disc11ExceptionKeepsTerminalFalse =
  refl
