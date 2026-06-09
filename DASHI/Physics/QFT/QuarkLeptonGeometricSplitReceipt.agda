module DASHI.Physics.QFT.QuarkLeptonGeometricSplitReceipt where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)
open import Data.List.Base using (List; _∷_; [])

------------------------------------------------------------------------
-- Quark/lepton geometric split receipt.
--
-- This receipt records the conductor-level split only.  The first three
-- class-number-1 positions have primitive/modular conductors 3, 4, and 7,
-- and those levels are pairwise coprime.  The next three positions are
-- recorded as lepton-lane candidates with levels 8, 11, and 12: D=-8
-- overlaps the conductor-4 quark lane, D=-12 overlaps the conductor-3 quark
-- lane, and D=-11 is the coprime positional exception.  No quark sector,
-- lepton sector, Standard Model, G_DHR = G_SM, or terminal claim is promoted.

data QuarkLeptonGeometricSplitStatus : Set where
  conductorLevelCoprimalitySplitRecorded :
    QuarkLeptonGeometricSplitStatus

data CandidateLaneKind : Set where
  quarkLaneCandidate :
    CandidateLaneKind

  leptonLaneCandidate :
    CandidateLaneKind

data QuarkLeptonGeometricSplitBlocker : Set where
  exactQuarkSectorNotConstructed :
    QuarkLeptonGeometricSplitBlocker

  exactLeptonSectorNotConstructed :
    QuarkLeptonGeometricSplitBlocker

  discElevenRequiresPositionalException :
    QuarkLeptonGeometricSplitBlocker

  exactStandardModelNotConstructed :
    QuarkLeptonGeometricSplitBlocker

  exactGDHRStandardModelMatchNotConstructed :
    QuarkLeptonGeometricSplitBlocker

  terminalUnificationNotConstructed :
    QuarkLeptonGeometricSplitBlocker

canonicalQuarkLevelConductors :
  List Nat
canonicalQuarkLevelConductors =
  3 ∷ 4 ∷ 7 ∷ []

canonicalLeptonCandidateLevels :
  List Nat
canonicalLeptonCandidateLevels =
  8 ∷ 11 ∷ 12 ∷ []

canonicalQuarkLeptonGeometricSplitBlockers :
  List QuarkLeptonGeometricSplitBlocker
canonicalQuarkLeptonGeometricSplitBlockers =
  exactQuarkSectorNotConstructed
  ∷ exactLeptonSectorNotConstructed
  ∷ discElevenRequiresPositionalException
  ∷ exactStandardModelNotConstructed
  ∷ exactGDHRStandardModelMatchNotConstructed
  ∷ terminalUnificationNotConstructed
  ∷ []

data QuarkLeptonGeometricSplitPromotion : Set where

quarkLeptonGeometricSplitPromotionImpossibleHere :
  QuarkLeptonGeometricSplitPromotion →
  ⊥
quarkLeptonGeometricSplitPromotionImpossibleHere ()

conductorCoprimalitySplitLabel : String
conductorCoprimalitySplitLabel =
  "Conductor-level split: quark candidate levels 3,4,7 are pairwise coprime; lepton candidates 8,11,12 are classified by overlap plus the D=-11 positional exception"

levelOverlapSplitLabel : String
levelOverlapSplitLabel =
  "D=-8 overlaps quark level 4, D=-12 overlaps quark level 3, and D=-11 is coprime to 3,4,7"

record ConductorLevelRow : Set where
  field
    laneKind :
      CandidateLaneKind

    discriminantAbs :
      Nat

    level :
      Nat

    laneStatement :
      String

open ConductorLevelRow public

quarkDMinusThreeConductorRow :
  ConductorLevelRow
quarkDMinusThreeConductorRow =
  record
    { laneKind =
        quarkLaneCandidate
    ; discriminantAbs =
        3
    ; level =
        3
    ; laneStatement =
        "D=-3: quark-lane candidate conductor level 3"
    }

quarkDMinusFourConductorRow :
  ConductorLevelRow
quarkDMinusFourConductorRow =
  record
    { laneKind =
        quarkLaneCandidate
    ; discriminantAbs =
        4
    ; level =
        4
    ; laneStatement =
        "D=-4: quark-lane candidate conductor level 4"
    }

quarkDMinusSevenConductorRow :
  ConductorLevelRow
quarkDMinusSevenConductorRow =
  record
    { laneKind =
        quarkLaneCandidate
    ; discriminantAbs =
        7
    ; level =
        7
    ; laneStatement =
        "D=-7: quark-lane candidate conductor level 7"
    }

leptonDMinusEightConductorRow :
  ConductorLevelRow
leptonDMinusEightConductorRow =
  record
    { laneKind =
        leptonLaneCandidate
    ; discriminantAbs =
        8
    ; level =
        8
    ; laneStatement =
        "D=-8: lepton-lane candidate level 8 with gcd(8,4)=4 overlap"
    }

leptonDMinusElevenConductorRow :
  ConductorLevelRow
leptonDMinusElevenConductorRow =
  record
    { laneKind =
        leptonLaneCandidate
    ; discriminantAbs =
        11
    ; level =
        11
    ; laneStatement =
        "D=-11: lepton-lane positional exception, coprime to 3,4,7"
    }

leptonDMinusTwelveConductorRow :
  ConductorLevelRow
leptonDMinusTwelveConductorRow =
  record
    { laneKind =
        leptonLaneCandidate
    ; discriminantAbs =
        12
    ; level =
        12
    ; laneStatement =
        "D=-12: lepton-lane candidate level 12 with gcd(12,3)=3 overlap"
    }

canonicalQuarkConductorRows :
  List ConductorLevelRow
canonicalQuarkConductorRows =
  quarkDMinusThreeConductorRow
  ∷ quarkDMinusFourConductorRow
  ∷ quarkDMinusSevenConductorRow
  ∷ []

canonicalLeptonConductorRows :
  List ConductorLevelRow
canonicalLeptonConductorRows =
  leptonDMinusEightConductorRow
  ∷ leptonDMinusElevenConductorRow
  ∷ leptonDMinusTwelveConductorRow
  ∷ []

record QuarkLeptonGeometricSplitReceipt : Set where
  field
    status :
      QuarkLeptonGeometricSplitStatus

    statusIsConductorLevelCoprimalitySplitRecorded :
      status ≡ conductorLevelCoprimalitySplitRecorded

    quarkRows :
      List ConductorLevelRow

    quarkRowsAreCanonical :
      quarkRows ≡ canonicalQuarkConductorRows

    leptonRows :
      List ConductorLevelRow

    leptonRowsAreCanonical :
      leptonRows ≡ canonicalLeptonConductorRows

    quarkLevelConductors :
      List Nat

    quarkLevelConductorsAreCanonical :
      quarkLevelConductors ≡ canonicalQuarkLevelConductors

    leptonCandidateLevels :
      List Nat

    leptonCandidateLevelsAreCanonical :
      leptonCandidateLevels ≡ canonicalLeptonCandidateLevels

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

    quarkConductorsPairwiseCoprime :
      Bool

    quarkConductorsPairwiseCoprimeIsTrue :
      quarkConductorsPairwiseCoprime ≡ true

    gcdEightFour :
      Nat

    gcdEightFourIsFour :
      gcdEightFour ≡ 4

    dMinusEightOverlapsConductorFour :
      Bool

    dMinusEightOverlapsConductorFourIsTrue :
      dMinusEightOverlapsConductorFour ≡ true

    gcdTwelveThree :
      Nat

    gcdTwelveThreeIsThree :
      gcdTwelveThree ≡ 3

    dMinusTwelveOverlapsConductorThree :
      Bool

    dMinusTwelveOverlapsConductorThreeIsTrue :
      dMinusTwelveOverlapsConductorThree ≡ true

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

    discElevenPositionalException :
      Bool

    discElevenPositionalExceptionIsTrue :
      discElevenPositionalException ≡ true

    conductorSplitStatement :
      String

    conductorSplitStatementIsCanonical :
      conductorSplitStatement ≡ conductorCoprimalitySplitLabel

    overlapSplitStatement :
      String

    overlapSplitStatementIsCanonical :
      overlapSplitStatement ≡ levelOverlapSplitLabel

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
      List QuarkLeptonGeometricSplitPromotion

    promotionFlagsAreEmpty :
      promotionFlags ≡ []

    blockers :
      List QuarkLeptonGeometricSplitBlocker

    blockersAreCanonical :
      blockers ≡ canonicalQuarkLeptonGeometricSplitBlockers

    auditTrail :
      List String

open QuarkLeptonGeometricSplitReceipt public

canonicalQuarkLeptonGeometricSplitReceipt :
  QuarkLeptonGeometricSplitReceipt
canonicalQuarkLeptonGeometricSplitReceipt =
  record
    { status =
        conductorLevelCoprimalitySplitRecorded
    ; statusIsConductorLevelCoprimalitySplitRecorded =
        refl
    ; quarkRows =
        canonicalQuarkConductorRows
    ; quarkRowsAreCanonical =
        refl
    ; leptonRows =
        canonicalLeptonConductorRows
    ; leptonRowsAreCanonical =
        refl
    ; quarkLevelConductors =
        canonicalQuarkLevelConductors
    ; quarkLevelConductorsAreCanonical =
        refl
    ; leptonCandidateLevels =
        canonicalLeptonCandidateLevels
    ; leptonCandidateLevelsAreCanonical =
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
    ; quarkConductorsPairwiseCoprime =
        true
    ; quarkConductorsPairwiseCoprimeIsTrue =
        refl
    ; gcdEightFour =
        4
    ; gcdEightFourIsFour =
        refl
    ; dMinusEightOverlapsConductorFour =
        true
    ; dMinusEightOverlapsConductorFourIsTrue =
        refl
    ; gcdTwelveThree =
        3
    ; gcdTwelveThreeIsThree =
        refl
    ; dMinusTwelveOverlapsConductorThree =
        true
    ; dMinusTwelveOverlapsConductorThreeIsTrue =
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
    ; discElevenPositionalException =
        true
    ; discElevenPositionalExceptionIsTrue =
        refl
    ; conductorSplitStatement =
        conductorCoprimalitySplitLabel
    ; conductorSplitStatementIsCanonical =
        refl
    ; overlapSplitStatement =
        levelOverlapSplitLabel
    ; overlapSplitStatementIsCanonical =
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
        canonicalQuarkLeptonGeometricSplitBlockers
    ; blockersAreCanonical =
        refl
    ; auditTrail =
        "Quark conductor levels 3,4,7 have gcds 1,1,1"
        ∷ "Lepton candidate level 8 overlaps quark conductor 4 by gcd 4"
        ∷ "Lepton candidate level 12 overlaps quark conductor 3 by gcd 3"
        ∷ "D=-11 has gcd 1 against quark conductors 3,4,7 and is retained only as a positional exception"
        ∷ "Exact quark, exact lepton, exact SM, G_DHR=G_SM, and terminal promotions remain false"
        ∷ []
    }

quarkLeptonSplitQuarkConductorsCoprime :
  quarkConductorsPairwiseCoprime canonicalQuarkLeptonGeometricSplitReceipt
  ≡
  true
quarkLeptonSplitQuarkConductorsCoprime =
  refl

quarkLeptonSplitKeepsExactQuarkFalse :
  exactQuarkSectorPromoted canonicalQuarkLeptonGeometricSplitReceipt
  ≡
  false
quarkLeptonSplitKeepsExactQuarkFalse =
  refl

quarkLeptonSplitKeepsExactLeptonFalse :
  exactLeptonSectorPromoted canonicalQuarkLeptonGeometricSplitReceipt
  ≡
  false
quarkLeptonSplitKeepsExactLeptonFalse =
  refl

quarkLeptonSplitKeepsExactSMFalse :
  exactStandardModelPromoted canonicalQuarkLeptonGeometricSplitReceipt
  ≡
  false
quarkLeptonSplitKeepsExactSMFalse =
  refl

quarkLeptonSplitKeepsGDHRFalse :
  gDHREqualsGSMPromoted canonicalQuarkLeptonGeometricSplitReceipt
  ≡
  false
quarkLeptonSplitKeepsGDHRFalse =
  refl

quarkLeptonSplitKeepsTerminalFalse :
  terminalClaimPromoted canonicalQuarkLeptonGeometricSplitReceipt
  ≡
  false
quarkLeptonSplitKeepsTerminalFalse =
  refl
