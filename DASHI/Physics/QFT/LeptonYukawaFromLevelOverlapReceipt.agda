module DASHI.Physics.QFT.LeptonYukawaFromLevelOverlapReceipt where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)
open import Data.List.Base using (List; _∷_; [])

------------------------------------------------------------------------
-- Lepton Yukawa from level-overlap receipt.
--
-- This is a ratio-candidate ledger only.  The level-overlap heuristic
-- records generation-1 lepton overlap 4/8 = 1/2.  The generation-3 lane
-- records the requested volume-ratio candidates: X0(3)/X0(6)=1/3 and
-- X0(4)/X0(12)=1/4, reflecting the D=-12 level/order ambiguity.
-- D=-11 contributes no overlap ratio
-- because it is coprime to 3, 4, and 7 and is handled by positional
-- exhaustion in the companion receipt.

data LeptonYukawaOverlapStatus : Set where
  levelOverlapRatioCandidatesRecorded :
    LeptonYukawaOverlapStatus

data LeptonGenerationCandidate : Set where
  leptonGenerationOneCandidate :
    LeptonGenerationCandidate

  leptonGenerationTwoPositionalException :
    LeptonGenerationCandidate

  leptonGenerationThreeCandidate :
    LeptonGenerationCandidate

data LevelOverlapSource : Set where
  dMinusEightOverConductorFour :
    LevelOverlapSource

  dMinusElevenNoOverlap :
    LevelOverlapSource

  dMinusTwelveOverConductorThree :
    LevelOverlapSource

  dMinusTwelveOverConductorFour :
    LevelOverlapSource

  dMinusTwelveAmbiguousLevelSix :
    LevelOverlapSource

data LeptonYukawaOverlapBlocker : Set where
  ratiosAreCandidateHeuristicOnly :
    LeptonYukawaOverlapBlocker

  missingPhysicalYukawaOperator :
    LeptonYukawaOverlapBlocker

  missingMassRenormalisationScale :
    LeptonYukawaOverlapBlocker

  discElevenHasNoLevelOverlapRatio :
    LeptonYukawaOverlapBlocker

  exactLeptonSectorNotConstructed :
    LeptonYukawaOverlapBlocker

  exactStandardModelNotConstructed :
    LeptonYukawaOverlapBlocker

  exactGDHRStandardModelMatchNotConstructed :
    LeptonYukawaOverlapBlocker

  terminalUnificationNotConstructed :
    LeptonYukawaOverlapBlocker

canonicalLeptonYukawaOverlapBlockers :
  List LeptonYukawaOverlapBlocker
canonicalLeptonYukawaOverlapBlockers =
  ratiosAreCandidateHeuristicOnly
  ∷ missingPhysicalYukawaOperator
  ∷ missingMassRenormalisationScale
  ∷ discElevenHasNoLevelOverlapRatio
  ∷ exactLeptonSectorNotConstructed
  ∷ exactStandardModelNotConstructed
  ∷ exactGDHRStandardModelMatchNotConstructed
  ∷ terminalUnificationNotConstructed
  ∷ []

data LeptonYukawaOverlapPromotion : Set where

leptonYukawaOverlapPromotionImpossibleHere :
  LeptonYukawaOverlapPromotion →
  ⊥
leptonYukawaOverlapPromotionImpossibleHere ()

genOneRatioLabel : String
genOneRatioLabel =
  "generation 1 candidate: D=-8 level 8 overlaps conductor 4, ratio 4/8 = 1/2"

genTwoExceptionLabel : String
genTwoExceptionLabel =
  "generation 2 candidate: D=-11 has no level-overlap Yukawa ratio; positional exception only"

genThreeRatioLabel : String
genThreeRatioLabel =
  "generation 3 candidates: D=-12 records vol(X0(3))/vol(X0(6)) = 1/3 and vol(X0(4))/vol(X0(12)) = 1/4"

ratioBoundaryLabel : String
ratioBoundaryLabel =
  "Level-overlap ratios are structural candidates only; they do not construct lepton Yukawa couplings or physical masses"

record ExactRatio : Set where
  field
    numerator :
      Nat

    denominator :
      Nat

    reducedNumerator :
      Nat

    reducedDenominator :
      Nat

    ratioStatement :
      String

open ExactRatio public

genOneOneHalfRatio :
  ExactRatio
genOneOneHalfRatio =
  record
    { numerator =
        4
    ; denominator =
        8
    ; reducedNumerator =
        1
    ; reducedDenominator =
        2
    ; ratioStatement =
        genOneRatioLabel
    }

genThreeOneQuarterRatio :
  ExactRatio
genThreeOneQuarterRatio =
  record
    { numerator =
        1
    ; denominator =
        4
    ; reducedNumerator =
        1
    ; reducedDenominator =
        4
    ; ratioStatement =
        "generation 3 candidate: vol(X0(4))/vol(X0(12)) = 1/4 from p2 overlap"
    }

genThreeOneThirdRatio :
  ExactRatio
genThreeOneThirdRatio =
  record
    { numerator =
        1
    ; denominator =
        3
    ; reducedNumerator =
        1
    ; reducedDenominator =
        3
    ; ratioStatement =
        "generation 3 candidate: vol(X0(3))/vol(X0(6)) = 1/3 from p3 overlap"
    }

discElevenNoRatio :
  ExactRatio
discElevenNoRatio =
  record
    { numerator =
        0
    ; denominator =
        1
    ; reducedNumerator =
        0
    ; reducedDenominator =
        1
    ; ratioStatement =
        genTwoExceptionLabel
    }

canonicalGenerationThreeCandidateRatios :
  List ExactRatio
canonicalGenerationThreeCandidateRatios =
  genThreeOneThirdRatio
  ∷ genThreeOneQuarterRatio
  ∷ []

record LeptonYukawaOverlapCandidate : Set where
  field
    generation :
      LeptonGenerationCandidate

    source :
      LevelOverlapSource

    discriminantAbs :
      Nat

    leptonLevel :
      Nat

    quarkConductorOverlap :
      Nat

    overlapRatio :
      ExactRatio

    overlapRatioIsCandidate :
      Bool

    overlapRatioIsCandidateIsTrue :
      overlapRatioIsCandidate ≡ true

    promotedPhysicalYukawa :
      Bool

    promotedPhysicalYukawaIsFalse :
      promotedPhysicalYukawa ≡ false

    candidateStatement :
      String

open LeptonYukawaOverlapCandidate public

generationOneLeptonYukawaCandidate :
  LeptonYukawaOverlapCandidate
generationOneLeptonYukawaCandidate =
  record
    { generation =
        leptonGenerationOneCandidate
    ; source =
        dMinusEightOverConductorFour
    ; discriminantAbs =
        8
    ; leptonLevel =
        8
    ; quarkConductorOverlap =
        4
    ; overlapRatio =
        genOneOneHalfRatio
    ; overlapRatioIsCandidate =
        true
    ; overlapRatioIsCandidateIsTrue =
        refl
    ; promotedPhysicalYukawa =
        false
    ; promotedPhysicalYukawaIsFalse =
        refl
    ; candidateStatement =
        genOneRatioLabel
    }

generationTwoLeptonYukawaException :
  LeptonYukawaOverlapCandidate
generationTwoLeptonYukawaException =
  record
    { generation =
        leptonGenerationTwoPositionalException
    ; source =
        dMinusElevenNoOverlap
    ; discriminantAbs =
        11
    ; leptonLevel =
        11
    ; quarkConductorOverlap =
        0
    ; overlapRatio =
        discElevenNoRatio
    ; overlapRatioIsCandidate =
        true
    ; overlapRatioIsCandidateIsTrue =
        refl
    ; promotedPhysicalYukawa =
        false
    ; promotedPhysicalYukawaIsFalse =
        refl
    ; candidateStatement =
        genTwoExceptionLabel
    }

generationThreeLeptonYukawaCandidateOneThird :
  LeptonYukawaOverlapCandidate
generationThreeLeptonYukawaCandidateOneThird =
  record
    { generation =
        leptonGenerationThreeCandidate
    ; source =
        dMinusTwelveOverConductorThree
    ; discriminantAbs =
        12
    ; leptonLevel =
        6
    ; quarkConductorOverlap =
        3
    ; overlapRatio =
        genThreeOneThirdRatio
    ; overlapRatioIsCandidate =
        true
    ; overlapRatioIsCandidateIsTrue =
        refl
    ; promotedPhysicalYukawa =
        false
    ; promotedPhysicalYukawaIsFalse =
        refl
    ; candidateStatement =
        "generation 3 candidate: vol(X0(3))/vol(X0(6)) = 1/3 from p3 overlap"
    }

generationThreeLeptonYukawaCandidateOneQuarter :
  LeptonYukawaOverlapCandidate
generationThreeLeptonYukawaCandidateOneQuarter =
  record
    { generation =
        leptonGenerationThreeCandidate
    ; source =
        dMinusTwelveOverConductorFour
    ; discriminantAbs =
        12
    ; leptonLevel =
        12
    ; quarkConductorOverlap =
        4
    ; overlapRatio =
        genThreeOneQuarterRatio
    ; overlapRatioIsCandidate =
        true
    ; overlapRatioIsCandidateIsTrue =
        refl
    ; promotedPhysicalYukawa =
        false
    ; promotedPhysicalYukawaIsFalse =
        refl
    ; candidateStatement =
        "generation 3 candidate: vol(X0(4))/vol(X0(12)) = 1/4 from p2 overlap"
    }

canonicalLeptonYukawaCandidates :
  List LeptonYukawaOverlapCandidate
canonicalLeptonYukawaCandidates =
  generationOneLeptonYukawaCandidate
  ∷ generationTwoLeptonYukawaException
  ∷ generationThreeLeptonYukawaCandidateOneThird
  ∷ generationThreeLeptonYukawaCandidateOneQuarter
  ∷ []

record LeptonYukawaFromLevelOverlapReceipt : Set where
  field
    status :
      LeptonYukawaOverlapStatus

    statusIsLevelOverlapRatioCandidatesRecorded :
      status ≡ levelOverlapRatioCandidatesRecorded

    candidates :
      List LeptonYukawaOverlapCandidate

    candidatesAreCanonical :
      candidates ≡ canonicalLeptonYukawaCandidates

    generationOneCandidate :
      LeptonYukawaOverlapCandidate

    generationOneCandidateIsCanonical :
      generationOneCandidate ≡ generationOneLeptonYukawaCandidate

    generationOneRatio :
      ExactRatio

    generationOneRatioIsOneHalf :
      generationOneRatio ≡ genOneOneHalfRatio

    generationOneNumeratorIsFour :
      numerator generationOneRatio ≡ 4

    generationOneDenominatorIsEight :
      denominator generationOneRatio ≡ 8

    generationOneReducedNumeratorIsOne :
      reducedNumerator generationOneRatio ≡ 1

    generationOneReducedDenominatorIsTwo :
      reducedDenominator generationOneRatio ≡ 2

    generationTwoException :
      LeptonYukawaOverlapCandidate

    generationTwoExceptionIsCanonical :
      generationTwoException ≡ generationTwoLeptonYukawaException

    generationTwoHasNoOverlap :
      Bool

    generationTwoHasNoOverlapIsTrue :
      generationTwoHasNoOverlap ≡ true

    generationThreeCandidateRatios :
      List ExactRatio

    generationThreeCandidateRatiosAreCanonical :
      generationThreeCandidateRatios ≡ canonicalGenerationThreeCandidateRatios

    generationThreeOneQuarter :
      ExactRatio

    generationThreeOneQuarterIsCanonical :
      generationThreeOneQuarter ≡ genThreeOneQuarterRatio

    generationThreeOneQuarterReducedNumeratorIsOne :
      reducedNumerator generationThreeOneQuarter ≡ 1

    generationThreeOneQuarterReducedDenominatorIsFour :
      reducedDenominator generationThreeOneQuarter ≡ 4

    generationThreeOneThird :
      ExactRatio

    generationThreeOneThirdIsCanonical :
      generationThreeOneThird ≡ genThreeOneThirdRatio

    generationThreeOneThirdReducedNumeratorIsOne :
      reducedNumerator generationThreeOneThird ≡ 1

    generationThreeOneThirdReducedDenominatorIsThree :
      reducedDenominator generationThreeOneThird ≡ 3

    generationThreeHasAmbiguousCandidateSet :
      Bool

    generationThreeHasAmbiguousCandidateSetIsTrue :
      generationThreeHasAmbiguousCandidateSet ≡ true

    ratioBoundary :
      String

    ratioBoundaryIsCanonical :
      ratioBoundary ≡ ratioBoundaryLabel

    generationOneStatement :
      String

    generationOneStatementIsCanonical :
      generationOneStatement ≡ genOneRatioLabel

    generationTwoStatement :
      String

    generationTwoStatementIsCanonical :
      generationTwoStatement ≡ genTwoExceptionLabel

    generationThreeStatement :
      String

    generationThreeStatementIsCanonical :
      generationThreeStatement ≡ genThreeRatioLabel

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
      List LeptonYukawaOverlapPromotion

    promotionFlagsAreEmpty :
      promotionFlags ≡ []

    blockers :
      List LeptonYukawaOverlapBlocker

    blockersAreCanonical :
      blockers ≡ canonicalLeptonYukawaOverlapBlockers

    auditTrail :
      List String

open LeptonYukawaFromLevelOverlapReceipt public

canonicalLeptonYukawaFromLevelOverlapReceipt :
  LeptonYukawaFromLevelOverlapReceipt
canonicalLeptonYukawaFromLevelOverlapReceipt =
  record
    { status =
        levelOverlapRatioCandidatesRecorded
    ; statusIsLevelOverlapRatioCandidatesRecorded =
        refl
    ; candidates =
        canonicalLeptonYukawaCandidates
    ; candidatesAreCanonical =
        refl
    ; generationOneCandidate =
        generationOneLeptonYukawaCandidate
    ; generationOneCandidateIsCanonical =
        refl
    ; generationOneRatio =
        genOneOneHalfRatio
    ; generationOneRatioIsOneHalf =
        refl
    ; generationOneNumeratorIsFour =
        refl
    ; generationOneDenominatorIsEight =
        refl
    ; generationOneReducedNumeratorIsOne =
        refl
    ; generationOneReducedDenominatorIsTwo =
        refl
    ; generationTwoException =
        generationTwoLeptonYukawaException
    ; generationTwoExceptionIsCanonical =
        refl
    ; generationTwoHasNoOverlap =
        true
    ; generationTwoHasNoOverlapIsTrue =
        refl
    ; generationThreeCandidateRatios =
        canonicalGenerationThreeCandidateRatios
    ; generationThreeCandidateRatiosAreCanonical =
        refl
    ; generationThreeOneQuarter =
        genThreeOneQuarterRatio
    ; generationThreeOneQuarterIsCanonical =
        refl
    ; generationThreeOneQuarterReducedNumeratorIsOne =
        refl
    ; generationThreeOneQuarterReducedDenominatorIsFour =
        refl
    ; generationThreeOneThird =
        genThreeOneThirdRatio
    ; generationThreeOneThirdIsCanonical =
        refl
    ; generationThreeOneThirdReducedNumeratorIsOne =
        refl
    ; generationThreeOneThirdReducedDenominatorIsThree =
        refl
    ; generationThreeHasAmbiguousCandidateSet =
        true
    ; generationThreeHasAmbiguousCandidateSetIsTrue =
        refl
    ; ratioBoundary =
        ratioBoundaryLabel
    ; ratioBoundaryIsCanonical =
        refl
    ; generationOneStatement =
        genOneRatioLabel
    ; generationOneStatementIsCanonical =
        refl
    ; generationTwoStatement =
        genTwoExceptionLabel
    ; generationTwoStatementIsCanonical =
        refl
    ; generationThreeStatement =
        genThreeRatioLabel
    ; generationThreeStatementIsCanonical =
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
        canonicalLeptonYukawaOverlapBlockers
    ; blockersAreCanonical =
        refl
    ; auditTrail =
        "Generation 1 level-overlap candidate is exactly 4/8 reduced to 1/2"
        ∷ "Generation 2 D=-11 has no level-overlap ratio and stays positional"
        ∷ "Generation 3 level-overlap candidates are volume ratios X0(3)/X0(6)=1/3 and X0(4)/X0(12)=1/4"
        ∷ "Ratios are structural candidates only, not physical Yukawa couplings or mass predictions"
        ∷ "Exact quark, exact lepton, exact SM, G_DHR=G_SM, and terminal promotions remain false"
        ∷ []
    }

leptonYukawaGenOneIsOneHalf :
  reducedDenominator
    (generationOneRatio canonicalLeptonYukawaFromLevelOverlapReceipt)
  ≡
  2
leptonYukawaGenOneIsOneHalf =
  refl

leptonYukawaGenThreeHasCandidates :
  generationThreeCandidateRatios canonicalLeptonYukawaFromLevelOverlapReceipt
  ≡
  canonicalGenerationThreeCandidateRatios
leptonYukawaGenThreeHasCandidates =
  refl

leptonYukawaKeepsExactLeptonFalse :
  exactLeptonSectorPromoted canonicalLeptonYukawaFromLevelOverlapReceipt
  ≡
  false
leptonYukawaKeepsExactLeptonFalse =
  refl

leptonYukawaKeepsExactSMFalse :
  exactStandardModelPromoted canonicalLeptonYukawaFromLevelOverlapReceipt
  ≡
  false
leptonYukawaKeepsExactSMFalse =
  refl

leptonYukawaKeepsGDHRFalse :
  gDHREqualsGSMPromoted canonicalLeptonYukawaFromLevelOverlapReceipt
  ≡
  false
leptonYukawaKeepsGDHRFalse =
  refl

leptonYukawaKeepsTerminalFalse :
  terminalClaimPromoted canonicalLeptonYukawaFromLevelOverlapReceipt
  ≡
  false
leptonYukawaKeepsTerminalFalse =
  refl
