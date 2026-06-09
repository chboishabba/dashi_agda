module DASHI.Physics.QFT.LeptonSectorGapReceipt where

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)
open import Data.List.Base using (List; _∷_; [])

import DASHI.Physics.Moonshine.HeegnerLaneAssignmentReceipt as Heegner
import DASHI.Physics.QFT.ConductorLevelCorrespondenceReceipt as Conductor

------------------------------------------------------------------------
-- Lepton-sector gap receipt.
--
-- This receipt records the next small class-number-1 discriminants after
-- the active p2/p3/p5 CM window.  The active window is still {-4,-3,-7}.
-- The next inspected discriminants -8, -11, and -12 are only lepton-lane
-- candidates.  The -8 row is no longer treated as a conductor-four
-- collision: it is the maximal order row with field discriminant -8 and
-- modular/character level 8.  The -8, -11, and -12 rows all remain open
-- candidates.  No lepton sector or exact SM promotion is constructed.

data ClassNumberOneDiscriminant : Set where
  D-3 :
    ClassNumberOneDiscriminant

  D-4 :
    ClassNumberOneDiscriminant

  D-7 :
    ClassNumberOneDiscriminant

  D-8 :
    ClassNumberOneDiscriminant

  D-11 :
    ClassNumberOneDiscriminant

  D-12 :
    ClassNumberOneDiscriminant

  D-16 :
    ClassNumberOneDiscriminant

  D-19 :
    ClassNumberOneDiscriminant

  D-27 :
    ClassNumberOneDiscriminant

  D-28 :
    ClassNumberOneDiscriminant

  D-43 :
    ClassNumberOneDiscriminant

  D-67 :
    ClassNumberOneDiscriminant

  D-163 :
    ClassNumberOneDiscriminant

canonicalClassNumberOneDiscriminants :
  List ClassNumberOneDiscriminant
canonicalClassNumberOneDiscriminants =
  D-3
  ∷ D-4
  ∷ D-7
  ∷ D-8
  ∷ D-11
  ∷ D-12
  ∷ D-16
  ∷ D-19
  ∷ D-27
  ∷ D-28
  ∷ D-43
  ∷ D-67
  ∷ D-163
  ∷ []

activePrimeLaneDiscriminants :
  List ClassNumberOneDiscriminant
activePrimeLaneDiscriminants =
  D-4
  ∷ D-3
  ∷ D-7
  ∷ []

nextLeptonLaneCandidateDiscriminants :
  List ClassNumberOneDiscriminant
nextLeptonLaneCandidateDiscriminants =
  D-8
  ∷ D-11
  ∷ D-12
  ∷ []

classNumberOneDiscriminantAbs :
  ClassNumberOneDiscriminant →
  Nat
classNumberOneDiscriminantAbs D-3 =
  3
classNumberOneDiscriminantAbs D-4 =
  4
classNumberOneDiscriminantAbs D-7 =
  7
classNumberOneDiscriminantAbs D-8 =
  8
classNumberOneDiscriminantAbs D-11 =
  11
classNumberOneDiscriminantAbs D-12 =
  12
classNumberOneDiscriminantAbs D-16 =
  16
classNumberOneDiscriminantAbs D-19 =
  19
classNumberOneDiscriminantAbs D-27 =
  27
classNumberOneDiscriminantAbs D-28 =
  28
classNumberOneDiscriminantAbs D-43 =
  43
classNumberOneDiscriminantAbs D-67 =
  67
classNumberOneDiscriminantAbs D-163 =
  163

classNumberOneDiscriminantLabel :
  ClassNumberOneDiscriminant →
  String
classNumberOneDiscriminantLabel D-3 =
  "D=-3"
classNumberOneDiscriminantLabel D-4 =
  "D=-4"
classNumberOneDiscriminantLabel D-7 =
  "D=-7"
classNumberOneDiscriminantLabel D-8 =
  "D=-8"
classNumberOneDiscriminantLabel D-11 =
  "D=-11"
classNumberOneDiscriminantLabel D-12 =
  "D=-12"
classNumberOneDiscriminantLabel D-16 =
  "D=-16"
classNumberOneDiscriminantLabel D-19 =
  "D=-19"
classNumberOneDiscriminantLabel D-27 =
  "D=-27"
classNumberOneDiscriminantLabel D-28 =
  "D=-28"
classNumberOneDiscriminantLabel D-43 =
  "D=-43"
classNumberOneDiscriminantLabel D-67 =
  "D=-67"
classNumberOneDiscriminantLabel D-163 =
  "D=-163"

data LeptonLaneCandidateStatus : Set where
  leptonLaneCandidateOpen :
    LeptonLaneCandidateStatus

data LeptonSectorGapBlocker : Set where
  dMinusEightLevelEightCandidateStillUnconstructed :
    LeptonSectorGapBlocker

  dMinusElevenHasNoLeptonSectorConstruction :
    LeptonSectorGapBlocker

  dMinusTwelveHasNoLeptonSectorConstruction :
    LeptonSectorGapBlocker

  missingExactLeptonRepresentationTable :
    LeptonSectorGapBlocker

  missingExactDHRToSMLeptonFunctor :
    LeptonSectorGapBlocker

canonicalLeptonSectorGapBlockers :
  List LeptonSectorGapBlocker
canonicalLeptonSectorGapBlockers =
  dMinusEightLevelEightCandidateStillUnconstructed
  ∷ dMinusElevenHasNoLeptonSectorConstruction
  ∷ dMinusTwelveHasNoLeptonSectorConstruction
  ∷ missingExactLeptonRepresentationTable
  ∷ missingExactDHRToSMLeptonFunctor
  ∷ []

data LeptonSectorPromotionFlag : Set where

leptonSectorPromotionFlagImpossibleHere :
  LeptonSectorPromotionFlag →
  ⊥
leptonSectorPromotionFlagImpossibleHere ()

leptonSectorGapBoundaryLabel : String
leptonSectorGapBoundaryLabel =
  "Lepton sector remains absent/open: -8 is corrected to field discriminant -8 with modular level 8, while -11 and -12 are also only lepton-lane candidates"

classNumberOneDiscriminantListLabel : String
classNumberOneDiscriminantListLabel =
  "Class-number-1 discriminant list recorded here: -3,-4,-7,-8,-11,-12,-16,-19,-27,-28,-43,-67,-163"

record LeptonLaneCandidate : Set where
  field
    discriminant :
      ClassNumberOneDiscriminant

    discriminantLabel :
      String

    discriminantLabelIsCanonical :
      discriminantLabel ≡ classNumberOneDiscriminantLabel discriminant

    candidateConductor :
      Nat

    status :
      LeptonLaneCandidateStatus

    statusStatement :
      String

open LeptonLaneCandidate public

dMinusEightLeptonLaneCandidate :
  LeptonLaneCandidate
dMinusEightLeptonLaneCandidate =
  record
    { discriminant =
        D-8
    ; discriminantLabel =
        "D=-8"
    ; discriminantLabelIsCanonical =
        refl
    ; candidateConductor =
        8
    ; status =
        leptonLaneCandidateOpen
    ; statusStatement =
        "D=-8 candidate is corrected to modular/character level 8; it remains open because no lepton sector is constructed"
    }

dMinusElevenLeptonLaneCandidate :
  LeptonLaneCandidate
dMinusElevenLeptonLaneCandidate =
  record
    { discriminant =
        D-11
    ; discriminantLabel =
        "D=-11"
    ; discriminantLabelIsCanonical =
        refl
    ; candidateConductor =
        11
    ; status =
        leptonLaneCandidateOpen
    ; statusStatement =
        "D=-11 is recorded as an open lepton-lane candidate"
    }

dMinusTwelveLeptonLaneCandidate :
  LeptonLaneCandidate
dMinusTwelveLeptonLaneCandidate =
  record
    { discriminant =
        D-12
    ; discriminantLabel =
        "D=-12"
    ; discriminantLabelIsCanonical =
        refl
    ; candidateConductor =
        12
    ; status =
        leptonLaneCandidateOpen
    ; statusStatement =
        "D=-12 is recorded as an open lepton-lane candidate"
    }

canonicalLeptonLaneCandidates :
  List LeptonLaneCandidate
canonicalLeptonLaneCandidates =
  dMinusEightLeptonLaneCandidate
  ∷ dMinusElevenLeptonLaneCandidate
  ∷ dMinusTwelveLeptonLaneCandidate
  ∷ []

record LeptonSectorGapReceipt : Setω where
  field
    heegnerLaneAssignmentReceipt :
      Heegner.HeegnerLaneAssignmentReceipt

    conductorLevelCorrespondenceReceipt :
      Conductor.ConductorLevelCorrespondenceReceipt

    classNumberOneDiscriminants :
      List ClassNumberOneDiscriminant

    classNumberOneDiscriminantsAreCanonical :
      classNumberOneDiscriminants
      ≡
      canonicalClassNumberOneDiscriminants

    classNumberOneDiscriminantListStatement :
      String

    classNumberOneDiscriminantListStatementIsCanonical :
      classNumberOneDiscriminantListStatement
      ≡
      classNumberOneDiscriminantListLabel

    activeDiscriminants :
      List ClassNumberOneDiscriminant

    activeDiscriminantsArePrimeLaneWindow :
      activeDiscriminants ≡ activePrimeLaneDiscriminants

    nextLeptonCandidateDiscriminants :
      List ClassNumberOneDiscriminant

    nextLeptonCandidateDiscriminantsAreCanonical :
      nextLeptonCandidateDiscriminants
      ≡
      nextLeptonLaneCandidateDiscriminants

    leptonLaneCandidates :
      List LeptonLaneCandidate

    leptonLaneCandidatesAreCanonical :
      leptonLaneCandidates ≡ canonicalLeptonLaneCandidates

    dMinusEightCandidate :
      LeptonLaneCandidate

    dMinusEightCandidateIsCanonical :
      dMinusEightCandidate ≡ dMinusEightLeptonLaneCandidate

    dMinusEightDiscriminantIsMinusEight :
      discriminant dMinusEightCandidate ≡ D-8

    dMinusEightCandidateLevelIsEight :
      candidateConductor dMinusEightCandidate ≡ 8

    p2LaneConductor :
      Nat

    p2LaneConductorIsFour :
      p2LaneConductor ≡ 4

    dMinusEightConductorConflictsWithP2Lane :
      Bool

    dMinusEightConductorConflictsWithP2LaneIsFalse :
      dMinusEightConductorConflictsWithP2Lane ≡ false

    dMinusEightStatusIsOpenCandidate :
      status dMinusEightCandidate
      ≡
      leptonLaneCandidateOpen

    dMinusElevenCandidate :
      LeptonLaneCandidate

    dMinusElevenCandidateIsCanonical :
      dMinusElevenCandidate ≡ dMinusElevenLeptonLaneCandidate

    dMinusElevenDiscriminantIsMinusEleven :
      discriminant dMinusElevenCandidate ≡ D-11

    dMinusElevenStatusIsOpenCandidate :
      status dMinusElevenCandidate ≡ leptonLaneCandidateOpen

    dMinusTwelveCandidate :
      LeptonLaneCandidate

    dMinusTwelveCandidateIsCanonical :
      dMinusTwelveCandidate ≡ dMinusTwelveLeptonLaneCandidate

    dMinusTwelveDiscriminantIsMinusTwelve :
      discriminant dMinusTwelveCandidate ≡ D-12

    dMinusTwelveStatusIsOpenCandidate :
      status dMinusTwelveCandidate ≡ leptonLaneCandidateOpen

    leptonSectorConstructed :
      Bool

    leptonSectorConstructedIsFalse :
      leptonSectorConstructed ≡ false

    leptonSectorAbsentOpen :
      Bool

    leptonSectorAbsentOpenIsTrue :
      leptonSectorAbsentOpen ≡ true

    exactStandardModelPromotion :
      Bool

    exactStandardModelPromotionIsFalse :
      exactStandardModelPromotion ≡ false

    gDHREqualsGSMPromoted :
      Bool

    gDHREqualsGSMPromotedIsFalse :
      gDHREqualsGSMPromoted ≡ false

    promotionFlags :
      List LeptonSectorPromotionFlag

    promotionFlagsAreEmpty :
      promotionFlags ≡ []

    blockers :
      List LeptonSectorGapBlocker

    blockersAreCanonical :
      blockers ≡ canonicalLeptonSectorGapBlockers

    receiptBoundary :
      String

    receiptBoundaryIsCanonical :
      receiptBoundary ≡ leptonSectorGapBoundaryLabel

    auditTrail :
      List String

open LeptonSectorGapReceipt public

canonicalLeptonSectorGapReceipt :
  LeptonSectorGapReceipt
canonicalLeptonSectorGapReceipt =
  record
    { heegnerLaneAssignmentReceipt =
        Heegner.canonicalHeegnerLaneAssignmentReceipt
    ; conductorLevelCorrespondenceReceipt =
        Conductor.canonicalConductorLevelCorrespondenceReceipt
    ; classNumberOneDiscriminants =
        canonicalClassNumberOneDiscriminants
    ; classNumberOneDiscriminantsAreCanonical =
        refl
    ; classNumberOneDiscriminantListStatement =
        classNumberOneDiscriminantListLabel
    ; classNumberOneDiscriminantListStatementIsCanonical =
        refl
    ; activeDiscriminants =
        activePrimeLaneDiscriminants
    ; activeDiscriminantsArePrimeLaneWindow =
        refl
    ; nextLeptonCandidateDiscriminants =
        nextLeptonLaneCandidateDiscriminants
    ; nextLeptonCandidateDiscriminantsAreCanonical =
        refl
    ; leptonLaneCandidates =
        canonicalLeptonLaneCandidates
    ; leptonLaneCandidatesAreCanonical =
        refl
    ; dMinusEightCandidate =
        dMinusEightLeptonLaneCandidate
    ; dMinusEightCandidateIsCanonical =
        refl
    ; dMinusEightDiscriminantIsMinusEight =
        refl
    ; dMinusEightCandidateLevelIsEight =
        refl
    ; p2LaneConductor =
        4
    ; p2LaneConductorIsFour =
        refl
    ; dMinusEightConductorConflictsWithP2Lane =
        false
    ; dMinusEightConductorConflictsWithP2LaneIsFalse =
        refl
    ; dMinusEightStatusIsOpenCandidate =
        refl
    ; dMinusElevenCandidate =
        dMinusElevenLeptonLaneCandidate
    ; dMinusElevenCandidateIsCanonical =
        refl
    ; dMinusElevenDiscriminantIsMinusEleven =
        refl
    ; dMinusElevenStatusIsOpenCandidate =
        refl
    ; dMinusTwelveCandidate =
        dMinusTwelveLeptonLaneCandidate
    ; dMinusTwelveCandidateIsCanonical =
        refl
    ; dMinusTwelveDiscriminantIsMinusTwelve =
        refl
    ; dMinusTwelveStatusIsOpenCandidate =
        refl
    ; leptonSectorConstructed =
        false
    ; leptonSectorConstructedIsFalse =
        refl
    ; leptonSectorAbsentOpen =
        true
    ; leptonSectorAbsentOpenIsTrue =
        refl
    ; exactStandardModelPromotion =
        false
    ; exactStandardModelPromotionIsFalse =
        refl
    ; gDHREqualsGSMPromoted =
        false
    ; gDHREqualsGSMPromotedIsFalse =
        refl
    ; promotionFlags =
        []
    ; promotionFlagsAreEmpty =
        refl
    ; blockers =
        canonicalLeptonSectorGapBlockers
    ; blockersAreCanonical =
        refl
    ; receiptBoundary =
        leptonSectorGapBoundaryLabel
    ; receiptBoundaryIsCanonical =
        refl
    ; auditTrail =
        "The active p2/p3/p5 class-number-1 CM window remains D=-4,D=-3,D=-7"
        ∷ "The full class-number-1 discriminant list recorded here is -3,-4,-7,-8,-11,-12,-16,-19,-27,-28,-43,-67,-163"
        ∷ "The next inspected discriminants D=-8,D=-11,D=-12 are recorded only as lepton-lane candidates"
        ∷ "D=-8 is corrected to field discriminant -8 with modular/character level 8; it is open because no lepton sector is constructed"
        ∷ "D=-11 is an open lepton-lane candidate"
        ∷ "D=-12 is an open lepton-lane candidate"
        ∷ "Closure.LeptonQuarkSeparationFinalReceipt now records the geometric-level diagnostic: pairwise-coprime quark levels, D=-8/D=-12 overlap, and D=-11 isolation"
        ∷ "The geometric split remains candidate-only; it does not construct a lepton sector or promote SM matter"
        ∷ "leptonSectorConstructed=false and leptonSectorAbsentOpen=true"
        ∷ "exactStandardModelPromotion=false and gDHREqualsGSMPromoted=false"
        ∷ []
    }

leptonSectorGapRecordsClassNumberOneList :
  classNumberOneDiscriminants canonicalLeptonSectorGapReceipt
  ≡
  canonicalClassNumberOneDiscriminants
leptonSectorGapRecordsClassNumberOneList =
  refl

leptonSectorGapRecordsNextCandidates :
  nextLeptonCandidateDiscriminants canonicalLeptonSectorGapReceipt
  ≡
  nextLeptonLaneCandidateDiscriminants
leptonSectorGapRecordsNextCandidates =
  refl

leptonSectorGapRecordsDMinusEightLevelEight :
  candidateConductor
    (dMinusEightCandidate canonicalLeptonSectorGapReceipt)
  ≡
  8
leptonSectorGapRecordsDMinusEightLevelEight =
  refl

leptonSectorGapRecordsDMinusEightNoP2Conflict :
  dMinusEightConductorConflictsWithP2Lane
    canonicalLeptonSectorGapReceipt
  ≡
  false
leptonSectorGapRecordsDMinusEightNoP2Conflict =
  refl

leptonSectorGapRecordsDMinusElevenCandidate :
  status (dMinusElevenCandidate canonicalLeptonSectorGapReceipt)
  ≡
  leptonLaneCandidateOpen
leptonSectorGapRecordsDMinusElevenCandidate =
  refl

leptonSectorGapKeepsLeptonSectorAbsentOpen :
  leptonSectorAbsentOpen canonicalLeptonSectorGapReceipt
  ≡
  true
leptonSectorGapKeepsLeptonSectorAbsentOpen =
  refl

leptonSectorGapKeepsLeptonSectorUnconstructed :
  leptonSectorConstructed canonicalLeptonSectorGapReceipt
  ≡
  false
leptonSectorGapKeepsLeptonSectorUnconstructed =
  refl

leptonSectorGapKeepsExactSMPromotionFalse :
  exactStandardModelPromotion canonicalLeptonSectorGapReceipt
  ≡
  false
leptonSectorGapKeepsExactSMPromotionFalse =
  refl

leptonSectorGapKeepsGDHRToGSMPromotionFalse :
  gDHREqualsGSMPromoted canonicalLeptonSectorGapReceipt
  ≡
  false
leptonSectorGapKeepsGDHRToGSMPromotionFalse =
  refl
