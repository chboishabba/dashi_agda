module DASHI.Physics.QFT.KacMoodyLevelReceipt where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)
open import Data.List.Base using (List; _∷_; [])

------------------------------------------------------------------------
-- Kac-Moody level receipt.
--
-- This receipt separates three notions that are easy to conflate:
--
-- * Chern-Simons level k_CS for a three-dimensional topological theory.
-- * WZW / affine Kac-Moody level k_KM for the boundary chiral algebra.
-- * SU(2)_k integrable highest-weight representations, recorded by doubled
--   spin 2j with the integrability bound 2j <= k, equivalently j <= k/2.
--
-- The Standard Model weak SU(2) line is recorded only as a level-1 candidate.
-- The p3 conductor-3 lane is recorded only as an SU(2)_3 candidate.  Their
-- level-one-vs-level-three mismatch remains an open obstruction.  No exact
-- Standard Model, DHR, or G_DHR ~= G_SM promotion is introduced here.

data LevelKind : Set where
  chernSimonsLevel :
    LevelKind

  wzwKacMoodyLevel :
    LevelKind

data GaugeFamily : Set where
  su2Family :
    GaugeFamily

data CandidateSource : Set where
  standardModelWeakSU2 :
    CandidateSource

  p3Conductor3Lane :
    CandidateSource

data CandidateStatus : Set where
  levelCandidateOnly :
    CandidateStatus

  mismatchOpen :
    CandidateStatus

data LevelMismatch : Set where
  weakLevelOneVsP3LevelThreeOpen :
    LevelMismatch

data PromotionBlocker : Set where
  noExactStandardModelPromotion :
    PromotionBlocker

  noExactDHRPromotion :
    PromotionBlocker

  noExactGDHREqualsGSMPromotion :
    PromotionBlocker

  levelOneVsLevelThreeMismatchNotResolved :
    PromotionBlocker

canonicalPromotionBlockers :
  List PromotionBlocker
canonicalPromotionBlockers =
  noExactStandardModelPromotion
  ∷ noExactDHRPromotion
  ∷ noExactGDHREqualsGSMPromotion
  ∷ levelOneVsLevelThreeMismatchNotResolved
  ∷ []

record LevelReading : Set where
  field
    source :
      CandidateSource

    family :
      GaugeFamily

    levelKind :
      LevelKind

    level :
      Nat

    status :
      CandidateStatus

open LevelReading public

smWeakSU2KacMoodyLevel1Candidate :
  LevelReading
smWeakSU2KacMoodyLevel1Candidate =
  record
    { source =
        standardModelWeakSU2
    ; family =
        su2Family
    ; levelKind =
        wzwKacMoodyLevel
    ; level =
        1
    ; status =
        levelCandidateOnly
    }

p3Conductor3ChernSimonsLevel3Candidate :
  LevelReading
p3Conductor3ChernSimonsLevel3Candidate =
  record
    { source =
        p3Conductor3Lane
    ; family =
        su2Family
    ; levelKind =
        chernSimonsLevel
    ; level =
        3
    ; status =
        levelCandidateOnly
    }

p3Conductor3KacMoodyLevel3Candidate :
  LevelReading
p3Conductor3KacMoodyLevel3Candidate =
  record
    { source =
        p3Conductor3Lane
    ; family =
        su2Family
    ; levelKind =
        wzwKacMoodyLevel
    ; level =
        3
    ; status =
        levelCandidateOnly
    }

canonicalLevelReadings :
  List LevelReading
canonicalLevelReadings =
  smWeakSU2KacMoodyLevel1Candidate
  ∷ p3Conductor3ChernSimonsLevel3Candidate
  ∷ p3Conductor3KacMoodyLevel3Candidate
  ∷ []

record SU2IntegrableRep : Set where
  field
    su2Level :
      Nat

    doubledSpin :
      Nat

    boundLabel :
      String

    allowedByIntegrabilityBound :
      Bool

open SU2IntegrableRep public

su2IntegrabilityBoundLabel :
  String
su2IntegrabilityBoundLabel =
  "SU(2)_k integrable highest weights satisfy j <= k/2, equivalently 2j <= k"

su2K1Spin0Allowed :
  SU2IntegrableRep
su2K1Spin0Allowed =
  record
    { su2Level =
        1
    ; doubledSpin =
        0
    ; boundLabel =
        su2IntegrabilityBoundLabel
    ; allowedByIntegrabilityBound =
        true
    }

su2K1SpinHalfAllowed :
  SU2IntegrableRep
su2K1SpinHalfAllowed =
  record
    { su2Level =
        1
    ; doubledSpin =
        1
    ; boundLabel =
        su2IntegrabilityBoundLabel
    ; allowedByIntegrabilityBound =
        true
    }

su2K3Spin0Allowed :
  SU2IntegrableRep
su2K3Spin0Allowed =
  record
    { su2Level =
        3
    ; doubledSpin =
        0
    ; boundLabel =
        su2IntegrabilityBoundLabel
    ; allowedByIntegrabilityBound =
        true
    }

su2K3SpinHalfAllowed :
  SU2IntegrableRep
su2K3SpinHalfAllowed =
  record
    { su2Level =
        3
    ; doubledSpin =
        1
    ; boundLabel =
        su2IntegrabilityBoundLabel
    ; allowedByIntegrabilityBound =
        true
    }

su2K3Spin1Allowed :
  SU2IntegrableRep
su2K3Spin1Allowed =
  record
    { su2Level =
        3
    ; doubledSpin =
        2
    ; boundLabel =
        su2IntegrabilityBoundLabel
    ; allowedByIntegrabilityBound =
        true
    }

su2K3SpinThreeHalfAllowed :
  SU2IntegrableRep
su2K3SpinThreeHalfAllowed =
  record
    { su2Level =
        3
    ; doubledSpin =
        3
    ; boundLabel =
        su2IntegrabilityBoundLabel
    ; allowedByIntegrabilityBound =
        true
    }

canonicalSU2Level1IntegrableReps :
  List SU2IntegrableRep
canonicalSU2Level1IntegrableReps =
  su2K1Spin0Allowed
  ∷ su2K1SpinHalfAllowed
  ∷ []

canonicalSU2Level3IntegrableReps :
  List SU2IntegrableRep
canonicalSU2Level3IntegrableReps =
  su2K3Spin0Allowed
  ∷ su2K3SpinHalfAllowed
  ∷ su2K3Spin1Allowed
  ∷ su2K3SpinThreeHalfAllowed
  ∷ []

levelKindSeparationLabel : String
levelKindSeparationLabel =
  "Chern-Simons level and WZW/Kac-Moody level are recorded as distinct level-kind fields"

smWeakLevelOneCandidateLabel : String
smWeakLevelOneCandidateLabel =
  "Standard Model weak SU(2) is recorded only as an SU(2)_1 WZW/Kac-Moody candidate"

p3Conductor3SU2Level3CandidateLabel : String
p3Conductor3SU2Level3CandidateLabel =
  "p3 conductor-3 is recorded only as an SU(2)_3 candidate"

levelOneVsLevelThreeMismatchOpenLabel : String
levelOneVsLevelThreeMismatchOpenLabel =
  "level-one Standard Model weak SU(2) candidate and level-three p3 SU(2)_3 candidate are not identified; mismatch remains open"

allPromotionsFalseLabel : String
allPromotionsFalseLabel =
  "exact Standard Model, DHR, and G_DHR ~= G_SM promotion flags remain false"

canonicalReceiptBoundary :
  List String
canonicalReceiptBoundary =
  levelKindSeparationLabel
  ∷ su2IntegrabilityBoundLabel
  ∷ smWeakLevelOneCandidateLabel
  ∷ p3Conductor3SU2Level3CandidateLabel
  ∷ levelOneVsLevelThreeMismatchOpenLabel
  ∷ allPromotionsFalseLabel
  ∷ []

record KacMoodyLevelReceipt : Set where
  field
    levelReadings :
      List LevelReading

    levelReadingsAreCanonical :
      levelReadings ≡ canonicalLevelReadings

    smWeakCandidate :
      LevelReading

    smWeakCandidateIsCanonical :
      smWeakCandidate ≡ smWeakSU2KacMoodyLevel1Candidate

    smWeakCandidateIsKacMoodyLevel :
      levelKind smWeakCandidate ≡ wzwKacMoodyLevel

    smWeakCandidateLevelIsOne :
      level smWeakCandidate ≡ 1

    p3ChernSimonsCandidate :
      LevelReading

    p3ChernSimonsCandidateIsCanonical :
      p3ChernSimonsCandidate ≡ p3Conductor3ChernSimonsLevel3Candidate

    p3ChernSimonsCandidateIsCSLevel :
      levelKind p3ChernSimonsCandidate ≡ chernSimonsLevel

    p3ChernSimonsCandidateLevelIsThree :
      level p3ChernSimonsCandidate ≡ 3

    p3KacMoodyCandidate :
      LevelReading

    p3KacMoodyCandidateIsCanonical :
      p3KacMoodyCandidate ≡ p3Conductor3KacMoodyLevel3Candidate

    p3KacMoodyCandidateIsKacMoodyLevel :
      levelKind p3KacMoodyCandidate ≡ wzwKacMoodyLevel

    p3KacMoodyCandidateLevelIsThree :
      level p3KacMoodyCandidate ≡ 3

    su2Level1IntegrableReps :
      List SU2IntegrableRep

    su2Level1IntegrableRepsAreCanonical :
      su2Level1IntegrableReps ≡ canonicalSU2Level1IntegrableReps

    su2Level3IntegrableReps :
      List SU2IntegrableRep

    su2Level3IntegrableRepsAreCanonical :
      su2Level3IntegrableReps ≡ canonicalSU2Level3IntegrableReps

    integrabilityBound :
      String

    integrabilityBoundIsCanonical :
      integrabilityBound ≡ su2IntegrabilityBoundLabel

    k1SpinHalfAllowed :
      Bool

    k1SpinHalfAllowedIsTrue :
      k1SpinHalfAllowed ≡ true

    k3SpinThreeHalfAllowed :
      Bool

    k3SpinThreeHalfAllowedIsTrue :
      k3SpinThreeHalfAllowed ≡ true

    levelMismatch :
      LevelMismatch

    levelMismatchIsOpen :
      levelMismatch ≡ weakLevelOneVsP3LevelThreeOpen

    levelOneVsLevelThreeIdentified :
      Bool

    levelOneVsLevelThreeIdentifiedIsFalse :
      levelOneVsLevelThreeIdentified ≡ false

    exactStandardModelPromotion :
      Bool

    exactStandardModelPromotionIsFalse :
      exactStandardModelPromotion ≡ false

    exactDHRPromotion :
      Bool

    exactDHRPromotionIsFalse :
      exactDHRPromotion ≡ false

    exactGDHREqualsGSMPromotion :
      Bool

    exactGDHREqualsGSMPromotionIsFalse :
      exactGDHREqualsGSMPromotion ≡ false

    promotionBlockers :
      List PromotionBlocker

    promotionBlockersAreCanonical :
      promotionBlockers ≡ canonicalPromotionBlockers

    receiptBoundary :
      List String

    receiptBoundaryIsCanonical :
      receiptBoundary ≡ canonicalReceiptBoundary

open KacMoodyLevelReceipt public

canonicalKacMoodyLevelReceipt :
  KacMoodyLevelReceipt
canonicalKacMoodyLevelReceipt =
  record
    { levelReadings =
        canonicalLevelReadings
    ; levelReadingsAreCanonical =
        refl
    ; smWeakCandidate =
        smWeakSU2KacMoodyLevel1Candidate
    ; smWeakCandidateIsCanonical =
        refl
    ; smWeakCandidateIsKacMoodyLevel =
        refl
    ; smWeakCandidateLevelIsOne =
        refl
    ; p3ChernSimonsCandidate =
        p3Conductor3ChernSimonsLevel3Candidate
    ; p3ChernSimonsCandidateIsCanonical =
        refl
    ; p3ChernSimonsCandidateIsCSLevel =
        refl
    ; p3ChernSimonsCandidateLevelIsThree =
        refl
    ; p3KacMoodyCandidate =
        p3Conductor3KacMoodyLevel3Candidate
    ; p3KacMoodyCandidateIsCanonical =
        refl
    ; p3KacMoodyCandidateIsKacMoodyLevel =
        refl
    ; p3KacMoodyCandidateLevelIsThree =
        refl
    ; su2Level1IntegrableReps =
        canonicalSU2Level1IntegrableReps
    ; su2Level1IntegrableRepsAreCanonical =
        refl
    ; su2Level3IntegrableReps =
        canonicalSU2Level3IntegrableReps
    ; su2Level3IntegrableRepsAreCanonical =
        refl
    ; integrabilityBound =
        su2IntegrabilityBoundLabel
    ; integrabilityBoundIsCanonical =
        refl
    ; k1SpinHalfAllowed =
        allowedByIntegrabilityBound su2K1SpinHalfAllowed
    ; k1SpinHalfAllowedIsTrue =
        refl
    ; k3SpinThreeHalfAllowed =
        allowedByIntegrabilityBound su2K3SpinThreeHalfAllowed
    ; k3SpinThreeHalfAllowedIsTrue =
        refl
    ; levelMismatch =
        weakLevelOneVsP3LevelThreeOpen
    ; levelMismatchIsOpen =
        refl
    ; levelOneVsLevelThreeIdentified =
        false
    ; levelOneVsLevelThreeIdentifiedIsFalse =
        refl
    ; exactStandardModelPromotion =
        false
    ; exactStandardModelPromotionIsFalse =
        refl
    ; exactDHRPromotion =
        false
    ; exactDHRPromotionIsFalse =
        refl
    ; exactGDHREqualsGSMPromotion =
        false
    ; exactGDHREqualsGSMPromotionIsFalse =
        refl
    ; promotionBlockers =
        canonicalPromotionBlockers
    ; promotionBlockersAreCanonical =
        refl
    ; receiptBoundary =
        canonicalReceiptBoundary
    ; receiptBoundaryIsCanonical =
        refl
    }

kacMoodyReceiptDistinguishesChernSimonsAndKacMoodyLevels :
  levelKind (p3ChernSimonsCandidate canonicalKacMoodyLevelReceipt)
  ≡
  chernSimonsLevel
kacMoodyReceiptDistinguishesChernSimonsAndKacMoodyLevels =
  refl

kacMoodyReceiptRecordsSMWeakSU2LevelOneCandidate :
  level (smWeakCandidate canonicalKacMoodyLevelReceipt)
  ≡
  1
kacMoodyReceiptRecordsSMWeakSU2LevelOneCandidate =
  refl

kacMoodyReceiptRecordsP3Conductor3SU2LevelThreeCandidate :
  level (p3KacMoodyCandidate canonicalKacMoodyLevelReceipt)
  ≡
  3
kacMoodyReceiptRecordsP3Conductor3SU2LevelThreeCandidate =
  refl

kacMoodyReceiptK1SpinHalfAllowed :
  k1SpinHalfAllowed canonicalKacMoodyLevelReceipt
  ≡
  true
kacMoodyReceiptK1SpinHalfAllowed =
  refl

kacMoodyReceiptK3SpinThreeHalfAllowed :
  k3SpinThreeHalfAllowed canonicalKacMoodyLevelReceipt
  ≡
  true
kacMoodyReceiptK3SpinThreeHalfAllowed =
  refl

kacMoodyReceiptLevelOneVsLevelThreeMismatchOpen :
  levelOneVsLevelThreeIdentified canonicalKacMoodyLevelReceipt
  ≡
  false
kacMoodyReceiptLevelOneVsLevelThreeMismatchOpen =
  refl

kacMoodyReceiptExactStandardModelPromotionFalse :
  exactStandardModelPromotion canonicalKacMoodyLevelReceipt
  ≡
  false
kacMoodyReceiptExactStandardModelPromotionFalse =
  refl

kacMoodyReceiptExactDHRPromotionFalse :
  exactDHRPromotion canonicalKacMoodyLevelReceipt
  ≡
  false
kacMoodyReceiptExactDHRPromotionFalse =
  refl

kacMoodyReceiptExactGDHREqualsGSMPromotionFalse :
  exactGDHREqualsGSMPromotion canonicalKacMoodyLevelReceipt
  ≡
  false
kacMoodyReceiptExactGDHREqualsGSMPromotionFalse =
  refl
