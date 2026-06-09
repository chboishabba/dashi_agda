module DASHI.Physics.QFT.LevelRankDualityReceipt where

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)
open import Data.List.Base using (List; _∷_; [])

------------------------------------------------------------------------
-- Level-rank duality receipt.
--
-- This module records a citation-authority style boundary for WZW/Chern-Simons
-- level-rank duality.  The external authority is inhabited for the general
-- SU(N)_k / SU(k)_N statement.  The local p3 conductor-3 CM ring is recorded
-- only as a candidate common spin/colour TQFT viewpoint relating an SU(2)_3
-- spin-side label and an SU(3)_1 colour-side label.
--
-- No exact SU(3)_c gauge-group construction and no exact G_DHR ~= G_SM
-- identification is promoted here.

data LevelRankDualityCitation : Set where
  nakanishiTsuchiyaLevelRankDuality :
    LevelRankDualityCitation

  rankLevelDualityWZWChernSimonsAuthority :
    LevelRankDualityCitation

canonicalLevelRankDualityCitations :
  List LevelRankDualityCitation
canonicalLevelRankDualityCitations =
  nakanishiTsuchiyaLevelRankDuality
  ∷ rankLevelDualityWZWChernSimonsAuthority
  ∷ []

data LevelRankAuthorityStatus : Set where
  externalCitationAuthority :
    LevelRankAuthorityStatus

data LevelRankBoundaryStatus : Set where
  exactSUNkSUkNDualityAuthority :
    LevelRankBoundaryStatus

  requestedSU2ThreeSU3OneCandidateBoundary :
    LevelRankBoundaryStatus

data CMRingCandidateStatus : Set where
  candidateOnly :
    CMRingCandidateStatus

data ExactGaugePromotionStatus : Set where
  notPromoted :
    ExactGaugePromotionStatus

data WZWChernSimonsTheoryLabel : Set where
  su2Level3SpinSide :
    WZWChernSimonsTheoryLabel

  su3Level1ColourSide :
    WZWChernSimonsTheoryLabel

  su3Level2FormalLevelRankPartner :
    WZWChernSimonsTheoryLabel

canonicalRequestedSpinColourPair :
  List WZWChernSimonsTheoryLabel
canonicalRequestedSpinColourPair =
  su2Level3SpinSide
  ∷ su3Level1ColourSide
  ∷ []

canonicalFormalLevelRankPair :
  List WZWChernSimonsTheoryLabel
canonicalFormalLevelRankPair =
  su2Level3SpinSide
  ∷ su3Level2FormalLevelRankPartner
  ∷ []

levelRankAuthorityLabel :
  String
levelRankAuthorityLabel =
  "External citation authority records SU(N)_k / SU(k)_N WZW-Chern-Simons level-rank duality"

su2ThreeSU3OneCandidateLabel :
  String
su2ThreeSU3OneCandidateLabel =
  "SU(2)_3 <-> SU(3)_1 is recorded here as a requested spin/colour candidate boundary, not as the strict SU(N)_k / SU(k)_N partner"

su2ThreeFormalPartnerLabel :
  String
su2ThreeFormalPartnerLabel =
  "For strict SU(N)_k / SU(k)_N level-rank bookkeeping, SU(2)_3 pairs with SU(3)_2"

p3Conductor3CMRingLabel :
  String
p3Conductor3CMRingLabel =
  "p3 conductor-3 CM ring candidate shared spin/colour TQFT perspective"

exactSU3cFalseLabel :
  String
exactSU3cFalseLabel =
  "Exact SU3_c is false in this receipt"

exactGDHREqualsGSMFalseLabel :
  String
exactGDHREqualsGSMFalseLabel =
  "Exact G_DHR ~= G_SM is false in this receipt"

data SameCMRingPromotion : Set where

sameCMRingPromotionImpossibleHere :
  SameCMRingPromotion →
  ⊥
sameCMRingPromotionImpossibleHere ()

record LevelRankDualityReceipt : Setω where
  field
    authorityStatus :
      LevelRankAuthorityStatus

    authorityStatusIsExternalCitation :
      authorityStatus ≡ externalCitationAuthority

    citations :
      List LevelRankDualityCitation

    citationsAreCanonical :
      citations ≡ canonicalLevelRankDualityCitations

    authorityStatement :
      String

    authorityStatementIsCanonical :
      authorityStatement ≡ levelRankAuthorityLabel

    levelRankDualityInhabited :
      Bool

    levelRankDualityInhabitedIsTrue :
      levelRankDualityInhabited ≡ true

    formalBoundaryStatus :
      LevelRankBoundaryStatus

    formalBoundaryStatusIsExactAuthority :
      formalBoundaryStatus ≡ exactSUNkSUkNDualityAuthority

    formalLevelRankPair :
      List WZWChernSimonsTheoryLabel

    formalLevelRankPairIsCanonical :
      formalLevelRankPair ≡ canonicalFormalLevelRankPair

    su2Rank :
      Nat

    su2RankIsTwo :
      su2Rank ≡ 2

    su2Level :
      Nat

    su2LevelIsThree :
      su2Level ≡ 3

    strictDualRank :
      Nat

    strictDualRankIsThree :
      strictDualRank ≡ 3

    strictDualLevel :
      Nat

    strictDualLevelIsTwo :
      strictDualLevel ≡ 2

    strictDualStatement :
      String

    strictDualStatementIsCanonical :
      strictDualStatement ≡ su2ThreeFormalPartnerLabel

    requestedCandidateStatus :
      LevelRankBoundaryStatus

    requestedCandidateStatusIsSU2ThreeSU3OneCandidate :
      requestedCandidateStatus ≡ requestedSU2ThreeSU3OneCandidateBoundary

    requestedSpinColourPair :
      List WZWChernSimonsTheoryLabel

    requestedSpinColourPairIsCanonical :
      requestedSpinColourPair ≡ canonicalRequestedSpinColourPair

    requestedSpinSideRank :
      Nat

    requestedSpinSideRankIsTwo :
      requestedSpinSideRank ≡ 2

    requestedSpinSideLevel :
      Nat

    requestedSpinSideLevelIsThree :
      requestedSpinSideLevel ≡ 3

    requestedColourSideRank :
      Nat

    requestedColourSideRankIsThree :
      requestedColourSideRank ≡ 3

    requestedColourSideLevel :
      Nat

    requestedColourSideLevelIsOne :
      requestedColourSideLevel ≡ 1

    requestedCandidateStatement :
      String

    requestedCandidateStatementIsCanonical :
      requestedCandidateStatement ≡ su2ThreeSU3OneCandidateLabel

    p3Prime :
      Nat

    p3PrimeIsThree :
      p3Prime ≡ 3

    p3Conductor :
      Nat

    p3ConductorIsThree :
      p3Conductor ≡ 3

    p3CMRingCandidate :
      CMRingCandidateStatus

    p3CMRingCandidateIsCandidateOnly :
      p3CMRingCandidate ≡ candidateOnly

    p3CMRingCandidateStatement :
      String

    p3CMRingCandidateStatementIsCanonical :
      p3CMRingCandidateStatement ≡ p3Conductor3CMRingLabel

    su2SpinAndSu3ColourFromSameCMRing :
      Bool

    su2SpinAndSu3ColourFromSameCMRingIsCandidateOnly :
      su2SpinAndSu3ColourFromSameCMRing ≡ true

    exactSameCMRingPromotionConstructed :
      Bool

    exactSameCMRingPromotionConstructedIsFalse :
      exactSameCMRingPromotionConstructed ≡ false

    exactSU3c :
      Bool

    exactSU3cIsFalse :
      exactSU3c ≡ false

    exactSU3cBoundary :
      String

    exactSU3cBoundaryIsCanonical :
      exactSU3cBoundary ≡ exactSU3cFalseLabel

    exactGDHREqualsGSM :
      Bool

    exactGDHREqualsGSMIsFalse :
      exactGDHREqualsGSM ≡ false

    exactGDHREqualsGSMBoundary :
      String

    exactGDHREqualsGSMBoundaryIsCanonical :
      exactGDHREqualsGSMBoundary ≡ exactGDHREqualsGSMFalseLabel

    exactGaugePromotionStatus :
      ExactGaugePromotionStatus

    exactGaugePromotionStatusIsNotPromoted :
      exactGaugePromotionStatus ≡ notPromoted

    receiptBoundary :
      List String

open LevelRankDualityReceipt public

canonicalLevelRankDualityReceipt :
  LevelRankDualityReceipt
canonicalLevelRankDualityReceipt =
  record
    { authorityStatus =
        externalCitationAuthority
    ; authorityStatusIsExternalCitation =
        refl
    ; citations =
        canonicalLevelRankDualityCitations
    ; citationsAreCanonical =
        refl
    ; authorityStatement =
        levelRankAuthorityLabel
    ; authorityStatementIsCanonical =
        refl
    ; levelRankDualityInhabited =
        true
    ; levelRankDualityInhabitedIsTrue =
        refl
    ; formalBoundaryStatus =
        exactSUNkSUkNDualityAuthority
    ; formalBoundaryStatusIsExactAuthority =
        refl
    ; formalLevelRankPair =
        canonicalFormalLevelRankPair
    ; formalLevelRankPairIsCanonical =
        refl
    ; su2Rank =
        2
    ; su2RankIsTwo =
        refl
    ; su2Level =
        3
    ; su2LevelIsThree =
        refl
    ; strictDualRank =
        3
    ; strictDualRankIsThree =
        refl
    ; strictDualLevel =
        2
    ; strictDualLevelIsTwo =
        refl
    ; strictDualStatement =
        su2ThreeFormalPartnerLabel
    ; strictDualStatementIsCanonical =
        refl
    ; requestedCandidateStatus =
        requestedSU2ThreeSU3OneCandidateBoundary
    ; requestedCandidateStatusIsSU2ThreeSU3OneCandidate =
        refl
    ; requestedSpinColourPair =
        canonicalRequestedSpinColourPair
    ; requestedSpinColourPairIsCanonical =
        refl
    ; requestedSpinSideRank =
        2
    ; requestedSpinSideRankIsTwo =
        refl
    ; requestedSpinSideLevel =
        3
    ; requestedSpinSideLevelIsThree =
        refl
    ; requestedColourSideRank =
        3
    ; requestedColourSideRankIsThree =
        refl
    ; requestedColourSideLevel =
        1
    ; requestedColourSideLevelIsOne =
        refl
    ; requestedCandidateStatement =
        su2ThreeSU3OneCandidateLabel
    ; requestedCandidateStatementIsCanonical =
        refl
    ; p3Prime =
        3
    ; p3PrimeIsThree =
        refl
    ; p3Conductor =
        3
    ; p3ConductorIsThree =
        refl
    ; p3CMRingCandidate =
        candidateOnly
    ; p3CMRingCandidateIsCandidateOnly =
        refl
    ; p3CMRingCandidateStatement =
        p3Conductor3CMRingLabel
    ; p3CMRingCandidateStatementIsCanonical =
        refl
    ; su2SpinAndSu3ColourFromSameCMRing =
        true
    ; su2SpinAndSu3ColourFromSameCMRingIsCandidateOnly =
        refl
    ; exactSameCMRingPromotionConstructed =
        false
    ; exactSameCMRingPromotionConstructedIsFalse =
        refl
    ; exactSU3c =
        false
    ; exactSU3cIsFalse =
        refl
    ; exactSU3cBoundary =
        exactSU3cFalseLabel
    ; exactSU3cBoundaryIsCanonical =
        refl
    ; exactGDHREqualsGSM =
        false
    ; exactGDHREqualsGSMIsFalse =
        refl
    ; exactGDHREqualsGSMBoundary =
        exactGDHREqualsGSMFalseLabel
    ; exactGDHREqualsGSMBoundaryIsCanonical =
        refl
    ; exactGaugePromotionStatus =
        notPromoted
    ; exactGaugePromotionStatusIsNotPromoted =
        refl
    ; receiptBoundary =
        "levelRankDualityInhabited=true records external citation authority for SU(N)_k / SU(k)_N level-rank duality"
        ∷ "Strict SU(N)_k / SU(k)_N bookkeeping sends SU(2)_3 to SU(3)_2"
        ∷ "The requested SU(2)_3 <-> SU(3)_1 surface is retained as a candidate spin/colour boundary"
        ∷ "The p3 conductor-3 CM ring is candidate-only shared TQFT perspective data"
        ∷ "su2SpinAndSu3ColourFromSameCMRing=true is candidate-only; exact same-CM-ring promotion is false"
        ∷ "Exact SU3_c and exact G_DHR ~= G_SM remain false"
        ∷ []
    }

levelRankDualityReceiptInhabited :
  Bool
levelRankDualityReceiptInhabited =
  LevelRankDualityReceipt.levelRankDualityInhabited
    canonicalLevelRankDualityReceipt

levelRankDualityReceiptInhabitedIsTrue :
  levelRankDualityReceiptInhabited ≡ true
levelRankDualityReceiptInhabitedIsTrue =
  refl

levelRankReceiptSU2SpinAndSU3ColourFromSameCMRing :
  Bool
levelRankReceiptSU2SpinAndSU3ColourFromSameCMRing =
  LevelRankDualityReceipt.su2SpinAndSu3ColourFromSameCMRing
    canonicalLevelRankDualityReceipt

levelRankReceiptSU2SpinAndSU3ColourFromSameCMRingIsCandidateOnly :
  levelRankReceiptSU2SpinAndSU3ColourFromSameCMRing ≡ true
levelRankReceiptSU2SpinAndSU3ColourFromSameCMRingIsCandidateOnly =
  refl

levelRankReceiptExactSameCMRingPromotionConstructedIsFalse :
  LevelRankDualityReceipt.exactSameCMRingPromotionConstructed
    canonicalLevelRankDualityReceipt
  ≡
  false
levelRankReceiptExactSameCMRingPromotionConstructedIsFalse =
  refl

levelRankReceiptExactSU3cIsFalse :
  exactSU3c canonicalLevelRankDualityReceipt
  ≡
  false
levelRankReceiptExactSU3cIsFalse =
  refl

levelRankReceiptExactGDHREqualsGSMIsFalse :
  exactGDHREqualsGSM canonicalLevelRankDualityReceipt
  ≡
  false
levelRankReceiptExactGDHREqualsGSMIsFalse =
  refl
