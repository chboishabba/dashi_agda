module DASHI.Physics.QFT.MuonNeutrinoIsolationReceipt where

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)
open import Data.List.Base using (List; _∷_; [])

import DASHI.Physics.QFT.ConductorLevelCorrespondenceReceipt as Conductor
import DASHI.Physics.QFT.LeptonSectorGapReceipt as Gap

------------------------------------------------------------------------
-- D=-11 / level 11 muon-neutrino isolation receipt.
--
-- This receipt records only the conductor-level diagnostic: the D=-11
-- candidate has level 11, which is coprime to the active quark-candidate
-- levels 3, 4, and 7.  In the level-overlap bookkeeping this blocks a
-- leading direct quark-lepton Yukawa overlap.  It does not construct a
-- physical muon neutrino, a lepton sector, an exact Standard Model sector,
-- G_DHR ~= G_SM, or a terminal claim.

data MuonNeutrinoIsolationStatus : Set where
  levelElevenCoprimeToQuarkLevelsRecorded :
    MuonNeutrinoIsolationStatus

data CoprimeWitness : Set where
  gcdIsOne :
    CoprimeWitness

data LeadingYukawaStatus : Set where
  noLeadingDirectQuarkLeptonYukawa :
    LeadingYukawaStatus

data MuonNeutrinoIsolationBlocker : Set where
  levelOverlapModelDiagnosticOnly :
    MuonNeutrinoIsolationBlocker

  muonNeutrinoLaneNotPhysicallyConstructed :
    MuonNeutrinoIsolationBlocker

  noLeptonRepresentationTable :
    MuonNeutrinoIsolationBlocker

  noYukawaCarrierMap :
    MuonNeutrinoIsolationBlocker

  noNeutrinoMassOrMixingReceipt :
    MuonNeutrinoIsolationBlocker

canonicalMuonNeutrinoIsolationBlockers :
  List MuonNeutrinoIsolationBlocker
canonicalMuonNeutrinoIsolationBlockers =
  levelOverlapModelDiagnosticOnly
  ∷ muonNeutrinoLaneNotPhysicallyConstructed
  ∷ noLeptonRepresentationTable
  ∷ noYukawaCarrierMap
  ∷ noNeutrinoMassOrMixingReceipt
  ∷ []

data MuonNeutrinoIsolationPromotion : Set where

muonNeutrinoIsolationPromotionImpossibleHere :
  MuonNeutrinoIsolationPromotion →
  ⊥
muonNeutrinoIsolationPromotionImpossibleHere ()

levelElevenCoprimeStatementLabel : String
levelElevenCoprimeStatementLabel =
  "D=-11 / level 11 is coprime to quark-candidate levels 3, 4, and 7"

leadingYukawaStatementLabel : String
leadingYukawaStatementLabel =
  "there is no leading direct quark-lepton Yukawa in the level-overlap diagnostic"

receiptBoundaryLabel : String
receiptBoundaryLabel =
  "D=-11 isolation is conductor-level bookkeeping only; exact lepton/quark/SM/G_DHR/terminal promotions remain false"

record MuonNeutrinoIsolationReceipt : Setω where
  field
    conductorLevelReceipt :
      Conductor.ConductorLevelCorrespondenceReceipt

    leptonSectorGapReceipt :
      Gap.LeptonSectorGapReceipt

    status :
      MuonNeutrinoIsolationStatus

    statusIsCoprimeDiagnostic :
      status ≡ levelElevenCoprimeToQuarkLevelsRecorded

    discriminant :
      Gap.ClassNumberOneDiscriminant

    discriminantIsDMinusEleven :
      discriminant ≡ Gap.D-11

    level :
      Nat

    levelIsEleven :
      level ≡ 11

    p3QuarkLevel :
      Nat

    p3QuarkLevelIsThree :
      p3QuarkLevel ≡ 3

    p2QuarkLevel :
      Nat

    p2QuarkLevelIsFour :
      p2QuarkLevel ≡ 4

    p5QuarkLevel :
      Nat

    p5QuarkLevelIsSeven :
      p5QuarkLevel ≡ 7

    gcdLevel11WithP3 :
      Nat

    gcdLevel11WithP3IsOne :
      gcdLevel11WithP3 ≡ 1

    gcdLevel11WithP2 :
      Nat

    gcdLevel11WithP2IsOne :
      gcdLevel11WithP2 ≡ 1

    gcdLevel11WithP5 :
      Nat

    gcdLevel11WithP5IsOne :
      gcdLevel11WithP5 ≡ 1

    coprimeWithP3 :
      CoprimeWitness

    coprimeWithP3IsGcdOne :
      coprimeWithP3 ≡ gcdIsOne

    coprimeWithP2 :
      CoprimeWitness

    coprimeWithP2IsGcdOne :
      coprimeWithP2 ≡ gcdIsOne

    coprimeWithP5 :
      CoprimeWitness

    coprimeWithP5IsGcdOne :
      coprimeWithP5 ≡ gcdIsOne

    coprimeStatement :
      String

    coprimeStatementIsCanonical :
      coprimeStatement ≡ levelElevenCoprimeStatementLabel

    leadingYukawaStatus :
      LeadingYukawaStatus

    leadingYukawaStatusIsNoDirectYukawa :
      leadingYukawaStatus ≡ noLeadingDirectQuarkLeptonYukawa

    leadingDirectQuarkLeptonYukawaPresent :
      Bool

    leadingDirectQuarkLeptonYukawaPresentIsFalse :
      leadingDirectQuarkLeptonYukawaPresent ≡ false

    leadingYukawaStatement :
      String

    leadingYukawaStatementIsCanonical :
      leadingYukawaStatement ≡ leadingYukawaStatementLabel

    structuralDiagnosticOnly :
      Bool

    structuralDiagnosticOnlyIsTrue :
      structuralDiagnosticOnly ≡ true

    exactLeptonPromotion :
      Bool

    exactLeptonPromotionIsFalse :
      exactLeptonPromotion ≡ false

    exactQuarkPromotion :
      Bool

    exactQuarkPromotionIsFalse :
      exactQuarkPromotion ≡ false

    exactStandardModelPromotion :
      Bool

    exactStandardModelPromotionIsFalse :
      exactStandardModelPromotion ≡ false

    exactGDHREqualsGSMPromotion :
      Bool

    exactGDHREqualsGSMPromotionIsFalse :
      exactGDHREqualsGSMPromotion ≡ false

    terminalClaimPromoted :
      Bool

    terminalClaimPromotedIsFalse :
      terminalClaimPromoted ≡ false

    blockers :
      List MuonNeutrinoIsolationBlocker

    blockersAreCanonical :
      blockers ≡ canonicalMuonNeutrinoIsolationBlockers

    promotionFlags :
      List MuonNeutrinoIsolationPromotion

    promotionFlagsAreEmpty :
      promotionFlags ≡ []

    receiptBoundary :
      String

    receiptBoundaryIsCanonical :
      receiptBoundary ≡ receiptBoundaryLabel

    auditTrail :
      List String

open MuonNeutrinoIsolationReceipt public

canonicalMuonNeutrinoIsolationReceipt :
  MuonNeutrinoIsolationReceipt
canonicalMuonNeutrinoIsolationReceipt =
  record
    { conductorLevelReceipt =
        Conductor.canonicalConductorLevelCorrespondenceReceipt
    ; leptonSectorGapReceipt =
        Gap.canonicalLeptonSectorGapReceipt
    ; status =
        levelElevenCoprimeToQuarkLevelsRecorded
    ; statusIsCoprimeDiagnostic =
        refl
    ; discriminant =
        Gap.D-11
    ; discriminantIsDMinusEleven =
        refl
    ; level =
        11
    ; levelIsEleven =
        refl
    ; p3QuarkLevel =
        3
    ; p3QuarkLevelIsThree =
        refl
    ; p2QuarkLevel =
        4
    ; p2QuarkLevelIsFour =
        refl
    ; p5QuarkLevel =
        7
    ; p5QuarkLevelIsSeven =
        refl
    ; gcdLevel11WithP3 =
        1
    ; gcdLevel11WithP3IsOne =
        refl
    ; gcdLevel11WithP2 =
        1
    ; gcdLevel11WithP2IsOne =
        refl
    ; gcdLevel11WithP5 =
        1
    ; gcdLevel11WithP5IsOne =
        refl
    ; coprimeWithP3 =
        gcdIsOne
    ; coprimeWithP3IsGcdOne =
        refl
    ; coprimeWithP2 =
        gcdIsOne
    ; coprimeWithP2IsGcdOne =
        refl
    ; coprimeWithP5 =
        gcdIsOne
    ; coprimeWithP5IsGcdOne =
        refl
    ; coprimeStatement =
        levelElevenCoprimeStatementLabel
    ; coprimeStatementIsCanonical =
        refl
    ; leadingYukawaStatus =
        noLeadingDirectQuarkLeptonYukawa
    ; leadingYukawaStatusIsNoDirectYukawa =
        refl
    ; leadingDirectQuarkLeptonYukawaPresent =
        false
    ; leadingDirectQuarkLeptonYukawaPresentIsFalse =
        refl
    ; leadingYukawaStatement =
        leadingYukawaStatementLabel
    ; leadingYukawaStatementIsCanonical =
        refl
    ; structuralDiagnosticOnly =
        true
    ; structuralDiagnosticOnlyIsTrue =
        refl
    ; exactLeptonPromotion =
        false
    ; exactLeptonPromotionIsFalse =
        refl
    ; exactQuarkPromotion =
        false
    ; exactQuarkPromotionIsFalse =
        refl
    ; exactStandardModelPromotion =
        false
    ; exactStandardModelPromotionIsFalse =
        refl
    ; exactGDHREqualsGSMPromotion =
        false
    ; exactGDHREqualsGSMPromotionIsFalse =
        refl
    ; terminalClaimPromoted =
        false
    ; terminalClaimPromotedIsFalse =
        refl
    ; blockers =
        canonicalMuonNeutrinoIsolationBlockers
    ; blockersAreCanonical =
        refl
    ; promotionFlags =
        []
    ; promotionFlagsAreEmpty =
        refl
    ; receiptBoundary =
        receiptBoundaryLabel
    ; receiptBoundaryIsCanonical =
        refl
    ; auditTrail =
        levelElevenCoprimeStatementLabel
        ∷ "gcd(11,3)=1, gcd(11,4)=1, and gcd(11,7)=1"
        ∷ leadingYukawaStatementLabel
        ∷ receiptBoundaryLabel
        ∷ []
    }

muonNeutrinoLevelElevenCoprimeToP3 :
  gcdLevel11WithP3 canonicalMuonNeutrinoIsolationReceipt ≡ 1
muonNeutrinoLevelElevenCoprimeToP3 =
  refl

muonNeutrinoLevelElevenCoprimeToP2 :
  gcdLevel11WithP2 canonicalMuonNeutrinoIsolationReceipt ≡ 1
muonNeutrinoLevelElevenCoprimeToP2 =
  refl

muonNeutrinoLevelElevenCoprimeToP5 :
  gcdLevel11WithP5 canonicalMuonNeutrinoIsolationReceipt ≡ 1
muonNeutrinoLevelElevenCoprimeToP5 =
  refl

muonNeutrinoNoLeadingDirectYukawa :
  leadingDirectQuarkLeptonYukawaPresent
    canonicalMuonNeutrinoIsolationReceipt
  ≡
  false
muonNeutrinoNoLeadingDirectYukawa =
  refl

muonNeutrinoIsolationNoPromotion :
  MuonNeutrinoIsolationPromotion →
  ⊥
muonNeutrinoIsolationNoPromotion =
  muonNeutrinoIsolationPromotionImpossibleHere
