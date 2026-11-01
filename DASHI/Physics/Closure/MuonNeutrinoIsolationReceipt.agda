module DASHI.Physics.Closure.MuonNeutrinoIsolationReceipt where

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)
open import Data.List.Base using (List; _∷_; [])

------------------------------------------------------------------------
-- Muon-neutrino isolation level-overlap candidate.
--
-- This receipt records one structural prediction in the level-overlap model:
-- the candidate muon-neutrino lane at discriminant -11 / level 11 has no gcd
-- overlap with the quark levels 3, 4, and 7.  At leading order in this model,
-- direct quark-lepton Yukawa overlap is therefore zero, while electroweak
-- gauge coupling remains the only leading-level coupling candidate.
--
-- This is not a physical neutrino, lepton, Yukawa, or Standard Model
-- promotion.  Terminal flags remain false.

data MuonNeutrinoIsolationStatus : Set where
  levelElevenNoQuarkLevelOverlapRecorded :
    MuonNeutrinoIsolationStatus

data MuonNeutrinoIsolationBlocker : Set where
  levelOverlapModelNotDerived :
    MuonNeutrinoIsolationBlocker

  muonNeutrinoLaneNotPhysicallyConstructed :
    MuonNeutrinoIsolationBlocker

  electroweakCouplingCandidateNotPromotion :
    MuonNeutrinoIsolationBlocker

  noNeutrinoMassOrMixingReceipt :
    MuonNeutrinoIsolationBlocker

canonicalMuonNeutrinoIsolationBlockers :
  List MuonNeutrinoIsolationBlocker
canonicalMuonNeutrinoIsolationBlockers =
  levelOverlapModelNotDerived
  ∷ muonNeutrinoLaneNotPhysicallyConstructed
  ∷ electroweakCouplingCandidateNotPromotion
  ∷ noNeutrinoMassOrMixingReceipt
  ∷ []

data MuonNeutrinoIsolationPromotion : Set where

muonNeutrinoIsolationPromotionImpossibleHere :
  MuonNeutrinoIsolationPromotion →
  ⊥
muonNeutrinoIsolationPromotionImpossibleHere ()

levelOverlapStatementLabel : String
levelOverlapStatementLabel =
  "disc -11 / level 11 has gcd overlap 1 with quark levels 3, 4, and 7"

leadingYukawaStatementLabel : String
leadingYukawaStatementLabel =
  "leading-order direct quark-lepton Yukawa is zero in the level-overlap model"

electroweakOnlyStatementLabel : String
electroweakOnlyStatementLabel =
  "electroweak gauge coupling only at leading level is a structural prediction/candidate"

record MuonNeutrinoIsolationReceipt : Setω where
  field
    status :
      MuonNeutrinoIsolationStatus

    discriminantAbs :
      Nat

    discriminantAbsIsEleven :
      discriminantAbs ≡ 11

    level :
      Nat

    levelIsEleven :
      level ≡ 11

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

    gcdLevel11With3 :
      Nat

    gcdLevel11With3IsOne :
      gcdLevel11With3 ≡ 1

    gcdLevel11With4 :
      Nat

    gcdLevel11With4IsOne :
      gcdLevel11With4 ≡ 1

    gcdLevel11With7 :
      Nat

    gcdLevel11With7IsOne :
      gcdLevel11With7 ≡ 1

    levelOverlapStatement :
      String

    levelOverlapStatementIsCanonical :
      levelOverlapStatement ≡ levelOverlapStatementLabel

    leadingOrderDirectYukawaZero :
      Bool

    leadingOrderDirectYukawaZeroIsTrue :
      leadingOrderDirectYukawaZero ≡ true

    leadingOrderDirectYukawaStatement :
      String

    leadingOrderDirectYukawaStatementIsCanonical :
      leadingOrderDirectYukawaStatement ≡ leadingYukawaStatementLabel

    electroweakGaugeCouplingOnlyAtLeadingLevel :
      Bool

    electroweakGaugeCouplingOnlyAtLeadingLevelIsTrue :
      electroweakGaugeCouplingOnlyAtLeadingLevel ≡ true

    electroweakGaugeCouplingStatement :
      String

    electroweakGaugeCouplingStatementIsCanonical :
      electroweakGaugeCouplingStatement ≡ electroweakOnlyStatementLabel

    structuralPredictionCandidateOnly :
      Bool

    structuralPredictionCandidateOnlyIsTrue :
      structuralPredictionCandidateOnly ≡ true

    physicalMuonNeutrinoConstructed :
      Bool

    physicalMuonNeutrinoConstructedIsFalse :
      physicalMuonNeutrinoConstructed ≡ false

    physicalLeptonMappingPromoted :
      Bool

    physicalLeptonMappingPromotedIsFalse :
      physicalLeptonMappingPromoted ≡ false

    physicalYukawaPromotion :
      Bool

    physicalYukawaPromotionIsFalse :
      physicalYukawaPromotion ≡ false

    physicalStandardModelPromotion :
      Bool

    physicalStandardModelPromotionIsFalse :
      physicalStandardModelPromotion ≡ false

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
      List String

open MuonNeutrinoIsolationReceipt public

canonicalMuonNeutrinoIsolationReceipt :
  MuonNeutrinoIsolationReceipt
canonicalMuonNeutrinoIsolationReceipt =
  record
    { status =
        levelElevenNoQuarkLevelOverlapRecorded
    ; discriminantAbs =
        11
    ; discriminantAbsIsEleven =
        refl
    ; level =
        11
    ; levelIsEleven =
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
    ; gcdLevel11With3 =
        1
    ; gcdLevel11With3IsOne =
        refl
    ; gcdLevel11With4 =
        1
    ; gcdLevel11With4IsOne =
        refl
    ; gcdLevel11With7 =
        1
    ; gcdLevel11With7IsOne =
        refl
    ; levelOverlapStatement =
        levelOverlapStatementLabel
    ; levelOverlapStatementIsCanonical =
        refl
    ; leadingOrderDirectYukawaZero =
        true
    ; leadingOrderDirectYukawaZeroIsTrue =
        refl
    ; leadingOrderDirectYukawaStatement =
        leadingYukawaStatementLabel
    ; leadingOrderDirectYukawaStatementIsCanonical =
        refl
    ; electroweakGaugeCouplingOnlyAtLeadingLevel =
        true
    ; electroweakGaugeCouplingOnlyAtLeadingLevelIsTrue =
        refl
    ; electroweakGaugeCouplingStatement =
        electroweakOnlyStatementLabel
    ; electroweakGaugeCouplingStatementIsCanonical =
        refl
    ; structuralPredictionCandidateOnly =
        true
    ; structuralPredictionCandidateOnlyIsTrue =
        refl
    ; physicalMuonNeutrinoConstructed =
        false
    ; physicalMuonNeutrinoConstructedIsFalse =
        refl
    ; physicalLeptonMappingPromoted =
        false
    ; physicalLeptonMappingPromotedIsFalse =
        refl
    ; physicalYukawaPromotion =
        false
    ; physicalYukawaPromotionIsFalse =
        refl
    ; physicalStandardModelPromotion =
        false
    ; physicalStandardModelPromotionIsFalse =
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
        "The candidate disc -11 / level 11 lane has gcd 1 with quark levels 3, 4, and 7"
        ∷ "In the level-overlap model this records zero leading-order direct quark-lepton Yukawa"
        ∷ "Electroweak gauge coupling only at leading level is recorded as structural prediction/candidate"
        ∷ "No physical muon-neutrino, lepton mapping, Yukawa, Standard Model, or terminal promotion is asserted"
        ∷ []
    }

muonNeutrinoIsolationGcdWithQuarkLevelsIsOne :
  gcdLevel11With3 canonicalMuonNeutrinoIsolationReceipt ≡ 1
muonNeutrinoIsolationGcdWithQuarkLevelsIsOne =
  refl

muonNeutrinoIsolationLeadingDirectYukawaZero :
  leadingOrderDirectYukawaZero canonicalMuonNeutrinoIsolationReceipt
  ≡
  true
muonNeutrinoIsolationLeadingDirectYukawaZero =
  refl

muonNeutrinoIsolationElectroweakOnlyCandidate :
  electroweakGaugeCouplingOnlyAtLeadingLevel
    canonicalMuonNeutrinoIsolationReceipt
  ≡
  true
muonNeutrinoIsolationElectroweakOnlyCandidate =
  refl

muonNeutrinoIsolationNoTerminalPromotion :
  terminalClaimPromoted canonicalMuonNeutrinoIsolationReceipt ≡ false
muonNeutrinoIsolationNoTerminalPromotion =
  refl
