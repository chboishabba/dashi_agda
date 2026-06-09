module DASHI.Physics.Closure.LeptonYukawaFromLevelOverlapReceipt where

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)
open import Data.List.Base using (List; _∷_; [])

import DASHI.Physics.Closure.D8LeptonLaneReceipt as D8

------------------------------------------------------------------------
-- Quark-lepton Yukawa from modular-level overlap receipt.
--
-- Candidate rule:
--
--   y_qℓ proportional to vol(X0(gcd(Nq,Nl))) / vol(X0(Nl)).
--
-- This receipt records only the exact generation-1 D=-4 quark / D=-8 lepton
-- overlap facts.  The ratio is rational because the common pi factor cancels:
-- psi(4)=6 gives vol(X0(4))=2*pi, psi(8)=12 gives vol(X0(8))=4*pi, and the
-- overlap ratio is 1/2.  Higher-generation D=-12 data are left as a string
-- candidate placeholder; no physical lepton Yukawa or SM promotion is made.

data LeptonYukawaLevelOverlapStatus : Set where
  levelOverlapCandidateRecordedNoPhysicalPromotion :
    LeptonYukawaLevelOverlapStatus

data LeptonYukawaLevelOverlapBlocker : Set where
  levelOverlapRuleNotDerived :
    LeptonYukawaLevelOverlapBlocker

  missingD12ExactVolumeFacts :
    LeptonYukawaLevelOverlapBlocker

  missingPhysicalLeptonYukawaNormalization :
    LeptonYukawaLevelOverlapBlocker

  missingQuarkLeptonDHRIntertwiner :
    LeptonYukawaLevelOverlapBlocker

  missingSMMatterPromotion :
    LeptonYukawaLevelOverlapBlocker

canonicalLeptonYukawaLevelOverlapBlockers :
  List LeptonYukawaLevelOverlapBlocker
canonicalLeptonYukawaLevelOverlapBlockers =
  levelOverlapRuleNotDerived
  ∷ missingD12ExactVolumeFacts
  ∷ missingPhysicalLeptonYukawaNormalization
  ∷ missingQuarkLeptonDHRIntertwiner
  ∷ missingSMMatterPromotion
  ∷ []

data LeptonYukawaLevelOverlapPromotion : Set where

leptonYukawaLevelOverlapPromotionImpossibleHere :
  LeptonYukawaLevelOverlapPromotion →
  ⊥
leptonYukawaLevelOverlapPromotionImpossibleHere ()

levelOverlapFormulaLabel : String
levelOverlapFormulaLabel =
  "candidate formula: y_qℓ proportional to vol(X0(gcd(Nq,Nl))) / vol(X0(Nl))"

psiFourLabel : String
psiFourLabel =
  "psi(4)=6 and vol(X0(4))=(pi/3)*6=2*pi"

psiEightLabel : String
psiEightLabel =
  "psi(8)=12 and vol(X0(8))=(pi/3)*12=4*pi"

genOneRatioLabel : String
genOneRatioLabel =
  "generation-1 D=-8 lepton with D=-4 quark overlap ratio is vol(X0(4))/vol(X0(8)) = 1/2"

d12PlaceholderLabel : String
d12PlaceholderLabel =
  "D=-12 generation-3 lepton candidate placeholder: exact level/psi/volume facts are not recorded in this A3 receipt"

record LevelOverlapVolumeDatum : Set where
  field
    level :
      Nat

    dedekindPsi :
      Nat

    volumePiNumerator :
      Nat

    volumePiDenominator :
      Nat

    label :
      String

open LevelOverlapVolumeDatum public

x04VolumeDatum :
  LevelOverlapVolumeDatum
x04VolumeDatum =
  record
    { level =
        4
    ; dedekindPsi =
        6
    ; volumePiNumerator =
        2
    ; volumePiDenominator =
        1
    ; label =
        psiFourLabel
    }

x08VolumeDatum :
  LevelOverlapVolumeDatum
x08VolumeDatum =
  record
    { level =
        8
    ; dedekindPsi =
        12
    ; volumePiNumerator =
        4
    ; volumePiDenominator =
        1
    ; label =
        psiEightLabel
    }

record LeptonYukawaFromLevelOverlapReceipt : Setω where
  field
    status :
      LeptonYukawaLevelOverlapStatus

    d8LeptonLane :
      D8.D8LeptonLaneReceipt

    d8LeptonLaneIsCanonical :
      d8LeptonLane ≡ D8.canonicalD8LeptonLaneReceipt

    d8LeptonLaneNotPromoted :
      D8.leptonSectorPromoted d8LeptonLane ≡ false

    levelOverlapFormula :
      String

    levelOverlapFormulaIsCanonical :
      levelOverlapFormula ≡ levelOverlapFormulaLabel

    quarkDiscriminant :
      String

    quarkDiscriminantIsDMinusFour :
      quarkDiscriminant ≡ "D=-4"

    quarkLevel :
      Nat

    quarkLevelIsFour :
      quarkLevel ≡ 4

    leptonDiscriminant :
      String

    leptonDiscriminantIsDMinusEight :
      leptonDiscriminant ≡ "D=-8"

    leptonLevel :
      Nat

    leptonLevelIsEight :
      leptonLevel ≡ 8

    gcdLevel :
      Nat

    gcdLevelIsFour :
      gcdLevel ≡ 4

    x04Volume :
      LevelOverlapVolumeDatum

    x04VolumeIsCanonical :
      x04Volume ≡ x04VolumeDatum

    psiFour :
      Nat

    psiFourIsSix :
      psiFour ≡ 6

    x04VolumePiNumerator :
      Nat

    x04VolumePiNumeratorIsTwo :
      x04VolumePiNumerator ≡ 2

    x04VolumePiDenominator :
      Nat

    x04VolumePiDenominatorIsOne :
      x04VolumePiDenominator ≡ 1

    x08Volume :
      LevelOverlapVolumeDatum

    x08VolumeIsCanonical :
      x08Volume ≡ x08VolumeDatum

    psiEight :
      Nat

    psiEightIsTwelve :
      psiEight ≡ 12

    x08VolumePiNumerator :
      Nat

    x08VolumePiNumeratorIsFour :
      x08VolumePiNumerator ≡ 4

    x08VolumePiDenominator :
      Nat

    x08VolumePiDenominatorIsOne :
      x08VolumePiDenominator ≡ 1

    genOneOverlapRatioNumerator :
      Nat

    genOneOverlapRatioNumeratorIsOne :
      genOneOverlapRatioNumerator ≡ 1

    genOneOverlapRatioDenominator :
      Nat

    genOneOverlapRatioDenominatorIsTwo :
      genOneOverlapRatioDenominator ≡ 2

    genOneOverlapRatioStatement :
      String

    genOneOverlapRatioStatementIsCanonical :
      genOneOverlapRatioStatement ≡ genOneRatioLabel

    d12GenerationThreeCandidate :
      String

    d12GenerationThreeCandidateIsPlaceholder :
      d12GenerationThreeCandidate ≡ d12PlaceholderLabel

    exactGenOneVolumeFactsRecorded :
      Bool

    exactGenOneVolumeFactsRecordedIsTrue :
      exactGenOneVolumeFactsRecorded ≡ true

    d12ExactFactsPromotedHere :
      Bool

    d12ExactFactsPromotedHereIsFalse :
      d12ExactFactsPromotedHere ≡ false

    levelOverlapRuleDerived :
      Bool

    levelOverlapRuleDerivedIsFalse :
      levelOverlapRuleDerived ≡ false

    physicalLeptonYukawaPromoted :
      Bool

    physicalLeptonYukawaPromotedIsFalse :
      physicalLeptonYukawaPromoted ≡ false

    physicalQuarkLeptonYukawaPromoted :
      Bool

    physicalQuarkLeptonYukawaPromotedIsFalse :
      physicalQuarkLeptonYukawaPromoted ≡ false

    smMatterPromoted :
      Bool

    smMatterPromotedIsFalse :
      smMatterPromoted ≡ false

    blockers :
      List LeptonYukawaLevelOverlapBlocker

    blockersAreCanonical :
      blockers ≡ canonicalLeptonYukawaLevelOverlapBlockers

    promotionFlags :
      List LeptonYukawaLevelOverlapPromotion

    promotionFlagsAreEmpty :
      promotionFlags ≡ []

    receiptBoundary :
      List String

open LeptonYukawaFromLevelOverlapReceipt public

canonicalLeptonYukawaFromLevelOverlapReceipt :
  LeptonYukawaFromLevelOverlapReceipt
canonicalLeptonYukawaFromLevelOverlapReceipt =
  record
    { status =
        levelOverlapCandidateRecordedNoPhysicalPromotion
    ; d8LeptonLane =
        D8.canonicalD8LeptonLaneReceipt
    ; d8LeptonLaneIsCanonical =
        refl
    ; d8LeptonLaneNotPromoted =
        D8.d8LeptonLaneDoesNotPromoteLeptons
    ; levelOverlapFormula =
        levelOverlapFormulaLabel
    ; levelOverlapFormulaIsCanonical =
        refl
    ; quarkDiscriminant =
        "D=-4"
    ; quarkDiscriminantIsDMinusFour =
        refl
    ; quarkLevel =
        4
    ; quarkLevelIsFour =
        refl
    ; leptonDiscriminant =
        "D=-8"
    ; leptonDiscriminantIsDMinusEight =
        refl
    ; leptonLevel =
        8
    ; leptonLevelIsEight =
        refl
    ; gcdLevel =
        4
    ; gcdLevelIsFour =
        refl
    ; x04Volume =
        x04VolumeDatum
    ; x04VolumeIsCanonical =
        refl
    ; psiFour =
        6
    ; psiFourIsSix =
        refl
    ; x04VolumePiNumerator =
        2
    ; x04VolumePiNumeratorIsTwo =
        refl
    ; x04VolumePiDenominator =
        1
    ; x04VolumePiDenominatorIsOne =
        refl
    ; x08Volume =
        x08VolumeDatum
    ; x08VolumeIsCanonical =
        refl
    ; psiEight =
        12
    ; psiEightIsTwelve =
        refl
    ; x08VolumePiNumerator =
        4
    ; x08VolumePiNumeratorIsFour =
        refl
    ; x08VolumePiDenominator =
        1
    ; x08VolumePiDenominatorIsOne =
        refl
    ; genOneOverlapRatioNumerator =
        1
    ; genOneOverlapRatioNumeratorIsOne =
        refl
    ; genOneOverlapRatioDenominator =
        2
    ; genOneOverlapRatioDenominatorIsTwo =
        refl
    ; genOneOverlapRatioStatement =
        genOneRatioLabel
    ; genOneOverlapRatioStatementIsCanonical =
        refl
    ; d12GenerationThreeCandidate =
        d12PlaceholderLabel
    ; d12GenerationThreeCandidateIsPlaceholder =
        refl
    ; exactGenOneVolumeFactsRecorded =
        true
    ; exactGenOneVolumeFactsRecordedIsTrue =
        refl
    ; d12ExactFactsPromotedHere =
        false
    ; d12ExactFactsPromotedHereIsFalse =
        refl
    ; levelOverlapRuleDerived =
        false
    ; levelOverlapRuleDerivedIsFalse =
        refl
    ; physicalLeptonYukawaPromoted =
        false
    ; physicalLeptonYukawaPromotedIsFalse =
        refl
    ; physicalQuarkLeptonYukawaPromoted =
        false
    ; physicalQuarkLeptonYukawaPromotedIsFalse =
        refl
    ; smMatterPromoted =
        false
    ; smMatterPromotedIsFalse =
        refl
    ; blockers =
        canonicalLeptonYukawaLevelOverlapBlockers
    ; blockersAreCanonical =
        refl
    ; promotionFlags =
        []
    ; promotionFlagsAreEmpty =
        refl
    ; receiptBoundary =
        "Candidate rule recorded: y_qℓ proportional to vol(X0(gcd(Nq,Nl))) / vol(X0(Nl))"
        ∷ "For D=-4 and D=-8, gcd(4,8)=4"
        ∷ "Exact facts recorded: psi(4)=6, vol(X0(4))=2*pi, psi(8)=12, vol(X0(8))=4*pi"
        ∷ "The generation-1 overlap ratio is therefore (2*pi)/(4*pi)=1/2"
        ∷ "D=-12 generation-3 data are left as a candidate placeholder pending exact facts from the owning lane"
        ∷ "No physical lepton Yukawa, quark-lepton Yukawa, or SM matter promotion is asserted"
        ∷ []
    }

leptonYukawaOverlapRecordsGenOneRatio :
  genOneOverlapRatioNumerator canonicalLeptonYukawaFromLevelOverlapReceipt
  ≡
  1
leptonYukawaOverlapRecordsGenOneRatio =
  refl

leptonYukawaOverlapRecordsGenOneDenominator :
  genOneOverlapRatioDenominator canonicalLeptonYukawaFromLevelOverlapReceipt
  ≡
  2
leptonYukawaOverlapRecordsGenOneDenominator =
  refl

leptonYukawaOverlapDoesNotDeriveRule :
  levelOverlapRuleDerived canonicalLeptonYukawaFromLevelOverlapReceipt
  ≡
  false
leptonYukawaOverlapDoesNotDeriveRule =
  refl

leptonYukawaOverlapDoesNotPromoteLeptonYukawa :
  physicalLeptonYukawaPromoted canonicalLeptonYukawaFromLevelOverlapReceipt
  ≡
  false
leptonYukawaOverlapDoesNotPromoteLeptonYukawa =
  refl

leptonYukawaOverlapDoesNotPromoteSM :
  smMatterPromoted canonicalLeptonYukawaFromLevelOverlapReceipt
  ≡
  false
leptonYukawaOverlapDoesNotPromoteSM =
  refl
