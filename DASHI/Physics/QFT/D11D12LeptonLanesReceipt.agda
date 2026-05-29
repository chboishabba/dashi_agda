module DASHI.Physics.QFT.D11D12LeptonLanesReceipt where

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)
open import Data.Integer.Base using (ℤ; +_; -[1+_])
open import Data.List.Base using (List; _∷_; [])

------------------------------------------------------------------------
-- D=-11 and D=-12 lepton-lane candidate receipt.
--
-- This receipt narrows the lepton-lane bookkeeping for the two open
-- class-number-1 candidates immediately beyond the active p2/p3/p5 window.
-- Both rows remain candidate/open.  The D=-12 row distinguishes the order
-- conductor 2 in Q(sqrt(-3)) from the Dirichlet/level conductor 12 record.
-- No lepton sector, exact SM assignment, or G_DHR ~= G_SM promotion is made.

data D11D12LeptonLaneDiscriminant : Set where
  D-11 :
    D11D12LeptonLaneDiscriminant

  D-12 :
    D11D12LeptonLaneDiscriminant

data LeptonLaneCandidateStatus : Set where
  leptonLaneCandidateOpen :
    LeptonLaneCandidateStatus

data UnitGroupRecord : Set where
  z2UnitGroup :
    UnitGroupRecord

data BaseCMField : Set where
  qSqrtMinusEleven :
    BaseCMField

  qSqrtMinusThree :
    BaseCMField

data OrderConductorRecord : Set where
  maximalOrderConductorOne :
    OrderConductorRecord

  orderConductorTwoInQSqrtMinusThree :
    OrderConductorRecord

data CharacterConductorRecord : Set where
  characterConductorEleven :
    CharacterConductorRecord

  dirichletLevelTwelve :
    CharacterConductorRecord

data LeptonLaneBlocker : Set where
  missingExactLeptonRepresentation :
    LeptonLaneBlocker

  missingDHRToSMLeptonFunctor :
    LeptonLaneBlocker

  dMinusElevenNoSMPromotion :
    LeptonLaneBlocker

  dMinusTwelveOrderConductorLevelDistinctionOpen :
    LeptonLaneBlocker

canonicalLeptonLaneBlockers :
  List LeptonLaneBlocker
canonicalLeptonLaneBlockers =
  missingExactLeptonRepresentation
  ∷ missingDHRToSMLeptonFunctor
  ∷ dMinusElevenNoSMPromotion
  ∷ dMinusTwelveOrderConductorLevelDistinctionOpen
  ∷ []

dMinusElevenDiscriminantValue :
  ℤ
dMinusElevenDiscriminantValue =
  -[1+ 10 ]

dMinusTwelveDiscriminantValue :
  ℤ
dMinusTwelveDiscriminantValue =
  -[1+ 11 ]

dMinusElevenJInvariant :
  ℤ
dMinusElevenJInvariant =
  -[1+ 32767 ]

dMinusTwelveJInvariant :
  ℤ
dMinusTwelveJInvariant =
  + 54000

canonicalDiscriminantValue :
  D11D12LeptonLaneDiscriminant →
  ℤ
canonicalDiscriminantValue D-11 =
  dMinusElevenDiscriminantValue
canonicalDiscriminantValue D-12 =
  dMinusTwelveDiscriminantValue

canonicalCandidateConductorOrLevel :
  D11D12LeptonLaneDiscriminant →
  Nat
canonicalCandidateConductorOrLevel D-11 =
  11
canonicalCandidateConductorOrLevel D-12 =
  12

dMinusElevenLabel :
  String
dMinusElevenLabel =
  "D=-11: j=-32768, unit group Z/2, conductor/character conductor 11, |E(F11)|=12, vol X0(11)=4*pi"

dMinusTwelveLabel :
  String
dMinusTwelveLabel =
  "D=-12: order conductor 2 in Q(sqrt(-3)), class number 1, j=54000, unit group Z/2, Dirichlet/level conductor 12"

receiptBoundaryLabel :
  String
receiptBoundaryLabel =
  "D=-11 and D=-12 are recorded as open lepton-lane candidates only; no lepton sector or exact Standard Model promotion is supplied"

record D11D12LeptonLaneCandidate : Set where
  field
    discriminant :
      D11D12LeptonLaneDiscriminant

    discriminantValue :
      ℤ

    discriminantValueIsCanonical :
      discriminantValue
      ≡
      canonicalDiscriminantValue discriminant

    baseCMField :
      BaseCMField

    classNumber :
      Nat

    classNumberIsOne :
      classNumber ≡ 1

    jInvariant :
      ℤ

    unitGroup :
      UnitGroupRecord

    unitGroupIsZ2 :
      unitGroup ≡ z2UnitGroup

    orderConductor :
      OrderConductorRecord

    characterConductor :
      CharacterConductorRecord

    candidateConductorOrLevel :
      Nat

    candidateConductorOrLevelIsCanonical :
      candidateConductorOrLevel
      ≡
      canonicalCandidateConductorOrLevel discriminant

    finiteFieldPointCount :
      Nat

    x0Level :
      Nat

    volumeNumerator :
      Nat

    volumeDenominator :
      Nat

    volumeSymbol :
      String

    status :
      LeptonLaneCandidateStatus

    statusIsOpen :
      status ≡ leptonLaneCandidateOpen

    candidateStatement :
      String

open D11D12LeptonLaneCandidate public

dMinusElevenLeptonLaneCandidate :
  D11D12LeptonLaneCandidate
dMinusElevenLeptonLaneCandidate =
  record
    { discriminant =
        D-11
    ; discriminantValue =
        dMinusElevenDiscriminantValue
    ; discriminantValueIsCanonical =
        refl
    ; baseCMField =
        qSqrtMinusEleven
    ; classNumber =
        1
    ; classNumberIsOne =
        refl
    ; jInvariant =
        dMinusElevenJInvariant
    ; unitGroup =
        z2UnitGroup
    ; unitGroupIsZ2 =
        refl
    ; orderConductor =
        maximalOrderConductorOne
    ; characterConductor =
        characterConductorEleven
    ; candidateConductorOrLevel =
        11
    ; candidateConductorOrLevelIsCanonical =
        refl
    ; finiteFieldPointCount =
        12
    ; x0Level =
        11
    ; volumeNumerator =
        4
    ; volumeDenominator =
        1
    ; volumeSymbol =
        "pi"
    ; status =
        leptonLaneCandidateOpen
    ; statusIsOpen =
        refl
    ; candidateStatement =
        dMinusElevenLabel
    }

dMinusTwelveLeptonLaneCandidate :
  D11D12LeptonLaneCandidate
dMinusTwelveLeptonLaneCandidate =
  record
    { discriminant =
        D-12
    ; discriminantValue =
        dMinusTwelveDiscriminantValue
    ; discriminantValueIsCanonical =
        refl
    ; baseCMField =
        qSqrtMinusThree
    ; classNumber =
        1
    ; classNumberIsOne =
        refl
    ; jInvariant =
        dMinusTwelveJInvariant
    ; unitGroup =
        z2UnitGroup
    ; unitGroupIsZ2 =
        refl
    ; orderConductor =
        orderConductorTwoInQSqrtMinusThree
    ; characterConductor =
        dirichletLevelTwelve
    ; candidateConductorOrLevel =
        12
    ; candidateConductorOrLevelIsCanonical =
        refl
    ; finiteFieldPointCount =
        0
    ; x0Level =
        12
    ; volumeNumerator =
        0
    ; volumeDenominator =
        1
    ; volumeSymbol =
        "not recorded here"
    ; status =
        leptonLaneCandidateOpen
    ; statusIsOpen =
        refl
    ; candidateStatement =
        dMinusTwelveLabel
    }

canonicalD11D12LeptonLaneCandidates :
  List D11D12LeptonLaneCandidate
canonicalD11D12LeptonLaneCandidates =
  dMinusElevenLeptonLaneCandidate
  ∷ dMinusTwelveLeptonLaneCandidate
  ∷ []

record D11D12LeptonLanesReceipt : Setω where
  field
    candidates :
      List D11D12LeptonLaneCandidate

    candidatesAreCanonical :
      candidates ≡ canonicalD11D12LeptonLaneCandidates

    dMinusElevenCandidate :
      D11D12LeptonLaneCandidate

    dMinusElevenCandidateIsCanonical :
      dMinusElevenCandidate ≡ dMinusElevenLeptonLaneCandidate

    dMinusElevenDiscriminantIsMinusEleven :
      discriminantValue dMinusElevenCandidate
      ≡
      -[1+ 10 ]

    dMinusElevenJInvariantIsMinus32768 :
      jInvariant dMinusElevenCandidate
      ≡
      -[1+ 32767 ]

    dMinusElevenUnitGroupIsZ2 :
      unitGroup dMinusElevenCandidate ≡ z2UnitGroup

    dMinusElevenConductorIsEleven :
      candidateConductorOrLevel dMinusElevenCandidate ≡ 11

    dMinusElevenCharacterConductorIsEleven :
      characterConductor dMinusElevenCandidate ≡ characterConductorEleven

    dMinusElevenEF11CountIsTwelve :
      finiteFieldPointCount dMinusElevenCandidate ≡ 12

    dMinusElevenX0LevelIsEleven :
      x0Level dMinusElevenCandidate ≡ 11

    dMinusElevenVolumeIsFourPi :
      volumeNumerator dMinusElevenCandidate ≡ 4

    dMinusTwelveCandidate :
      D11D12LeptonLaneCandidate

    dMinusTwelveCandidateIsCanonical :
      dMinusTwelveCandidate ≡ dMinusTwelveLeptonLaneCandidate

    dMinusTwelveDiscriminantIsMinusTwelve :
      discriminantValue dMinusTwelveCandidate
      ≡
      -[1+ 11 ]

    dMinusTwelveOrderConductorIsTwoInQSqrtMinusThree :
      orderConductor dMinusTwelveCandidate
      ≡
      orderConductorTwoInQSqrtMinusThree

    dMinusTwelveBaseFieldIsQSqrtMinusThree :
      baseCMField dMinusTwelveCandidate ≡ qSqrtMinusThree

    dMinusTwelveClassNumberIsOne :
      classNumber dMinusTwelveCandidate ≡ 1

    dMinusTwelveJInvariantIs54000 :
      jInvariant dMinusTwelveCandidate ≡ + 54000

    dMinusTwelveUnitGroupIsZ2 :
      unitGroup dMinusTwelveCandidate ≡ z2UnitGroup

    dMinusTwelveDirichletLevelIsTwelve :
      candidateConductorOrLevel dMinusTwelveCandidate ≡ 12

    dMinusTwelveCharacterConductorIsLevelTwelve :
      characterConductor dMinusTwelveCandidate ≡ dirichletLevelTwelve

    orderConductorAndDirichletLevelDistinguished :
      Bool

    orderConductorAndDirichletLevelDistinguishedIsTrue :
      orderConductorAndDirichletLevelDistinguished ≡ true

    leptonSectorCandidateOpen :
      Bool

    leptonSectorCandidateOpenIsTrue :
      leptonSectorCandidateOpen ≡ true

    leptonSectorConstructed :
      Bool

    leptonSectorConstructedIsFalse :
      leptonSectorConstructed ≡ false

    exactStandardModelPromotion :
      Bool

    exactStandardModelPromotionIsFalse :
      exactStandardModelPromotion ≡ false

    gDHREqualsGSMPromoted :
      Bool

    gDHREqualsGSMPromotedIsFalse :
      gDHREqualsGSMPromoted ≡ false

    blockers :
      List LeptonLaneBlocker

    blockersAreCanonical :
      blockers ≡ canonicalLeptonLaneBlockers

    receiptBoundary :
      String

    receiptBoundaryIsCanonical :
      receiptBoundary ≡ receiptBoundaryLabel

    auditTrail :
      List String

open D11D12LeptonLanesReceipt public

canonicalD11D12LeptonLanesReceipt :
  D11D12LeptonLanesReceipt
canonicalD11D12LeptonLanesReceipt =
  record
    { candidates =
        canonicalD11D12LeptonLaneCandidates
    ; candidatesAreCanonical =
        refl
    ; dMinusElevenCandidate =
        dMinusElevenLeptonLaneCandidate
    ; dMinusElevenCandidateIsCanonical =
        refl
    ; dMinusElevenDiscriminantIsMinusEleven =
        refl
    ; dMinusElevenJInvariantIsMinus32768 =
        refl
    ; dMinusElevenUnitGroupIsZ2 =
        refl
    ; dMinusElevenConductorIsEleven =
        refl
    ; dMinusElevenCharacterConductorIsEleven =
        refl
    ; dMinusElevenEF11CountIsTwelve =
        refl
    ; dMinusElevenX0LevelIsEleven =
        refl
    ; dMinusElevenVolumeIsFourPi =
        refl
    ; dMinusTwelveCandidate =
        dMinusTwelveLeptonLaneCandidate
    ; dMinusTwelveCandidateIsCanonical =
        refl
    ; dMinusTwelveDiscriminantIsMinusTwelve =
        refl
    ; dMinusTwelveOrderConductorIsTwoInQSqrtMinusThree =
        refl
    ; dMinusTwelveBaseFieldIsQSqrtMinusThree =
        refl
    ; dMinusTwelveClassNumberIsOne =
        refl
    ; dMinusTwelveJInvariantIs54000 =
        refl
    ; dMinusTwelveUnitGroupIsZ2 =
        refl
    ; dMinusTwelveDirichletLevelIsTwelve =
        refl
    ; dMinusTwelveCharacterConductorIsLevelTwelve =
        refl
    ; orderConductorAndDirichletLevelDistinguished =
        true
    ; orderConductorAndDirichletLevelDistinguishedIsTrue =
        refl
    ; leptonSectorCandidateOpen =
        true
    ; leptonSectorCandidateOpenIsTrue =
        refl
    ; leptonSectorConstructed =
        false
    ; leptonSectorConstructedIsFalse =
        refl
    ; exactStandardModelPromotion =
        false
    ; exactStandardModelPromotionIsFalse =
        refl
    ; gDHREqualsGSMPromoted =
        false
    ; gDHREqualsGSMPromotedIsFalse =
        refl
    ; blockers =
        canonicalLeptonLaneBlockers
    ; blockersAreCanonical =
        refl
    ; receiptBoundary =
        receiptBoundaryLabel
    ; receiptBoundaryIsCanonical =
        refl
    ; auditTrail =
        dMinusElevenLabel
        ∷ dMinusTwelveLabel
        ∷ "D=-12 order conductor 2 is not conflated with Dirichlet/level conductor 12"
        ∷ "Both candidates remain open lepton-lane data; no SM promotion is recorded"
        ∷ []
    }

dMinusElevenLaneRemainsOpen :
  status dMinusElevenLeptonLaneCandidate
  ≡
  leptonLaneCandidateOpen
dMinusElevenLaneRemainsOpen =
  refl

dMinusTwelveLaneRemainsOpen :
  status dMinusTwelveLeptonLaneCandidate
  ≡
  leptonLaneCandidateOpen
dMinusTwelveLaneRemainsOpen =
  refl

d11D12NoLeptonSectorConstruction :
  leptonSectorConstructed canonicalD11D12LeptonLanesReceipt
  ≡
  false
d11D12NoLeptonSectorConstruction =
  refl

d11D12NoStandardModelPromotion :
  exactStandardModelPromotion canonicalD11D12LeptonLanesReceipt
  ≡
  false
d11D12NoStandardModelPromotion =
  refl
