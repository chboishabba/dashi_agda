module DASHI.Foundations.SurrealCompactificationIntake where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Agda.Builtin.String using (String)
open import Data.List.Base using (List; []; _∷_)
open import Data.Rational using (ℚ)

open import DASHI.Algebra.Trit using (Trit; neg; zer; pos)
import DASHI.Foundations.SurrealCompactification as SC

------------------------------------------------------------------------
-- Boundary-only intake contract.
--
-- This module records the exact carrier and lemma surface needed before a
-- rational/surreal compactification bridge may be promoted.  It constructs
-- only finite symbolic shapes and fail-closed request records.  It does not
-- construct No, QQ, rational order, a rational-valued 3^-n metric, a
-- truncation error theorem, or a tail bound.

data Empty : Set where

data CarrierShape : Set where
  noSurrealCarrier :
    CarrierShape

  qqRationalCarrier :
    CarrierShape

data BridgeVariable : Set where
  depthN :
    BridgeVariable

  depthM :
    BridgeVariable

  truncationDepthK :
    BridgeVariable

  kappaTolerance :
    BridgeVariable

  tailStartN :
    BridgeVariable

canonicalBridgeVariables : List BridgeVariable
canonicalBridgeVariables =
  depthN
  ∷ depthM
  ∷ truncationDepthK
  ∷ kappaTolerance
  ∷ tailStartN
  ∷ []

record CarrierAuthorityGate : Set where
  field
    carrierShape :
      CarrierShape

    carrierName :
      String

    externalAuthorityRequired :
      Bool

    externalAuthorityRequiredIsTrue :
      externalAuthorityRequired ≡ true

    constructedHere :
      Bool

    constructedHereIsFalse :
      constructedHere ≡ false

    promotedHere :
      Bool

    promotedHereIsFalse :
      promotedHere ≡ false

open CarrierAuthorityGate public

noCarrierAuthorityGate : CarrierAuthorityGate
noCarrierAuthorityGate =
  record
    { carrierShape =
        noSurrealCarrier
    ; carrierName =
        "No surreal-number carrier"
    ; externalAuthorityRequired =
        true
    ; externalAuthorityRequiredIsTrue =
        refl
    ; constructedHere =
        false
    ; constructedHereIsFalse =
        refl
    ; promotedHere =
        false
    ; promotedHereIsFalse =
        refl
    }

qqCarrierAuthorityGate : CarrierAuthorityGate
qqCarrierAuthorityGate =
  record
    { carrierShape =
        qqRationalCarrier
    ; carrierName =
        "QQ rational carrier"
    ; externalAuthorityRequired =
        true
    ; externalAuthorityRequiredIsTrue =
        refl
    ; constructedHere =
        false
    ; constructedHereIsFalse =
        refl
    ; promotedHere =
        false
    ; promotedHereIsFalse =
        refl
    }

record NoQQCarrierBridgeIntake : Set where
  field
    noGate :
      CarrierAuthorityGate

    noGateIsCanonical :
      noGate ≡ noCarrierAuthorityGate

    qqGate :
      CarrierAuthorityGate

    qqGateIsCanonical :
      qqGate ≡ qqCarrierAuthorityGate

    carrierMapShape :
      String

    carrierMapShapeIsNoToQQ :
      carrierMapShape ≡ "finite balanced ternary approximants -> QQ -> No"

    bridgeVariables :
      List BridgeVariable

    bridgeVariablesAreCanonical :
      bridgeVariables ≡ canonicalBridgeVariables

open NoQQCarrierBridgeIntake public

canonicalNoQQCarrierBridgeIntake : NoQQCarrierBridgeIntake
canonicalNoQQCarrierBridgeIntake =
  record
    { noGate =
        noCarrierAuthorityGate
    ; noGateIsCanonical =
        refl
    ; qqGate =
        qqCarrierAuthorityGate
    ; qqGateIsCanonical =
        refl
    ; carrierMapShape =
        "finite balanced ternary approximants -> QQ -> No"
    ; carrierMapShapeIsNoToQQ =
        refl
    ; bridgeVariables =
        canonicalBridgeVariables
    ; bridgeVariablesAreCanonical =
        refl
    }

------------------------------------------------------------------------
-- Checked finite balanced-ternary digit embedding.

data BalancedTernaryDigit : Set where
  minusOneDigit :
    BalancedTernaryDigit

  zeroDigit :
    BalancedTernaryDigit

  plusOneDigit :
    BalancedTernaryDigit

balancedTernaryEmbedDigit :
  Trit →
  BalancedTernaryDigit
balancedTernaryEmbedDigit neg =
  minusOneDigit
balancedTernaryEmbedDigit zer =
  zeroDigit
balancedTernaryEmbedDigit pos =
  plusOneDigit

negEmbedsToMinusOne :
  balancedTernaryEmbedDigit neg ≡ minusOneDigit
negEmbedsToMinusOne =
  refl

zerEmbedsToZero :
  balancedTernaryEmbedDigit zer ≡ zeroDigit
zerEmbedsToZero =
  refl

posEmbedsToPlusOne :
  balancedTernaryEmbedDigit pos ≡ plusOneDigit
posEmbedsToPlusOne =
  refl

embedTower :
  {depth : Nat} →
  SC.FiniteTritTower depth →
  SC.Vec BalancedTernaryDigit depth
embedTower SC.emptyTower =
  SC.[]
embedTower (SC.extendTower tower trit) =
  SC._∷_ (balancedTernaryEmbedDigit trit) (embedTower tower)

emptyTowerEmbedsToEmpty :
  embedTower SC.emptyTower ≡ SC.[]
emptyTowerEmbedsToEmpty =
  refl

extendTowerEmbedsPointwise :
  {depth : Nat} →
  (tower : SC.FiniteTritTower depth) →
  (trit : Trit) →
  embedTower (SC.extendTower tower trit)
  ≡
  SC._∷_ (balancedTernaryEmbedDigit trit) (embedTower tower)
extendTowerEmbedsPointwise tower trit =
  refl

record BalancedTernaryEmbeddingIntake : Set₁ where
  field
    sourceDigitCarrier :
      Set

    sourceDigitCarrierIsTrit :
      sourceDigitCarrier ≡ Trit

    targetDigitCarrier :
      Set

    targetDigitCarrierIsBalancedTernaryDigit :
      targetDigitCarrier ≡ BalancedTernaryDigit

    finiteTowerCarrier :
      Nat →
      Set

    finiteTowerCarrierIsSurrealCompactificationTower :
      finiteTowerCarrier ≡ SC.FiniteTritTower

    digitEmbedding :
      Trit →
      BalancedTernaryDigit

    digitEmbeddingIsCanonical :
      digitEmbedding ≡ balancedTernaryEmbedDigit

    negReceipt :
      digitEmbedding neg ≡ minusOneDigit

    zerReceipt :
      digitEmbedding zer ≡ zeroDigit

    posReceipt :
      digitEmbedding pos ≡ plusOneDigit

    extensionToQQRequired :
      Bool

    extensionToQQRequiredIsTrue :
      extensionToQQRequired ≡ true

    extensionToQQConstructedHere :
      Bool

    extensionToQQConstructedHereIsFalse :
      extensionToQQConstructedHere ≡ false

open BalancedTernaryEmbeddingIntake public

canonicalBalancedTernaryEmbeddingIntake :
  BalancedTernaryEmbeddingIntake
canonicalBalancedTernaryEmbeddingIntake =
  record
    { sourceDigitCarrier =
        Trit
    ; sourceDigitCarrierIsTrit =
        refl
    ; targetDigitCarrier =
        BalancedTernaryDigit
    ; targetDigitCarrierIsBalancedTernaryDigit =
        refl
    ; finiteTowerCarrier =
        SC.FiniteTritTower
    ; finiteTowerCarrierIsSurrealCompactificationTower =
        refl
    ; digitEmbedding =
        balancedTernaryEmbedDigit
    ; digitEmbeddingIsCanonical =
        refl
    ; negReceipt =
        refl
    ; zerReceipt =
        refl
    ; posReceipt =
        refl
    ; extensionToQQRequired =
        true
    ; extensionToQQRequiredIsTrue =
        refl
    ; extensionToQQConstructedHere =
        false
    ; extensionToQQConstructedHereIsFalse =
        refl
    }

------------------------------------------------------------------------
-- Symbolic 3^-n gauge and analytic obligations.

data SymbolicGauge : Set where
  threeToMinus :
    Nat →
    SymbolicGauge

symbolicThreeMinusGauge :
  Nat →
  SymbolicGauge
symbolicThreeMinusGauge n =
  threeToMinus n

record SymbolicThreeMinusNGaugeIntake (n : Nat) : Set where
  field
    gaugeTerm :
      SymbolicGauge

    gaugeTermIsThreeToMinusN :
      gaugeTerm ≡ threeToMinus n

    base :
      Nat

    baseIsThree :
      base ≡ 3

    exponentDepth :
      Nat

    exponentDepthIsN :
      exponentDepth ≡ n

    rationalValueRequired :
      Bool

    rationalValueRequiredIsTrue :
      rationalValueRequired ≡ true

    rationalValueConstructedHere :
      Bool

    rationalValueConstructedHereIsFalse :
      rationalValueConstructedHere ≡ false

open SymbolicThreeMinusNGaugeIntake public

canonicalSymbolicThreeMinusNGaugeIntake :
  (n : Nat) →
  SymbolicThreeMinusNGaugeIntake n
canonicalSymbolicThreeMinusNGaugeIntake n =
  record
    { gaugeTerm =
        symbolicThreeMinusGauge n
    ; gaugeTermIsThreeToMinusN =
        refl
    ; base =
        3
    ; baseIsThree =
        refl
    ; exponentDepth =
        n
    ; exponentDepthIsN =
        refl
    ; rationalValueRequired =
        true
    ; rationalValueRequiredIsTrue =
        refl
    ; rationalValueConstructedHere =
        false
    ; rationalValueConstructedHereIsFalse =
        refl
    }

record AntitoneGaugeLemmaIntake (m n : Nat) : Set where
  field
    premiseShape :
      String

    premiseShapeIsOrderOnNat :
      premiseShape ≡ "m <= n"

    conclusionShape :
      String

    conclusionShapeIsAntitoneGauge :
      conclusionShape ≡ "3^-n <= 3^-m in QQ"

    natOrderVariablesRecorded :
      List BridgeVariable

    natOrderVariablesAreCanonical :
      natOrderVariablesRecorded ≡ depthM ∷ depthN ∷ []

    rationalOrderAuthorityRequired :
      Bool

    rationalOrderAuthorityRequiredIsTrue :
      rationalOrderAuthorityRequired ≡ true

    antitoneLemmaProvedHere :
      Bool

    antitoneLemmaProvedHereIsFalse :
      antitoneLemmaProvedHere ≡ false

open AntitoneGaugeLemmaIntake public

canonicalAntitoneGaugeLemmaIntake :
  (m n : Nat) →
  AntitoneGaugeLemmaIntake m n
canonicalAntitoneGaugeLemmaIntake m n =
  record
    { premiseShape =
        "m <= n"
    ; premiseShapeIsOrderOnNat =
        refl
    ; conclusionShape =
        "3^-n <= 3^-m in QQ"
    ; conclusionShapeIsAntitoneGauge =
        refl
    ; natOrderVariablesRecorded =
        depthM ∷ depthN ∷ []
    ; natOrderVariablesAreCanonical =
        refl
    ; rationalOrderAuthorityRequired =
        true
    ; rationalOrderAuthorityRequiredIsTrue =
        refl
    ; antitoneLemmaProvedHere =
        false
    ; antitoneLemmaProvedHereIsFalse =
        refl
    }

data TruncationShape : Set where
  truncateAtDepth :
    Nat →
    TruncationShape

data KappaShape : Set where
  kappaOfDepth :
    Nat →
    KappaShape

record TruncationKappaIntake (k : Nat) : Set where
  field
    truncation :
      TruncationShape

    truncationIsAtK :
      truncation ≡ truncateAtDepth k

    kappa :
      KappaShape

    kappaIsAtK :
      kappa ≡ kappaOfDepth k

    truncationVariableRecorded :
      BridgeVariable

    truncationVariableIsK :
      truncationVariableRecorded ≡ truncationDepthK

    kappaVariableRecorded :
      BridgeVariable

    kappaVariableIsTolerance :
      kappaVariableRecorded ≡ kappaTolerance

    truncationAuthorityRequired :
      Bool

    truncationAuthorityRequiredIsTrue :
      truncationAuthorityRequired ≡ true

    truncationBoundProvedHere :
      Bool

    truncationBoundProvedHereIsFalse :
      truncationBoundProvedHere ≡ false

open TruncationKappaIntake public

canonicalTruncationKappaIntake :
  (k : Nat) →
  TruncationKappaIntake k
canonicalTruncationKappaIntake k =
  record
    { truncation =
        truncateAtDepth k
    ; truncationIsAtK =
        refl
    ; kappa =
        kappaOfDepth k
    ; kappaIsAtK =
        refl
    ; truncationVariableRecorded =
        truncationDepthK
    ; truncationVariableIsK =
        refl
    ; kappaVariableRecorded =
        kappaTolerance
    ; kappaVariableIsTolerance =
        refl
    ; truncationAuthorityRequired =
        true
    ; truncationAuthorityRequiredIsTrue =
        refl
    ; truncationBoundProvedHere =
        false
    ; truncationBoundProvedHereIsFalse =
        refl
    }

data TailBoundShape : Set where
  ternaryTailFrom :
    Nat →
    TailBoundShape

record TailBoundIntake (n : Nat) : Set where
  field
    tailShape :
      TailBoundShape

    tailShapeIsFromN :
      tailShape ≡ ternaryTailFrom n

    boundFormula :
      String

    boundFormulaIsCanonical :
      boundFormula ≡ "sum_{i>=n} 3^-i <= kappa(n)"

    tailVariableRecorded :
      BridgeVariable

    tailVariableIsN :
      tailVariableRecorded ≡ tailStartN

    tailBoundAuthorityRequired :
      Bool

    tailBoundAuthorityRequiredIsTrue :
      tailBoundAuthorityRequired ≡ true

    tailBoundProvedHere :
      Bool

    tailBoundProvedHereIsFalse :
      tailBoundProvedHere ≡ false

open TailBoundIntake public

canonicalTailBoundIntake :
  (n : Nat) →
  TailBoundIntake n
canonicalTailBoundIntake n =
  record
    { tailShape =
        ternaryTailFrom n
    ; tailShapeIsFromN =
        refl
    ; boundFormula =
        "sum_{i>=n} 3^-i <= kappa(n)"
    ; boundFormulaIsCanonical =
        refl
    ; tailVariableRecorded =
        tailStartN
    ; tailVariableIsN =
        refl
    ; tailBoundAuthorityRequired =
        true
    ; tailBoundAuthorityRequiredIsTrue =
        refl
    ; tailBoundProvedHere =
        false
    ; tailBoundProvedHereIsFalse =
        refl
    }

------------------------------------------------------------------------
-- Exact checked intake fields.

data IntakeCheckStatus : Set where
  checkedInternal :
    IntakeCheckStatus

  externalAuthorityRequiredFailClosed :
    IntakeCheckStatus

record AgreementGaugeBridgeShapeReference (n : Nat) : Set where
  field
    bridgeShapeName :
      String

    bridgeShapeNameIsAgreementGauge :
      bridgeShapeName
      ≡
      "AgreementSurrealGaugeBridge rational gauge intake shape"

    bridgeFormula :
      String

    bridgeFormulaIsCanonical :
      bridgeFormula ≡ "No/surreal gauge slot: 3^-agreeDepth"

    bridgeShapeRecorded :
      Bool

    bridgeShapeRecordedIsTrue :
      bridgeShapeRecorded ≡ true

    rationalAuthorityAcceptedHere :
      Bool

    rationalAuthorityAcceptedHereIsFalse :
      rationalAuthorityAcceptedHere ≡ false

    bridgePromotionAcceptedHere :
      Bool

    bridgePromotionAcceptedHereIsFalse :
      bridgePromotionAcceptedHere ≡ false

open AgreementGaugeBridgeShapeReference public

canonicalAgreementGaugeBridgeShapeReference :
  (n : Nat) →
  AgreementGaugeBridgeShapeReference n
canonicalAgreementGaugeBridgeShapeReference n =
  record
    { bridgeShapeName =
        "AgreementSurrealGaugeBridge rational gauge intake shape"
    ; bridgeShapeNameIsAgreementGauge =
        refl
    ; bridgeFormula =
        "No/surreal gauge slot: 3^-agreeDepth"
    ; bridgeFormulaIsCanonical =
        refl
    ; bridgeShapeRecorded =
        true
    ; bridgeShapeRecordedIsTrue =
        refl
    ; rationalAuthorityAcceptedHere =
        false
    ; rationalAuthorityAcceptedHereIsFalse =
        refl
    ; bridgePromotionAcceptedHere =
        false
    ; bridgePromotionAcceptedHereIsFalse =
        refl
    }

record OrderedQQBridgeReferenceRows (n : Nat) : Set where
  field
    referenceMode :
      String

    referenceModeIsCanonicalStringsOnly :
      referenceMode
      ≡
      "ordered QQ bridge references are canonical strings/records only; no bridge import"

    orderedQQBridgeModuleRequest :
      String

    orderedQQBridgeModuleRequestIsCanonical :
      orderedQQBridgeModuleRequest
      ≡
      "DASHI.Foundations.SurrealCompactificationOrderedQQBridge if available"

    tritToQQRow :
      String

    tritToQQRowIsExact :
      tritToQQRow ≡ "tritToQQ : Trit -> QQ"

    qqThirdRow :
      String

    qqThirdRowIsExact :
      qqThirdRow ≡ "qqThird : QQ"

    threeMinusN-zeroRow :
      String

    threeMinusN-zeroRowIsExact :
      threeMinusN-zeroRow ≡ "threeMinusN-zero : threeMinusN zero == 1"

    threeMinusN-sucRow :
      String

    threeMinusN-sucRowIsExact :
      threeMinusN-sucRow
      ≡
      "threeMinusN-suc : threeMinusN (suc n) == qqThird * threeMinusN n"

    embeddingIntervalRequestRow :
      String

    embeddingIntervalRequestRowIsExact :
      embeddingIntervalRequestRow
      ≡
      "embedding interval request: finite balanced ternary QQ image lies in closed interval [-1/2, 1/2]"

    orderedQQPromotionAcceptedHere :
      Bool

    orderedQQPromotionAcceptedHereIsFalse :
      orderedQQPromotionAcceptedHere ≡ false

open OrderedQQBridgeReferenceRows public

canonicalOrderedQQBridgeReferenceRows :
  (n : Nat) →
  OrderedQQBridgeReferenceRows n
canonicalOrderedQQBridgeReferenceRows n =
  record
    { referenceMode =
        "ordered QQ bridge references are canonical strings/records only; no bridge import"
    ; referenceModeIsCanonicalStringsOnly =
        refl
    ; orderedQQBridgeModuleRequest =
        "DASHI.Foundations.SurrealCompactificationOrderedQQBridge if available"
    ; orderedQQBridgeModuleRequestIsCanonical =
        refl
    ; tritToQQRow =
        "tritToQQ : Trit -> QQ"
    ; tritToQQRowIsExact =
        refl
    ; qqThirdRow =
        "qqThird : QQ"
    ; qqThirdRowIsExact =
        refl
    ; threeMinusN-zeroRow =
        "threeMinusN-zero : threeMinusN zero == 1"
    ; threeMinusN-zeroRowIsExact =
        refl
    ; threeMinusN-sucRow =
        "threeMinusN-suc : threeMinusN (suc n) == qqThird * threeMinusN n"
    ; threeMinusN-sucRowIsExact =
        refl
    ; embeddingIntervalRequestRow =
        "embedding interval request: finite balanced ternary QQ image lies in closed interval [-1/2, 1/2]"
    ; embeddingIntervalRequestRowIsExact =
        refl
    ; orderedQQPromotionAcceptedHere =
        false
    ; orderedQQPromotionAcceptedHereIsFalse =
        refl
    }

record ExactCheckedRationalBridgeFields
  (m n k : Nat) :
  Set₁ where
  field
    qqCarrier :
      Set

    qqCarrierIsDataRational :
      qqCarrier ≡ ℚ

    qqCarrierGate :
      CarrierAuthorityGate

    qqCarrierGateIsCanonical :
      qqCarrierGate ≡ qqCarrierAuthorityGate

    qqCarrierConstructedHere :
      Bool

    qqCarrierConstructedHereIsFalse :
      qqCarrierConstructedHere ≡ false

    qqCarrierPromotedHere :
      Bool

    qqCarrierPromotedHereIsFalse :
      qqCarrierPromotedHere ≡ false

    tritDigitMap :
      Trit →
      BalancedTernaryDigit

    tritDigitMapIsCanonical :
      tritDigitMap ≡ balancedTernaryEmbedDigit

    tritNegDigitChecked :
      tritDigitMap neg ≡ minusOneDigit

    tritZeroDigitChecked :
      tritDigitMap zer ≡ zeroDigit

    tritPosDigitChecked :
      tritDigitMap pos ≡ plusOneDigit

    threeMinusN :
      SymbolicGauge

    threeMinusNIsCanonical :
      threeMinusN ≡ threeToMinus n

    threeMinusNRationalValueConstructedHere :
      Bool

    threeMinusNRationalValueConstructedHereIsFalse :
      threeMinusNRationalValueConstructedHere ≡ false

    embedTowerMap :
      {depth : Nat} →
      SC.FiniteTritTower depth →
      SC.Vec BalancedTernaryDigit depth

    embedTowerMapIsCanonical :
      {depth : Nat} →
      (tower : SC.FiniteTritTower depth) →
      embedTowerMap tower ≡ embedTower tower

    embedEmptyTowerChecked :
      embedTowerMap SC.emptyTower ≡ SC.[]

    embedExtendTowerChecked :
      {depth : Nat} →
      (tower : SC.FiniteTritTower depth) →
      (trit : Trit) →
      embedTowerMap (SC.extendTower tower trit)
      ≡
      SC._∷_ (tritDigitMap trit) (embedTowerMap tower)

    antitoneIntakeChecked :
      AntitoneGaugeLemmaIntake m n

    antitoneIntakeCheckedIsCanonical :
      antitoneIntakeChecked ≡ canonicalAntitoneGaugeLemmaIntake m n

    antitoneStatus :
      IntakeCheckStatus

    antitoneStatusIsFailClosed :
      antitoneStatus ≡ externalAuthorityRequiredFailClosed

    kappaChecked :
      KappaShape

    kappaCheckedIsAtK :
      kappaChecked ≡ kappaOfDepth k

    kappaStatus :
      IntakeCheckStatus

    kappaStatusIsFailClosed :
      kappaStatus ≡ externalAuthorityRequiredFailClosed

    tailBoundStatus :
      IntakeCheckStatus

    tailBoundStatusIsFailClosed :
      tailBoundStatus ≡ externalAuthorityRequiredFailClosed

    tailBoundIntakeChecked :
      TailBoundIntake n

    tailBoundIntakeCheckedIsCanonical :
      tailBoundIntakeChecked ≡ canonicalTailBoundIntake n

    rationalBridgeShapeReference :
      AgreementGaugeBridgeShapeReference n

    rationalBridgeShapeReferenceIsCanonical :
      rationalBridgeShapeReference
      ≡
      canonicalAgreementGaugeBridgeShapeReference n

    orderedQQBridgeReferenceRows :
      OrderedQQBridgeReferenceRows n

    orderedQQBridgeReferenceRowsAreCanonical :
      orderedQQBridgeReferenceRows
      ≡
      canonicalOrderedQQBridgeReferenceRows n

open ExactCheckedRationalBridgeFields public

canonicalExactCheckedRationalBridgeFields :
  (m n k : Nat) →
  ExactCheckedRationalBridgeFields m n k
canonicalExactCheckedRationalBridgeFields m n k =
  record
    { qqCarrier =
        ℚ
    ; qqCarrierIsDataRational =
        refl
    ; qqCarrierGate =
        qqCarrierAuthorityGate
    ; qqCarrierGateIsCanonical =
        refl
    ; qqCarrierConstructedHere =
        false
    ; qqCarrierConstructedHereIsFalse =
        refl
    ; qqCarrierPromotedHere =
        false
    ; qqCarrierPromotedHereIsFalse =
        refl
    ; tritDigitMap =
        balancedTernaryEmbedDigit
    ; tritDigitMapIsCanonical =
        refl
    ; tritNegDigitChecked =
        refl
    ; tritZeroDigitChecked =
        refl
    ; tritPosDigitChecked =
        refl
    ; threeMinusN =
        threeToMinus n
    ; threeMinusNIsCanonical =
        refl
    ; threeMinusNRationalValueConstructedHere =
        false
    ; threeMinusNRationalValueConstructedHereIsFalse =
        refl
    ; embedTowerMap =
        embedTower
    ; embedTowerMapIsCanonical =
        λ tower → refl
    ; embedEmptyTowerChecked =
        refl
    ; embedExtendTowerChecked =
        λ tower trit → refl
    ; antitoneIntakeChecked =
        canonicalAntitoneGaugeLemmaIntake m n
    ; antitoneIntakeCheckedIsCanonical =
        refl
    ; antitoneStatus =
        externalAuthorityRequiredFailClosed
    ; antitoneStatusIsFailClosed =
        refl
    ; kappaChecked =
        kappaOfDepth k
    ; kappaCheckedIsAtK =
        refl
    ; kappaStatus =
        externalAuthorityRequiredFailClosed
    ; kappaStatusIsFailClosed =
        refl
    ; tailBoundStatus =
        externalAuthorityRequiredFailClosed
    ; tailBoundStatusIsFailClosed =
        refl
    ; tailBoundIntakeChecked =
        canonicalTailBoundIntake n
    ; tailBoundIntakeCheckedIsCanonical =
        refl
    ; rationalBridgeShapeReference =
        canonicalAgreementGaugeBridgeShapeReference n
    ; rationalBridgeShapeReferenceIsCanonical =
        refl
    ; orderedQQBridgeReferenceRows =
        canonicalOrderedQQBridgeReferenceRows n
    ; orderedQQBridgeReferenceRowsAreCanonical =
        refl
    }

------------------------------------------------------------------------
-- External gates and top-level intake.

data ExternalAuthorityGate : Set where
  noCarrierAuthority :
    ExternalAuthorityGate

  qqCarrierAuthority :
    ExternalAuthorityGate

  qqOrderAuthority :
    ExternalAuthorityGate

  balancedTernaryToQQEmbeddingAuthority :
    ExternalAuthorityGate

  threeMinusNGaugeAuthority :
    ExternalAuthorityGate

  antitoneGaugeLemmaAuthority :
    ExternalAuthorityGate

  truncationKappaAuthority :
    ExternalAuthorityGate

  tailBoundAuthority :
    ExternalAuthorityGate

canonicalExternalAuthorityGates : List ExternalAuthorityGate
canonicalExternalAuthorityGates =
  noCarrierAuthority
  ∷ qqCarrierAuthority
  ∷ qqOrderAuthority
  ∷ balancedTernaryToQQEmbeddingAuthority
  ∷ threeMinusNGaugeAuthority
  ∷ antitoneGaugeLemmaAuthority
  ∷ truncationKappaAuthority
  ∷ tailBoundAuthority
  ∷ []

record ExternalAuthorityGateIntake : Set where
  field
    gates :
      List ExternalAuthorityGate

    gatesAreCanonical :
      gates ≡ canonicalExternalAuthorityGates

    allGatesExternal :
      Bool

    allGatesExternalIsTrue :
      allGatesExternal ≡ true

    anyGateAcceptedHere :
      Bool

    anyGateAcceptedHereIsFalse :
      anyGateAcceptedHere ≡ false

open ExternalAuthorityGateIntake public

canonicalExternalAuthorityGateIntake :
  ExternalAuthorityGateIntake
canonicalExternalAuthorityGateIntake =
  record
    { gates =
        canonicalExternalAuthorityGates
    ; gatesAreCanonical =
        refl
    ; allGatesExternal =
        true
    ; allGatesExternalIsTrue =
        refl
    ; anyGateAcceptedHere =
        false
    ; anyGateAcceptedHereIsFalse =
        refl
    }

record NoPromotionFlags : Set where
  field
    noToQQPromoted :
      Bool

    noToQQPromotedIsFalse :
      noToQQPromoted ≡ false

    qqToNoPromoted :
      Bool

    qqToNoPromotedIsFalse :
      qqToNoPromoted ≡ false

    compactificationPromoted :
      Bool

    compactificationPromotedIsFalse :
      compactificationPromoted ≡ false

    analyticTailBoundPromoted :
      Bool

    analyticTailBoundPromotedIsFalse :
      analyticTailBoundPromoted ≡ false

open NoPromotionFlags public

canonicalNoPromotionFlags : NoPromotionFlags
canonicalNoPromotionFlags =
  record
    { noToQQPromoted =
        false
    ; noToQQPromotedIsFalse =
        refl
    ; qqToNoPromoted =
        false
    ; qqToNoPromotedIsFalse =
        refl
    ; compactificationPromoted =
        false
    ; compactificationPromotedIsFalse =
        refl
    ; analyticTailBoundPromoted =
        false
    ; analyticTailBoundPromotedIsFalse =
        refl
    }

record SurrealCompactificationIntakeContract : Set₁ where
  field
    carrierIntake :
      NoQQCarrierBridgeIntake

    carrierIntakeIsCanonical :
      carrierIntake ≡ canonicalNoQQCarrierBridgeIntake

    balancedTernaryEmbeddingIntake :
      BalancedTernaryEmbeddingIntake

    balancedTernaryEmbeddingIntakeIsCanonical :
      balancedTernaryEmbeddingIntake
      ≡
      canonicalBalancedTernaryEmbeddingIntake

    gaugeIntake :
      (n : Nat) →
      SymbolicThreeMinusNGaugeIntake n

    gaugeIntakeIsCanonical :
      gaugeIntake ≡ canonicalSymbolicThreeMinusNGaugeIntake

    antitoneIntake :
      (m n : Nat) →
      AntitoneGaugeLemmaIntake m n

    antitoneIntakeIsCanonical :
      antitoneIntake ≡ canonicalAntitoneGaugeLemmaIntake

    truncationKappaIntake :
      (k : Nat) →
      TruncationKappaIntake k

    truncationKappaIntakeIsCanonical :
      truncationKappaIntake ≡ canonicalTruncationKappaIntake

    tailBoundIntake :
      (n : Nat) →
      TailBoundIntake n

    tailBoundIntakeIsCanonical :
      tailBoundIntake ≡ canonicalTailBoundIntake

    exactCheckedRationalBridgeFields :
      (m n k : Nat) →
      ExactCheckedRationalBridgeFields m n k

    exactCheckedRationalBridgeFieldsAreCanonical :
      exactCheckedRationalBridgeFields
      ≡
      canonicalExactCheckedRationalBridgeFields

    externalAuthorityGateIntake :
      ExternalAuthorityGateIntake

    externalAuthorityGateIntakeIsCanonical :
      externalAuthorityGateIntake ≡ canonicalExternalAuthorityGateIntake

    promotionFlags :
      NoPromotionFlags

    promotionFlagsAreCanonical :
      promotionFlags ≡ canonicalNoPromotionFlags

open SurrealCompactificationIntakeContract public

canonicalSurrealCompactificationIntakeContract :
  SurrealCompactificationIntakeContract
canonicalSurrealCompactificationIntakeContract =
  record
    { carrierIntake =
        canonicalNoQQCarrierBridgeIntake
    ; carrierIntakeIsCanonical =
        refl
    ; balancedTernaryEmbeddingIntake =
        canonicalBalancedTernaryEmbeddingIntake
    ; balancedTernaryEmbeddingIntakeIsCanonical =
        refl
    ; gaugeIntake =
        canonicalSymbolicThreeMinusNGaugeIntake
    ; gaugeIntakeIsCanonical =
        refl
    ; antitoneIntake =
        canonicalAntitoneGaugeLemmaIntake
    ; antitoneIntakeIsCanonical =
        refl
    ; truncationKappaIntake =
        canonicalTruncationKappaIntake
    ; truncationKappaIntakeIsCanonical =
        refl
    ; tailBoundIntake =
        canonicalTailBoundIntake
    ; tailBoundIntakeIsCanonical =
        refl
    ; exactCheckedRationalBridgeFields =
        canonicalExactCheckedRationalBridgeFields
    ; exactCheckedRationalBridgeFieldsAreCanonical =
        refl
    ; externalAuthorityGateIntake =
        canonicalExternalAuthorityGateIntake
    ; externalAuthorityGateIntakeIsCanonical =
        refl
    ; promotionFlags =
        canonicalNoPromotionFlags
    ; promotionFlagsAreCanonical =
        refl
    }

data NoCarrierAuthorityArtifact : Set where

data QQCarrierAuthorityArtifact : Set where

data RationalOrderAuthorityArtifact : Set where

noCarrierAuthorityNotAcceptedHere :
  NoCarrierAuthorityArtifact →
  Empty
noCarrierAuthorityNotAcceptedHere ()

qqCarrierAuthorityNotAcceptedHere :
  QQCarrierAuthorityArtifact →
  Empty
qqCarrierAuthorityNotAcceptedHere ()

rationalOrderAuthorityNotAcceptedHere :
  RationalOrderAuthorityArtifact →
  Empty
rationalOrderAuthorityNotAcceptedHere ()
