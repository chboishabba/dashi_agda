module DASHI.Foundations.SurrealCompactificationBalancedTernaryEmbedding where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat; zero; suc)

open import DASHI.Algebra.Trit using (Trit; neg; zer; pos)
import DASHI.Foundations.SurrealCompactification as SC
import DASHI.Foundations.SurrealCompactificationIntake as Intake
import DASHI.Foundations.SurrealCompactificationOrderedQQBridge as OQQ
import DASHI.Foundations.SurrealCompactificationQQCarrier as QQC
import DASHI.Foundations.SurrealCompactificationRationalBridge as RB

QQ : Set
QQ =
  QQC.BoundedQQ

qqMinusOne : QQ
qqMinusOne =
  QQC.qq-neg QQC.oneQQ

trit-to-QQ :
  Trit →
  QQ
trit-to-QQ neg =
  qqMinusOne
trit-to-QQ zer =
  QQC.zeroQQ
trit-to-QQ pos =
  QQC.oneQQ

trit-to-QQ-neg :
  trit-to-QQ neg ≡ qqMinusOne
trit-to-QQ-neg =
  refl

trit-to-QQ-zer :
  trit-to-QQ zer ≡ QQC.zeroQQ
trit-to-QQ-zer =
  refl

trit-to-QQ-pos :
  trit-to-QQ pos ≡ QQC.oneQQ
trit-to-QQ-pos =
  refl

threeMinusN :
  Nat →
  QQ
threeMinusN zero =
  QQC.oneQQ
threeMinusN (suc n) =
  QQC.mulByThird (threeMinusN n)

threeMinusN-zero :
  threeMinusN zero ≡ QQC.oneQQ
threeMinusN-zero =
  refl

threeMinusN-suc :
  (n : Nat) →
  threeMinusN (suc n) ≡ QQC.mulByThird (threeMinusN n)
threeMinusN-suc n =
  refl

threeMinusN-is-carrierGauge :
  (n : Nat) →
  threeMinusN n ≡ QQC.thirdPowerGauge n
threeMinusN-is-carrierGauge zero =
  refl
threeMinusN-is-carrierGauge (suc n) =
  SC.cong QQC.mulByThird (threeMinusN-is-carrierGauge n)

embedTowerDigits :
  {depth : Nat} →
  SC.FiniteTritTower depth →
  SC.Vec QQ depth
embedTowerDigits SC.emptyTower =
  SC.[]
embedTowerDigits (SC.extendTower tower trit) =
  SC._∷_ (trit-to-QQ trit) (embedTowerDigits tower)

embedTowerDigits-empty :
  embedTowerDigits SC.emptyTower ≡ SC.[]
embedTowerDigits-empty =
  refl

embedTowerDigits-extend :
  {depth : Nat} →
  (tower : SC.FiniteTritTower depth) →
  (trit : Trit) →
  embedTowerDigits (SC.extendTower tower trit)
  ≡
  SC._∷_ (trit-to-QQ trit) (embedTowerDigits tower)
embedTowerDigits-extend tower trit =
  refl

embedTower :
  {depth : Nat} →
  SC.FiniteTritTower depth →
  QQ
embedTower SC.emptyTower =
  QQC.zeroQQ
embedTower (SC.extendTower {depth} tower trit) =
  QQC._qq+_
    (embedTower tower)
    (QQC._qq*_ (trit-to-QQ trit) (threeMinusN (suc depth)))

embedTower-empty :
  embedTower SC.emptyTower ≡ QQC.zeroQQ
embedTower-empty =
  refl

embedTower-extend :
  {depth : Nat} →
  (tower : SC.FiniteTritTower depth) →
  (trit : Trit) →
  embedTower (SC.extendTower tower trit)
  ≡
  QQC._qq+_
    (embedTower tower)
    (QQC._qq*_ (trit-to-QQ trit) (threeMinusN (suc depth)))
embedTower-extend tower trit =
  refl

data BoundedEmbeddingProofContent : Set where
  tritCasesChecked :
    BoundedEmbeddingProofContent

  threeMinusNRecursionChecked :
    BoundedEmbeddingProofContent

  carrierGaugeCompatibilityChecked :
    BoundedEmbeddingProofContent

  finiteTowerRecursionChecked :
    BoundedEmbeddingProofContent

  intervalShapeTokenOnly :
    BoundedEmbeddingProofContent

  analyticQQInequalityExternal :
    BoundedEmbeddingProofContent

canonicalBoundedEmbeddingProofContent :
  List BoundedEmbeddingProofContent
canonicalBoundedEmbeddingProofContent =
  tritCasesChecked
  ∷ threeMinusNRecursionChecked
  ∷ carrierGaugeCompatibilityChecked
  ∷ finiteTowerRecursionChecked
  ∷ intervalShapeTokenOnly
  ∷ analyticQQInequalityExternal
  ∷ []

data IntervalEndpointShape : Set where
  minusHalfEndpoint :
    IntervalEndpointShape

  plusHalfEndpoint :
    IntervalEndpointShape

data ClosedBalancedIntervalToken (term : QQ) : Set where
  closedMinusHalfPlusHalfShape :
    ClosedBalancedIntervalToken term

record BalancedTernaryIntervalReceipt
  {depth : Nat}
  (tower : SC.FiniteTritTower depth) :
  Set where
  field
    embeddedTerm :
      QQ

    embeddedTermIsEmbedTower :
      embeddedTerm ≡ embedTower tower

    lowerEndpointShape :
      IntervalEndpointShape

    lowerEndpointShapeIsMinusHalf :
      lowerEndpointShape ≡ minusHalfEndpoint

    upperEndpointShape :
      IntervalEndpointShape

    upperEndpointShapeIsPlusHalf :
      upperEndpointShape ≡ plusHalfEndpoint

    closedIntervalToken :
      ClosedBalancedIntervalToken embeddedTerm

    closedIntervalTokenIsStructural :
      closedIntervalToken ≡ closedMinusHalfPlusHalfShape

    orderedQQEndpointTermLower :
      OQQ.SymbolicOrderedQQTerm

    orderedQQEndpointTermLowerIsMinusHalfShape :
      orderedQQEndpointTermLower
      ≡
      OQQ.qq-neg
        (OQQ.qq-inv (OQQ._qq+_ OQQ.qq-one OQQ.qq-one))

    orderedQQEndpointTermUpper :
      OQQ.SymbolicOrderedQQTerm

    orderedQQEndpointTermUpperIsHalfShape :
      orderedQQEndpointTermUpper
      ≡
      OQQ.qq-inv (OQQ._qq+_ OQQ.qq-one OQQ.qq-one)

    boundedInternalDepth :
      Nat

    boundedInternalDepthIsIndex :
      boundedInternalDepth ≡ depth

    boundedInternalProofContent :
      List BoundedEmbeddingProofContent

    boundedInternalProofContentIsCanonical :
      boundedInternalProofContent ≡ canonicalBoundedEmbeddingProofContent

    symbolicIntervalShapeChecked :
      Bool

    symbolicIntervalShapeCheckedIsTrue :
      symbolicIntervalShapeChecked ≡ true

    analyticLowerInequalityProvedHere :
      Bool

    analyticLowerInequalityProvedHereIsFalse :
      analyticLowerInequalityProvedHere ≡ false

    analyticUpperInequalityProvedHere :
      Bool

    analyticUpperInequalityProvedHereIsFalse :
      analyticUpperInequalityProvedHere ≡ false

    boundedQQCarrierPromotedHere :
      Bool

    boundedQQCarrierPromotedHereIsFalse :
      boundedQQCarrierPromotedHere ≡ false

    surrealLimitPromotedHere :
      Bool

    surrealLimitPromotedHereIsFalse :
      surrealLimitPromotedHere ≡ false

open BalancedTernaryIntervalReceipt public

canonicalBalancedTernaryIntervalReceipt :
  {depth : Nat} →
  (tower : SC.FiniteTritTower depth) →
  BalancedTernaryIntervalReceipt tower
canonicalBalancedTernaryIntervalReceipt {depth} tower =
  record
    { embeddedTerm =
        embedTower tower
    ; embeddedTermIsEmbedTower =
        refl
    ; lowerEndpointShape =
        minusHalfEndpoint
    ; lowerEndpointShapeIsMinusHalf =
        refl
    ; upperEndpointShape =
        plusHalfEndpoint
    ; upperEndpointShapeIsPlusHalf =
        refl
    ; closedIntervalToken =
        closedMinusHalfPlusHalfShape
    ; closedIntervalTokenIsStructural =
        refl
    ; orderedQQEndpointTermLower =
        OQQ.qq-neg
          (OQQ.qq-inv (OQQ._qq+_ OQQ.qq-one OQQ.qq-one))
    ; orderedQQEndpointTermLowerIsMinusHalfShape =
        refl
    ; orderedQQEndpointTermUpper =
        OQQ.qq-inv (OQQ._qq+_ OQQ.qq-one OQQ.qq-one)
    ; orderedQQEndpointTermUpperIsHalfShape =
        refl
    ; boundedInternalDepth =
        depth
    ; boundedInternalDepthIsIndex =
        refl
    ; boundedInternalProofContent =
        canonicalBoundedEmbeddingProofContent
    ; boundedInternalProofContentIsCanonical =
        refl
    ; symbolicIntervalShapeChecked =
        true
    ; symbolicIntervalShapeCheckedIsTrue =
        refl
    ; analyticLowerInequalityProvedHere =
        false
    ; analyticLowerInequalityProvedHereIsFalse =
        refl
    ; analyticUpperInequalityProvedHere =
        false
    ; analyticUpperInequalityProvedHereIsFalse =
        refl
    ; boundedQQCarrierPromotedHere =
        false
    ; boundedQQCarrierPromotedHereIsFalse =
        refl
    ; surrealLimitPromotedHere =
        false
    ; surrealLimitPromotedHereIsFalse =
        refl
    }

record BalancedTernaryEmbeddingShapeReceipt : Set₁ where
  field
    sourceCarrier :
      Nat →
      Set

    sourceCarrierIsSurrealCompactificationTower :
      sourceCarrier ≡ SC.FiniteTritTower

    boundedQQCarrier :
      QQC.QQCarrierSurface

    boundedQQCarrierIsCanonical :
      boundedQQCarrier ≡ QQC.canonicalQQCarrierSurface

    orderedQQBridge :
      OQQ.OrderedQQBridgeSurface

    orderedQQBridgeIsCanonical :
      orderedQQBridge ≡ OQQ.canonicalOrderedQQBridgeSurface

    rationalBridge :
      RB.FiniteTritTowerSymbolicRationalBridge

    rationalBridgeIsCanonical :
      rationalBridge ≡ RB.canonicalFiniteTritTowerSymbolicRationalBridge

    intakeContract :
      Intake.SurrealCompactificationIntakeContract

    intakeContractIsCanonical :
      intakeContract ≡ Intake.canonicalSurrealCompactificationIntakeContract

    targetCarrier :
      Set

    targetCarrierIsBoundedQQ :
      targetCarrier ≡ QQ

    digitMap :
      Trit →
      QQ

    digitMapIsTrit-to-QQ :
      digitMap ≡ trit-to-QQ

    digitMapNegChecked :
      digitMap neg ≡ qqMinusOne

    digitMapZerChecked :
      digitMap zer ≡ QQC.zeroQQ

    digitMapPosChecked :
      digitMap pos ≡ QQC.oneQQ

    threeMinusNMap :
      Nat →
      QQ

    threeMinusNMapZero :
      threeMinusNMap zero ≡ QQC.oneQQ

    threeMinusNMapSuc :
      (n : Nat) →
      threeMinusNMap (suc n) ≡ QQC.mulByThird (threeMinusNMap n)

    threeMinusNMapIsCarrierGauge :
      (n : Nat) →
      threeMinusNMap n ≡ QQC.thirdPowerGauge n

    towerEmbedding :
      {depth : Nat} →
      SC.FiniteTritTower depth →
      QQ

    towerEmbeddingIsEmbedTower :
      {depth : Nat} →
      (tower : SC.FiniteTritTower depth) →
      towerEmbedding tower ≡ embedTower tower

    towerEmbeddingEmptyChecked :
      towerEmbedding SC.emptyTower ≡ QQC.zeroQQ

    towerEmbeddingExtendChecked :
      {depth : Nat} →
      (tower : SC.FiniteTritTower depth) →
      (trit : Trit) →
      towerEmbedding (SC.extendTower tower trit)
      ≡
      QQC._qq+_
        (towerEmbedding tower)
        (QQC._qq*_ (digitMap trit) (threeMinusNMap (suc depth)))

    proofContent :
      List BoundedEmbeddingProofContent

    proofContentIsCanonical :
      proofContent ≡ canonicalBoundedEmbeddingProofContent

    intervalReceiptsAreStructuralOnly :
      Bool

    intervalReceiptsAreStructuralOnlyIsTrue :
      intervalReceiptsAreStructuralOnly ≡ true

    analyticIntervalProofPromotedHere :
      Bool

    analyticIntervalProofPromotedHereIsFalse :
      analyticIntervalProofPromotedHere ≡ false

    externalQQCarrierAuthorityAcceptedHere :
      Bool

    externalQQCarrierAuthorityAcceptedHereIsFalse :
      externalQQCarrierAuthorityAcceptedHere ≡ false

    orderedQQPromotionAcceptedHere :
      Bool

    orderedQQPromotionAcceptedHereIsFalse :
      orderedQQPromotionAcceptedHere ≡ false

    compactificationPromotionAcceptedHere :
      Bool

    compactificationPromotionAcceptedHereIsFalse :
      compactificationPromotionAcceptedHere ≡ false

open BalancedTernaryEmbeddingShapeReceipt public

canonicalBalancedTernaryEmbeddingShapeReceipt :
  BalancedTernaryEmbeddingShapeReceipt
canonicalBalancedTernaryEmbeddingShapeReceipt =
  record
    { sourceCarrier =
        SC.FiniteTritTower
    ; sourceCarrierIsSurrealCompactificationTower =
        refl
    ; boundedQQCarrier =
        QQC.canonicalQQCarrierSurface
    ; boundedQQCarrierIsCanonical =
        refl
    ; orderedQQBridge =
        OQQ.canonicalOrderedQQBridgeSurface
    ; orderedQQBridgeIsCanonical =
        refl
    ; rationalBridge =
        RB.canonicalFiniteTritTowerSymbolicRationalBridge
    ; rationalBridgeIsCanonical =
        refl
    ; intakeContract =
        Intake.canonicalSurrealCompactificationIntakeContract
    ; intakeContractIsCanonical =
        refl
    ; targetCarrier =
        QQ
    ; targetCarrierIsBoundedQQ =
        refl
    ; digitMap =
        trit-to-QQ
    ; digitMapIsTrit-to-QQ =
        refl
    ; digitMapNegChecked =
        refl
    ; digitMapZerChecked =
        refl
    ; digitMapPosChecked =
        refl
    ; threeMinusNMap =
        threeMinusN
    ; threeMinusNMapZero =
        refl
    ; threeMinusNMapSuc =
        λ n → refl
    ; threeMinusNMapIsCarrierGauge =
        threeMinusN-is-carrierGauge
    ; towerEmbedding =
        embedTower
    ; towerEmbeddingIsEmbedTower =
        λ tower → refl
    ; towerEmbeddingEmptyChecked =
        refl
    ; towerEmbeddingExtendChecked =
        λ tower trit → refl
    ; proofContent =
        canonicalBoundedEmbeddingProofContent
    ; proofContentIsCanonical =
        refl
    ; intervalReceiptsAreStructuralOnly =
        true
    ; intervalReceiptsAreStructuralOnlyIsTrue =
        refl
    ; analyticIntervalProofPromotedHere =
        false
    ; analyticIntervalProofPromotedHereIsFalse =
        refl
    ; externalQQCarrierAuthorityAcceptedHere =
        false
    ; externalQQCarrierAuthorityAcceptedHereIsFalse =
        refl
    ; orderedQQPromotionAcceptedHere =
        false
    ; orderedQQPromotionAcceptedHereIsFalse =
        refl
    ; compactificationPromotionAcceptedHere =
        false
    ; compactificationPromotionAcceptedHereIsFalse =
        refl
    }

canonicalShapeUsesBoundedQQCarrier :
  targetCarrier canonicalBalancedTernaryEmbeddingShapeReceipt ≡ QQ
canonicalShapeUsesBoundedQQCarrier =
  refl

canonicalShapeConsumesSurrealCompactification :
  sourceCarrier canonicalBalancedTernaryEmbeddingShapeReceipt
  ≡
  SC.FiniteTritTower
canonicalShapeConsumesSurrealCompactification =
  refl

canonicalShapeIntervalProofIsNotPromoted :
  analyticIntervalProofPromotedHere canonicalBalancedTernaryEmbeddingShapeReceipt
  ≡
  false
canonicalShapeIntervalProofIsNotPromoted =
  refl

canonicalShapeExternalQQAuthorityIsNotAccepted :
  externalQQCarrierAuthorityAcceptedHere canonicalBalancedTernaryEmbeddingShapeReceipt
  ≡
  false
canonicalShapeExternalQQAuthorityIsNotAccepted =
  refl
