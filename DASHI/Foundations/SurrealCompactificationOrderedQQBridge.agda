module DASHI.Foundations.SurrealCompactificationOrderedQQBridge where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)

import DASHI.Foundations.SurrealCompactification as SC
import DASHI.Foundations.SurrealCompactificationIntake as Intake
import DASHI.Foundations.SurrealCompactificationRationalBridge as RB
import DASHI.Foundations.CarrierPromotionBoundaryCore as CarrierCore

------------------------------------------------------------------------
-- Symbolic ordered-QQ carrier.
--
-- This file intentionally does not import Data.Rational.  It records the
-- ordered QQ carrier shape requested by the bridge while keeping every
-- concrete QQ/No/order promotion fail-closed.

data QQCarrierShape : Set where
  symbolicOrderedQQCarrier :
    QQCarrierShape

data SymbolicOrderedQQTerm : Set where
  qq-zero-term :
    SymbolicOrderedQQTerm

  qq-one-term :
    SymbolicOrderedQQTerm

  qq-third-term :
    SymbolicOrderedQQTerm

  qq-from-rational-approximation :
    RB.SymbolicRationalApproximation →
    SymbolicOrderedQQTerm

  qq-add-term :
    SymbolicOrderedQQTerm →
    SymbolicOrderedQQTerm →
    SymbolicOrderedQQTerm

  qq-mul-term :
    SymbolicOrderedQQTerm →
    SymbolicOrderedQQTerm →
    SymbolicOrderedQQTerm

  qq-neg-term :
    SymbolicOrderedQQTerm →
    SymbolicOrderedQQTerm

  qq-inv-term :
    SymbolicOrderedQQTerm →
    SymbolicOrderedQQTerm

qq-zero :
  SymbolicOrderedQQTerm
qq-zero =
  qq-zero-term

qq-one :
  SymbolicOrderedQQTerm
qq-one =
  qq-one-term

qq-third :
  SymbolicOrderedQQTerm
qq-third =
  qq-third-term

_qq+_ :
  SymbolicOrderedQQTerm →
  SymbolicOrderedQQTerm →
  SymbolicOrderedQQTerm
_qq+_ =
  qq-add-term

_qq*_ :
  SymbolicOrderedQQTerm →
  SymbolicOrderedQQTerm →
  SymbolicOrderedQQTerm
_qq*_ =
  qq-mul-term

qq-neg :
  SymbolicOrderedQQTerm →
  SymbolicOrderedQQTerm
qq-neg =
  qq-neg-term

qq-inv :
  SymbolicOrderedQQTerm →
  SymbolicOrderedQQTerm
qq-inv =
  qq-inv-term

data SymbolicQQOrderReceipt :
  SymbolicOrderedQQTerm →
  SymbolicOrderedQQTerm →
  Set where

  symbolicQQOrderReceipt :
    (left right : SymbolicOrderedQQTerm) →
    SymbolicQQOrderReceipt left right

_qq≤_ :
  SymbolicOrderedQQTerm →
  SymbolicOrderedQQTerm →
  Set
_qq≤_ =
  SymbolicQQOrderReceipt

qq-order :
  SymbolicOrderedQQTerm →
  SymbolicOrderedQQTerm →
  Set
qq-order =
  _qq≤_

------------------------------------------------------------------------
-- Antitone dependency shape.

record OrderedQQAntitoneDependency (m n : Nat) : Set where
  field
    intakeAntitone :
      Intake.AntitoneGaugeLemmaIntake m n

    intakeAntitoneIsCanonical :
      intakeAntitone ≡ Intake.canonicalAntitoneGaugeLemmaIntake m n

    premiseShape :
      String

    premiseShapeIsNatOrder :
      premiseShape ≡ "m <= n"

    conclusionShape :
      String

    conclusionShapeIsOrderedQQ :
      conclusionShape ≡ "3^-n <= 3^-m in QQ"

    dependencyVariables :
      List Intake.BridgeVariable

    dependencyVariablesAreMN :
      dependencyVariables ≡ Intake.depthM ∷ Intake.depthN ∷ []

    dependsOnNatOrder :
      Bool

    dependsOnNatOrderIsTrue :
      dependsOnNatOrder ≡ true

    dependsOnQQOrder :
      Bool

    dependsOnQQOrderIsTrue :
      dependsOnQQOrder ≡ true

    rationalOrderAuthorityRequired :
      Bool

    rationalOrderAuthorityRequiredIsTrue :
      rationalOrderAuthorityRequired ≡ true

    antitoneLemmaPromotedHere :
      Bool

    antitoneLemmaPromotedHereIsFalse :
      antitoneLemmaPromotedHere ≡ false

open OrderedQQAntitoneDependency public

canonicalOrderedQQAntitoneDependency :
  (m n : Nat) →
  OrderedQQAntitoneDependency m n
canonicalOrderedQQAntitoneDependency m n =
  record
    { intakeAntitone =
        Intake.canonicalAntitoneGaugeLemmaIntake m n
    ; intakeAntitoneIsCanonical =
        refl
    ; premiseShape =
        "m <= n"
    ; premiseShapeIsNatOrder =
        refl
    ; conclusionShape =
        "3^-n <= 3^-m in QQ"
    ; conclusionShapeIsOrderedQQ =
        refl
    ; dependencyVariables =
        Intake.depthM ∷ Intake.depthN ∷ []
    ; dependencyVariablesAreMN =
        refl
    ; dependsOnNatOrder =
        true
    ; dependsOnNatOrderIsTrue =
        refl
    ; dependsOnQQOrder =
        true
    ; dependsOnQQOrderIsTrue =
        refl
    ; rationalOrderAuthorityRequired =
        true
    ; rationalOrderAuthorityRequiredIsTrue =
        refl
    ; antitoneLemmaPromotedHere =
        false
    ; antitoneLemmaPromotedHereIsFalse =
        refl
    }

------------------------------------------------------------------------
-- Non-promotion receipts.

record OrderedQQNonPromotionReceipts : Set where
  field
    orderedQQCarrierPromotionCore :
      CarrierCore.CarrierPromotionReceipt

    orderedQQCarrierPromotionCoreIsCanonical :
      orderedQQCarrierPromotionCore
      ≡
      CarrierCore.canonicalOrderedQQCarrierPromotionReceipt

    orderedQQCarrierPromotionCoreFalse :
      CarrierCore.orderedQQCarrierPromoted
        (CarrierCore.boundary orderedQQCarrierPromotionCore)
      ≡
      false

    noQQCarrierBridgeIntake :
      Intake.NoQQCarrierBridgeIntake

    noQQCarrierBridgeIntakeIsCanonical :
      noQQCarrierBridgeIntake ≡ Intake.canonicalNoQQCarrierBridgeIntake

    noPromotionFlags :
      Intake.NoPromotionFlags

    noPromotionFlagsAreCanonical :
      noPromotionFlags ≡ Intake.canonicalNoPromotionFlags

    concreteQQCarrierPromoted :
      Bool

    concreteQQCarrierPromotedIsFalse :
      concreteQQCarrierPromoted ≡ false

    concreteNoCarrierPromoted :
      Bool

    concreteNoCarrierPromotedIsFalse :
      concreteNoCarrierPromoted ≡ false

    concreteQQArithmeticPromoted :
      Bool

    concreteQQArithmeticPromotedIsFalse :
      concreteQQArithmeticPromoted ≡ false

    concreteQQOrderPromoted :
      Bool

    concreteQQOrderPromotedIsFalse :
      concreteQQOrderPromoted ≡ false

    qqCarrierAuthorityNotAccepted :
      Intake.QQCarrierAuthorityArtifact →
      Intake.Empty

    rationalOrderAuthorityNotAccepted :
      Intake.RationalOrderAuthorityArtifact →
      Intake.Empty

open OrderedQQNonPromotionReceipts public

canonicalOrderedQQNonPromotionReceipts :
  OrderedQQNonPromotionReceipts
canonicalOrderedQQNonPromotionReceipts =
  record
    { orderedQQCarrierPromotionCore =
        CarrierCore.canonicalOrderedQQCarrierPromotionReceipt
    ; orderedQQCarrierPromotionCoreIsCanonical =
        refl
    ; orderedQQCarrierPromotionCoreFalse =
        refl
    ; noQQCarrierBridgeIntake =
        Intake.canonicalNoQQCarrierBridgeIntake
    ; noQQCarrierBridgeIntakeIsCanonical =
        refl
    ; noPromotionFlags =
        Intake.canonicalNoPromotionFlags
    ; noPromotionFlagsAreCanonical =
        refl
    ; concreteQQCarrierPromoted =
        false
    ; concreteQQCarrierPromotedIsFalse =
        refl
    ; concreteNoCarrierPromoted =
        false
    ; concreteNoCarrierPromotedIsFalse =
        refl
    ; concreteQQArithmeticPromoted =
        false
    ; concreteQQArithmeticPromotedIsFalse =
        refl
    ; concreteQQOrderPromoted =
        false
    ; concreteQQOrderPromotedIsFalse =
        refl
    ; qqCarrierAuthorityNotAccepted =
        Intake.qqCarrierAuthorityNotAcceptedHere
    ; rationalOrderAuthorityNotAccepted =
        Intake.rationalOrderAuthorityNotAcceptedHere
    }

------------------------------------------------------------------------
-- Ordered bridge surface consuming the rational bridge.

record OrderedQQBridgeSurface : Set₁ where
  field
    rationalBridge :
      RB.FiniteTritTowerSymbolicRationalBridge

    rationalBridgeIsCanonical :
      rationalBridge ≡ RB.canonicalFiniteTritTowerSymbolicRationalBridge

    QQCarrier :
      Set

    QQCarrierIsSymbolicOrderedQQTerm :
      QQCarrier ≡ SymbolicOrderedQQTerm

    QQCarrierShapeRecorded :
      QQCarrierShape

    QQCarrierShapeIsSymbolicOrdered :
      QQCarrierShapeRecorded ≡ symbolicOrderedQQCarrier

    QQCarrierShapeDescription :
      String

    QQCarrierShapeDescriptionIsRequestedSurface :
      QQCarrierShapeDescription
      ≡
      "QQCarrier = symbolic ordered term carrier over SurrealCompactificationRationalBridge.SymbolicRationalApproximation"

    rationalApproximationEmbedding :
      RB.SymbolicRationalApproximation →
      SymbolicOrderedQQTerm

    rationalApproximationEmbeddingIsInternal :
      rationalApproximationEmbedding ≡ qq-from-rational-approximation

    qq-zero-field :
      SymbolicOrderedQQTerm

    qq-zero-field-is-qq-zero :
      qq-zero-field ≡ qq-zero

    qq-one-field :
      SymbolicOrderedQQTerm

    qq-one-field-is-qq-one :
      qq-one-field ≡ qq-one

    qq-third-field :
      SymbolicOrderedQQTerm

    qq-third-field-is-qq-third :
      qq-third-field ≡ qq-third

    qq-add :
      SymbolicOrderedQQTerm →
      SymbolicOrderedQQTerm →
      SymbolicOrderedQQTerm

    qq-add-is-symbolic :
      qq-add ≡ _qq+_

    qq-mul :
      SymbolicOrderedQQTerm →
      SymbolicOrderedQQTerm →
      SymbolicOrderedQQTerm

    qq-mul-is-symbolic :
      qq-mul ≡ _qq*_

    qq-neg-field :
      SymbolicOrderedQQTerm →
      SymbolicOrderedQQTerm

    qq-neg-field-is-symbolic :
      qq-neg-field ≡ qq-neg

    qq-inv-field :
      SymbolicOrderedQQTerm →
      SymbolicOrderedQQTerm

    qq-inv-field-is-symbolic :
      qq-inv-field ≡ qq-inv

    qq-order-field :
      SymbolicOrderedQQTerm →
      SymbolicOrderedQQTerm →
      Set

    qq-order-field-is-symbolic :
      qq-order-field ≡ qq-order

    antitoneDependency :
      (m n : Nat) →
      OrderedQQAntitoneDependency m n

    antitoneDependencyIsCanonical :
      (m n : Nat) →
      antitoneDependency m n ≡ canonicalOrderedQQAntitoneDependency m n

    nonPromotionReceipts :
      OrderedQQNonPromotionReceipts

    nonPromotionReceiptsAreCanonical :
      nonPromotionReceipts ≡ canonicalOrderedQQNonPromotionReceipts

open OrderedQQBridgeSurface public

canonicalOrderedQQBridgeSurface :
  OrderedQQBridgeSurface
canonicalOrderedQQBridgeSurface =
  record
    { rationalBridge =
        RB.canonicalFiniteTritTowerSymbolicRationalBridge
    ; rationalBridgeIsCanonical =
        refl
    ; QQCarrier =
        SymbolicOrderedQQTerm
    ; QQCarrierIsSymbolicOrderedQQTerm =
        refl
    ; QQCarrierShapeRecorded =
        symbolicOrderedQQCarrier
    ; QQCarrierShapeIsSymbolicOrdered =
        refl
    ; QQCarrierShapeDescription =
        "QQCarrier = symbolic ordered term carrier over SurrealCompactificationRationalBridge.SymbolicRationalApproximation"
    ; QQCarrierShapeDescriptionIsRequestedSurface =
        refl
    ; rationalApproximationEmbedding =
        qq-from-rational-approximation
    ; rationalApproximationEmbeddingIsInternal =
        refl
    ; qq-zero-field =
        qq-zero
    ; qq-zero-field-is-qq-zero =
        refl
    ; qq-one-field =
        qq-one
    ; qq-one-field-is-qq-one =
        refl
    ; qq-third-field =
        qq-third
    ; qq-third-field-is-qq-third =
        refl
    ; qq-add =
        _qq+_
    ; qq-add-is-symbolic =
        refl
    ; qq-mul =
        _qq*_
    ; qq-mul-is-symbolic =
        refl
    ; qq-neg-field =
        qq-neg
    ; qq-neg-field-is-symbolic =
        refl
    ; qq-inv-field =
        qq-inv
    ; qq-inv-field-is-symbolic =
        refl
    ; qq-order-field =
        qq-order
    ; qq-order-field-is-symbolic =
        refl
    ; antitoneDependency =
        canonicalOrderedQQAntitoneDependency
    ; antitoneDependencyIsCanonical =
        λ m n → refl
    ; nonPromotionReceipts =
        canonicalOrderedQQNonPromotionReceipts
    ; nonPromotionReceiptsAreCanonical =
        refl
    }

orderedBridgeTowerTerm :
  {depth : Nat} →
  SC.FiniteTritTower depth →
  SymbolicOrderedQQTerm
orderedBridgeTowerTerm tower =
  qq-from-rational-approximation
    (RB.bridgeFiniteTower
      (rationalBridge canonicalOrderedQQBridgeSurface)
      tower)

orderedBridgeTowerTermIsRationalBridgeEmbedding :
  {depth : Nat} →
  (tower : SC.FiniteTritTower depth) →
  orderedBridgeTowerTerm tower
  ≡
  qq-from-rational-approximation (RB.towerToSymbolicRational tower)
orderedBridgeTowerTermIsRationalBridgeEmbedding tower =
  refl

canonicalOrderedBridgeConcreteQQCarrierNotPromoted :
  concreteQQCarrierPromoted
    (nonPromotionReceipts canonicalOrderedQQBridgeSurface)
  ≡
  false
canonicalOrderedBridgeConcreteQQCarrierNotPromoted =
  refl

canonicalOrderedBridgeConcreteNoCarrierNotPromoted :
  concreteNoCarrierPromoted
    (nonPromotionReceipts canonicalOrderedQQBridgeSurface)
  ≡
  false
canonicalOrderedBridgeConcreteNoCarrierNotPromoted =
  refl

canonicalOrderedBridgeConcreteQQArithmeticNotPromoted :
  concreteQQArithmeticPromoted
    (nonPromotionReceipts canonicalOrderedQQBridgeSurface)
  ≡
  false
canonicalOrderedBridgeConcreteQQArithmeticNotPromoted =
  refl

canonicalOrderedBridgeConcreteQQOrderNotPromoted :
  concreteQQOrderPromoted
    (nonPromotionReceipts canonicalOrderedQQBridgeSurface)
  ≡
  false
canonicalOrderedBridgeConcreteQQOrderNotPromoted =
  refl

canonicalOrderedBridgeAntitoneDoesNotPromoteLemma :
  (m n : Nat) →
  antitoneLemmaPromotedHere
    (antitoneDependency canonicalOrderedQQBridgeSurface m n)
  ≡
  false
canonicalOrderedBridgeAntitoneDoesNotPromoteLemma m n =
  refl
