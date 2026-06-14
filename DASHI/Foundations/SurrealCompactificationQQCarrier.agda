module DASHI.Foundations.SurrealCompactificationQQCarrier where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Agda.Builtin.String using (String)

import DASHI.Foundations.SurrealCompactification as SC

------------------------------------------------------------------------
-- Builtin-only bounded QQ-like carrier.
--
-- This module intentionally does not import Data.Rational and does not
-- construct an external QQ or No authority.  It is a checked symbolic
-- surface for finite surreal compactification consumers that only need
-- zero/one/third, internal order receipts, and 3^-n gauge antitonicity.

data QQCarrierScope : Set where
  internal-bounded-surreal-compactification :
    QQCarrierScope

data QQAuthorityBoundary : Set where
  no-external-QQ-or-No-authority :
    QQAuthorityBoundary

data BoundedQQ : Set where
  qq-zero-constructor :
    BoundedQQ

  qq-one-constructor :
    BoundedQQ

  qq-third-constructor :
    BoundedQQ

  qq-add-constructor :
    BoundedQQ →
    BoundedQQ →
    BoundedQQ

  qq-neg-constructor :
    BoundedQQ →
    BoundedQQ

  qq-mul-constructor :
    BoundedQQ →
    BoundedQQ →
    BoundedQQ

  qq-mul-third-constructor :
    BoundedQQ →
    BoundedQQ

zeroQQ :
  BoundedQQ
zeroQQ =
  qq-zero-constructor

oneQQ :
  BoundedQQ
oneQQ =
  qq-one-constructor

thirdQQ :
  BoundedQQ
thirdQQ =
  qq-third-constructor

_qq+_ :
  BoundedQQ →
  BoundedQQ →
  BoundedQQ
_qq+_ =
  qq-add-constructor

qq-neg :
  BoundedQQ →
  BoundedQQ
qq-neg =
  qq-neg-constructor

_qq*_ :
  BoundedQQ →
  BoundedQQ →
  BoundedQQ
_qq*_ =
  qq-mul-constructor

mulByThird :
  BoundedQQ →
  BoundedQQ
mulByThird qq-zero-constructor =
  qq-zero-constructor
mulByThird qq-one-constructor =
  qq-third-constructor
mulByThird value =
  qq-mul-third-constructor value

thirdPowerGauge :
  Nat →
  BoundedQQ
thirdPowerGauge zero =
  oneQQ
thirdPowerGauge (suc depth) =
  mulByThird (thirdPowerGauge depth)

gauge-zero-is-one :
  thirdPowerGauge zero ≡ oneQQ
gauge-zero-is-one =
  refl

gauge-one-is-third :
  thirdPowerGauge (suc zero) ≡ thirdQQ
gauge-one-is-third =
  refl

mulByThird-zero :
  mulByThird zeroQQ ≡ zeroQQ
mulByThird-zero =
  refl

mulByThird-one :
  mulByThird oneQQ ≡ thirdQQ
mulByThird-one =
  refl

------------------------------------------------------------------------
-- Internal order evidence and checked receipts.

infix 4 _≤QQ_

data _≤QQ_ : BoundedQQ → BoundedQQ → Set where
  qq≤-refl :
    (value : BoundedQQ) →
    value ≤QQ value

  qq≤-trans :
    {left middle right : BoundedQQ} →
    left ≤QQ middle →
    middle ≤QQ right →
    left ≤QQ right

  qq≤-zero-one :
    zeroQQ ≤QQ oneQQ

  qq≤-zero-third :
    zeroQQ ≤QQ thirdQQ

  qq≤-third-one :
    thirdQQ ≤QQ oneQQ

  qq≤-mulByThird-monotone :
    {left right : BoundedQQ} →
    left ≤QQ right →
    mulByThird left ≤QQ mulByThird right

  qq≤-mulByThird-contracts-nonnegative :
    {value : BoundedQQ} →
    zeroQQ ≤QQ value →
    mulByThird value ≤QQ value

record QQOrderReceipt (left right : BoundedQQ) : Set where
  constructor qq-order-receipt
  field
    orderEvidence :
      left ≤QQ right

    receiptScope :
      QQCarrierScope

    receiptScopeIsInternalBounded :
      receiptScope ≡ internal-bounded-surreal-compactification

    orderReceiptCheckedHere :
      Bool

    orderReceiptCheckedHereIsTrue :
      orderReceiptCheckedHere ≡ true

    externalQQOrderAuthorityAccepted :
      Bool

    externalQQOrderAuthorityAcceptedIsFalse :
      externalQQOrderAuthorityAccepted ≡ false

open QQOrderReceipt public

checkedOrderReceipt :
  {left right : BoundedQQ} →
  left ≤QQ right →
  QQOrderReceipt left right
checkedOrderReceipt evidence =
  qq-order-receipt
    evidence
    internal-bounded-surreal-compactification
    refl
    true
    refl
    false
    refl

qq≤-receipt-refl :
  (value : BoundedQQ) →
  QQOrderReceipt value value
qq≤-receipt-refl value =
  checkedOrderReceipt (qq≤-refl value)

qq≤-receipt-trans :
  {left middle right : BoundedQQ} →
  QQOrderReceipt left middle →
  QQOrderReceipt middle right →
  QQOrderReceipt left right
qq≤-receipt-trans left≤middle middle≤right =
  checkedOrderReceipt
    (qq≤-trans
      (orderEvidence left≤middle)
      (orderEvidence middle≤right))

zero≤one-receipt :
  QQOrderReceipt zeroQQ oneQQ
zero≤one-receipt =
  checkedOrderReceipt qq≤-zero-one

zero≤third-receipt :
  QQOrderReceipt zeroQQ thirdQQ
zero≤third-receipt =
  checkedOrderReceipt qq≤-zero-third

third≤one-receipt :
  QQOrderReceipt thirdQQ oneQQ
third≤one-receipt =
  checkedOrderReceipt qq≤-third-one

mulByThird-monotone-receipt :
  {left right : BoundedQQ} →
  QQOrderReceipt left right →
  QQOrderReceipt (mulByThird left) (mulByThird right)
mulByThird-monotone-receipt left≤right =
  checkedOrderReceipt
    (qq≤-mulByThird-monotone (orderEvidence left≤right))

mulByThird-contracts-nonnegative-receipt :
  {value : BoundedQQ} →
  QQOrderReceipt zeroQQ value →
  QQOrderReceipt (mulByThird value) value
mulByThird-contracts-nonnegative-receipt zero≤value =
  checkedOrderReceipt
    (qq≤-mulByThird-contracts-nonnegative (orderEvidence zero≤value))

------------------------------------------------------------------------
-- Gauge receipts for downstream antitone consumers.

zero≤gauge :
  (depth : Nat) →
  QQOrderReceipt zeroQQ (thirdPowerGauge depth)
zero≤gauge zero =
  zero≤one-receipt
zero≤gauge (suc depth) =
  mulByThird-monotone-receipt (zero≤gauge depth)

gauge-step :
  (depth : Nat) →
  QQOrderReceipt
    (thirdPowerGauge (suc depth))
    (thirdPowerGauge depth)
gauge-step depth =
  mulByThird-contracts-nonnegative-receipt (zero≤gauge depth)

gauge≤one :
  (depth : Nat) →
  QQOrderReceipt (thirdPowerGauge depth) oneQQ
gauge≤one zero =
  qq≤-receipt-refl oneQQ
gauge≤one (suc depth) =
  qq≤-receipt-trans (gauge-step depth) (gauge≤one depth)

gauge-antitone :
  {m n : Nat} →
  m SC.≤ n →
  QQOrderReceipt (thirdPowerGauge n) (thirdPowerGauge m)
gauge-antitone {n = n} SC.z≤n =
  gauge≤one n
gauge-antitone (SC.s≤s m≤n) =
  mulByThird-monotone-receipt (gauge-antitone m≤n)

mulByThird-gauge-step-receipt :
  (depth : Nat) →
  QQOrderReceipt
    (mulByThird (thirdPowerGauge depth))
    (thirdPowerGauge depth)
mulByThird-gauge-step-receipt =
  gauge-step

mulByThird-gauge-monotone-receipt :
  {m n : Nat} →
  m SC.≤ n →
  QQOrderReceipt
    (mulByThird (thirdPowerGauge n))
    (mulByThird (thirdPowerGauge m))
mulByThird-gauge-monotone-receipt m≤n =
  mulByThird-monotone-receipt (gauge-antitone m≤n)

------------------------------------------------------------------------
-- Explicit fail-closed boundary flags.

record QQCarrierFailClosedFlags : Set where
  constructor qq-carrier-fail-closed-flags
  field
    carrierScope :
      QQCarrierScope

    carrierScopeIsInternalBounded :
      carrierScope ≡ internal-bounded-surreal-compactification

    authorityBoundary :
      QQAuthorityBoundary

    authorityBoundaryIsNoExternalQQOrNo :
      authorityBoundary ≡ no-external-QQ-or-No-authority

    builtinOnlySurface :
      Bool

    builtinOnlySurfaceIsTrue :
      builtinOnlySurface ≡ true

    internalBoundedOnly :
      Bool

    internalBoundedOnlyIsTrue :
      internalBoundedOnly ≡ true

    externalQQCarrierAuthorityAccepted :
      Bool

    externalQQCarrierAuthorityAcceptedIsFalse :
      externalQQCarrierAuthorityAccepted ≡ false

    externalNoCarrierAuthorityAccepted :
      Bool

    externalNoCarrierAuthorityAcceptedIsFalse :
      externalNoCarrierAuthorityAccepted ≡ false

    dataRationalImported :
      Bool

    dataRationalImportedIsFalse :
      dataRationalImported ≡ false

    completeQQClaimed :
      Bool

    completeQQClaimedIsFalse :
      completeQQClaimed ≡ false

    completeNoClaimed :
      Bool

    completeNoClaimedIsFalse :
      completeNoClaimed ≡ false

open QQCarrierFailClosedFlags public

canonicalQQCarrierFailClosedFlags :
  QQCarrierFailClosedFlags
canonicalQQCarrierFailClosedFlags =
  qq-carrier-fail-closed-flags
    internal-bounded-surreal-compactification
    refl
    no-external-QQ-or-No-authority
    refl
    true
    refl
    true
    refl
    false
    refl
    false
    refl
    false
    refl
    false
    refl
    false
    refl

record QQCarrierSurface : Set₁ where
  field
    Carrier :
      Set

    CarrierIsBoundedQQ :
      Carrier ≡ BoundedQQ

    qq-zero-field :
      BoundedQQ

    qq-zero-field-is-constructor :
      qq-zero-field ≡ zeroQQ

    qq-one-field :
      BoundedQQ

    qq-one-field-is-constructor :
      qq-one-field ≡ oneQQ

    qq-third-field :
      BoundedQQ

    qq-third-field-is-constructor :
      qq-third-field ≡ thirdQQ

    multiplyByThird :
      BoundedQQ →
      BoundedQQ

    multiplyByThirdIsInternal :
      multiplyByThird ≡ mulByThird

    orderReceipt :
      BoundedQQ →
      BoundedQQ →
      Set

    orderReceiptIsInternal :
      orderReceipt ≡ QQOrderReceipt

    multiplyByThirdMonotone :
      {left right : BoundedQQ} →
      QQOrderReceipt left right →
      QQOrderReceipt (mulByThird left) (mulByThird right)

    multiplyByThirdMonotoneIsCanonical :
      {left right : BoundedQQ} →
      (receipt : QQOrderReceipt left right) →
      multiplyByThirdMonotone receipt
      ≡
      mulByThird-monotone-receipt receipt

    gauge :
      Nat →
      BoundedQQ

    gaugeIsThirdPower :
      gauge ≡ thirdPowerGauge

    gaugeAntitone :
      {m n : Nat} →
      m SC.≤ n →
      QQOrderReceipt (thirdPowerGauge n) (thirdPowerGauge m)

    gaugeAntitoneIsCanonical :
      {m n : Nat} →
      (m≤n : m SC.≤ n) →
      gaugeAntitone m≤n ≡ gauge-antitone m≤n

    failClosedFlags :
      QQCarrierFailClosedFlags

    failClosedFlagsAreCanonical :
      failClosedFlags ≡ canonicalQQCarrierFailClosedFlags

open QQCarrierSurface public

canonicalQQCarrierSurface :
  QQCarrierSurface
canonicalQQCarrierSurface =
  record
    { Carrier =
        BoundedQQ
    ; CarrierIsBoundedQQ =
        refl
    ; qq-zero-field =
        zeroQQ
    ; qq-zero-field-is-constructor =
        refl
    ; qq-one-field =
        oneQQ
    ; qq-one-field-is-constructor =
        refl
    ; qq-third-field =
        thirdQQ
    ; qq-third-field-is-constructor =
        refl
    ; multiplyByThird =
        mulByThird
    ; multiplyByThirdIsInternal =
        refl
    ; orderReceipt =
        QQOrderReceipt
    ; orderReceiptIsInternal =
        refl
    ; multiplyByThirdMonotone =
        mulByThird-monotone-receipt
    ; multiplyByThirdMonotoneIsCanonical =
        λ receipt → refl
    ; gauge =
        thirdPowerGauge
    ; gaugeIsThirdPower =
        refl
    ; gaugeAntitone =
        gauge-antitone
    ; gaugeAntitoneIsCanonical =
        λ m≤n → refl
    ; failClosedFlags =
        canonicalQQCarrierFailClosedFlags
    ; failClosedFlagsAreCanonical =
        refl
    }

surfaceDoesNotAcceptExternalQQ :
  externalQQCarrierAuthorityAccepted
    (failClosedFlags canonicalQQCarrierSurface)
  ≡
  false
surfaceDoesNotAcceptExternalQQ =
  refl

surfaceDoesNotAcceptExternalNo :
  externalNoCarrierAuthorityAccepted
    (failClosedFlags canonicalQQCarrierSurface)
  ≡
  false
surfaceDoesNotAcceptExternalNo =
  refl

surfaceDoesNotClaimCompleteQQ :
  completeQQClaimed (failClosedFlags canonicalQQCarrierSurface) ≡ false
surfaceDoesNotClaimCompleteQQ =
  refl

surfaceDoesNotClaimCompleteNo :
  completeNoClaimed (failClosedFlags canonicalQQCarrierSurface) ≡ false
surfaceDoesNotClaimCompleteNo =
  refl
