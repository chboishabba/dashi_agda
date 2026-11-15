module DASHI.Physics.Plasma.KSW668OriginalRationalTransferCountermodelExact where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Relation.Binary.PropositionalEquality using (cong; trans)
open import Agda.Builtin.String using (String)

import DASHI.Physics.Closure.NSTriadKNComplex3ExactCarrier as C3
import DASHI.Physics.Closure.NSTriadKNRationalOrderedFiniteL2 as Rational
import DASHI.Physics.Plasma.MHDFullTransferFromExchangeCompatiblePayloadExact as MHD

------------------------------------------------------------------------
-- Stronger A: exact original C3.RealField rational instance and actual
-- ExchangeCompatibleTransfer values on that SAME source carrier.
-- Neither direction is inferred from scalar magnitudes or physical |B|.
------------------------------------------------------------------------

private
  F : C3.RealField _
  F = Rational.rationalRealField

  unit : C3.Carrier F
  unit = C3.one F

  negativeUnit : C3.Carrier F
  negativeUnit = C3.negate F unit

  multiplyRightUnit : (x : C3.Carrier F) →
    C3.multiply F x unit ≡ x
  multiplyRightUnit x =
    trans (C3.multiplyCommutative F x unit)
          (C3.multiplyOneLeft F x)

positiveSourcePair : MHD.ExchangeCompatibleTransfer F
positiveSourcePair =
  MHD.exchange-compatible-transfer
    (C3.negate F negativeUnit)
    negativeUnit
    unit unit
    refl refl
    "original rational C3: forward +1, reverse -1, payload +1"

negativeSourcePair : MHD.ExchangeCompatibleTransfer F
negativeSourcePair =
  MHD.exchange-compatible-transfer
    negativeUnit
    unit
    unit unit
    refl refl
    "original rational C3: forward -1, reverse +1, payload +1"

positiveForwardIsUnit :
  MHD.forwardTransfer positiveSourcePair ≡ unit
positiveForwardIsUnit =
  trans
    (cong (λ v → C3.multiply F v unit)
      (C3.negateInvolutive F unit))
    (multiplyRightUnit unit)

negativeForwardIsNegativeUnit :
  MHD.forwardTransfer negativeSourcePair ≡ negativeUnit
negativeForwardIsNegativeUnit = multiplyRightUnit negativeUnit

positivePairCancels :
  C3.add F (MHD.forwardTransfer positiveSourcePair)
    (MHD.reverseTransfer positiveSourcePair) ≡ C3.zero F
positivePairCancels = MHD.pairTransferCancels positiveSourcePair

negativePairCancels :
  C3.add F (MHD.forwardTransfer negativeSourcePair)
    (MHD.reverseTransfer negativeSourcePair) ≡ C3.zero F
negativePairCancels = MHD.pairTransferCancels negativeSourcePair
