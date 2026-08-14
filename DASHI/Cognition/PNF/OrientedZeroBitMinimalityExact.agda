module DASHI.Cognition.PNF.OrientedZeroBitMinimalityExact where

open import DASHI.Core.Prelude

import DASHI.Cognition.PNF.OrientedZeroFutureQuotientExact as Wave
import DASHI.Core.ResidualBitLowerBoundThreeExact as Three

------------------------------------------------------------------------
-- TWO DIFFERENT CODING QUESTIONS MUST NOT BE CONFLATED
--
-- (1) Standalone fixed-length code for all four oriented wave states:
--     two bits are necessary and sufficient.
--
-- (2) Residual paired with the already-retained scalar projection:
--     only the zero fibre needs an additional distinction, so one local bit is
--     necessary and sufficient there and no residual bit is needed off zero.
------------------------------------------------------------------------

record OneBitStandaloneCode (encode : Wave.Wave4 → Bool) : Set₁ where
  constructor oneBitStandaloneCode
  field
    decode : Bool → Wave.Wave4
    decodeExact : (state : Wave.Wave4) → decode (encode state) ≡ state

open OneBitStandaloneCode public

oneBitCannotEncodeFourWaveStatesExactly :
  (encode : Wave.Wave4 → Bool) → OneBitStandaloneCode encode → ⊥
oneBitCannotEncodeFourWaveStatesExactly encode receipt
  with Three.threeBooleansHaveCollision
    (encode Wave.negativeOne)
    (encode Wave.negativeZero)
    (encode Wave.positiveZero)
... | inj₁ equality = negativeOneNotNegativeZero stateEquality
  where
    stateEquality : Wave.negativeOne ≡ Wave.negativeZero
    stateEquality =
      trans
        (sym (decodeExact receipt Wave.negativeOne))
        (trans (cong (decode receipt) equality)
          (decodeExact receipt Wave.negativeZero))

    negativeOneNotNegativeZero : Wave.negativeOne ≡ Wave.negativeZero → ⊥
    negativeOneNotNegativeZero ()
... | inj₂ (inj₁ equality) = negativeOneNotPositiveZero stateEquality
  where
    stateEquality : Wave.negativeOne ≡ Wave.positiveZero
    stateEquality =
      trans
        (sym (decodeExact receipt Wave.negativeOne))
        (trans (cong (decode receipt) equality)
          (decodeExact receipt Wave.positiveZero))

    negativeOneNotPositiveZero : Wave.negativeOne ≡ Wave.positiveZero → ⊥
    negativeOneNotPositiveZero ()
... | inj₂ (inj₂ equality) = negativeZeroNotPositiveZero stateEquality
  where
    stateEquality : Wave.negativeZero ≡ Wave.positiveZero
    stateEquality =
      trans
        (sym (decodeExact receipt Wave.negativeZero))
        (trans (cong (decode receipt) equality)
          (decodeExact receipt Wave.positiveZero))

    negativeZeroNotPositiveZero : Wave.negativeZero ≡ Wave.positiveZero → ⊥
    negativeZeroNotPositiveZero ()

record TwoBitStandaloneCode : Set₁ where
  constructor twoBitStandaloneCode
  field
    encode : Wave.Wave4 → Wave.TwoBit
    decode : Wave.TwoBit → Wave.Wave4
    decodeExact : (state : Wave.Wave4) → decode (encode state) ≡ state

open TwoBitStandaloneCode public

canonicalTwoBitStandaloneCode : TwoBitStandaloneCode
canonicalTwoBitStandaloneCode =
  twoBitStandaloneCode Wave.binaryCode Wave.binaryDecode Wave.binaryTwoBitsReopenExactly

------------------------------------------------------------------------
-- Local zero-fibre bound.  With scalar value already retained, the only
-- collision is {-0,+0}; a Boolean residual resolves it exactly.
------------------------------------------------------------------------

zeroOrientationBit : Wave.Wave4 → Bool
zeroOrientationBit Wave.negativeOne = false
zeroOrientationBit Wave.negativeZero = false
zeroOrientationBit Wave.positiveZero = true
zeroOrientationBit Wave.positiveOne = false

reopenScalarAndBit : Wave.Scalar3 → Bool → Wave.Wave4
reopenScalarAndBit Wave.negative bit = Wave.negativeOne
reopenScalarAndBit Wave.scalarZero false = Wave.negativeZero
reopenScalarAndBit Wave.scalarZero true = Wave.positiveZero
reopenScalarAndBit Wave.positive bit = Wave.positiveOne

scalarPlusOneBitReopensExactly :
  (state : Wave.Wave4) →
  reopenScalarAndBit (Wave.scalar state) (zeroOrientationBit state) ≡ state
scalarPlusOneBitReopensExactly Wave.negativeOne = refl
scalarPlusOneBitReopensExactly Wave.negativeZero = refl
scalarPlusOneBitReopensExactly Wave.positiveZero = refl
scalarPlusOneBitReopensExactly Wave.positiveOne = refl

record ZeroFibreNoBitResidual : Set₁ where
  constructor zeroFibreNoBitResidual
  field
    reopenZeroWithoutOrientation : Wave.Wave4
    negativeZeroExact : reopenZeroWithoutOrientation ≡ Wave.negativeZero
    positiveZeroExact : reopenZeroWithoutOrientation ≡ Wave.positiveZero

zeroFibreCannotReopenWithoutOrientation : ZeroFibreNoBitResidual → ⊥
zeroFibreCannotReopenWithoutOrientation impossible = distinct
  (trans
    (sym (negativeZeroExact impossible))
    (positiveZeroExact impossible))
  where
    distinct : Wave.negativeZero ≡ Wave.positiveZero → ⊥
    distinct ()

------------------------------------------------------------------------
-- Therefore:
--   standalone Wave4 code: exactly two fixed bits;
--   scalar projection + adaptive residual: exactly one extra bit on zero,
--   zero extra bits on the two singleton nonzero fibres.
------------------------------------------------------------------------
