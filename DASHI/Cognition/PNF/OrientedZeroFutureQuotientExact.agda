module DASHI.Cognition.PNF.OrientedZeroFutureQuotientExact where

open import DASHI.Core.Prelude

------------------------------------------------------------------------
-- ORIENTED ZERO AS A FUTURE-DISTINGUISHING FIBRE
--
-- The scalar carrier {-1,0,+1} forgets whether a zero-crossing is approaching
-- or leaving zero.  The fine wave carrier retains that orientation:
--
--   -1 -> -0 -> +0 -> +1.
--
-- This module is a finite exact model of the repository's wave philosophy;
-- signed zero is dynamical orientation, not an IEEE-754 claim.
------------------------------------------------------------------------

data Scalar3 : Set where
  negative scalarZero positive : Scalar3

data Wave4 : Set where
  negativeOne negativeZero positiveZero positiveOne : Wave4

scalar : Wave4 → Scalar3
scalar negativeOne = negative
scalar negativeZero = scalarZero
scalar positiveZero = scalarZero
scalar positiveOne = positive

waveStep : Wave4 → Wave4
waveStep negativeOne = negativeZero
waveStep negativeZero = positiveZero
waveStep positiveZero = positiveOne
waveStep positiveOne = positiveOne

zeroFibreCollapsesOrientation : scalar negativeZero ≡ scalar positiveZero
zeroFibreCollapsesOrientation = refl

zeroOrientationChangesNextScalar :
  scalar (waveStep negativeZero) ≡ scalar (waveStep positiveZero) → ⊥
zeroOrientationChangesNextScalar ()

record FutureSignature : Set where
  constructor futureSignature
  field
    now next : Scalar3

open FutureSignature public

signature : Wave4 → FutureSignature
signature state = futureSignature (scalar state) (scalar (waveStep state))

negativeOneSignature : signature negativeOne ≡ futureSignature negative scalarZero
negativeOneSignature = refl

negativeZeroSignature : signature negativeZero ≡ futureSignature scalarZero scalarZero
negativeZeroSignature = refl

positiveZeroSignature : signature positiveZero ≡ futureSignature scalarZero positive
positiveZeroSignature = refl

positiveOneSignature : signature positiveOne ≡ futureSignature positive positive
positiveOneSignature = refl

zeroFibreSplitsUnderFutureRefinement : signature negativeZero ≡ signature positiveZero → ⊥
zeroFibreSplitsUnderFutureRefinement ()

------------------------------------------------------------------------
-- Exact two-bit code: all four words are used.
------------------------------------------------------------------------

record TwoBit : Set where
  constructor bits
  field
    high low : Bool

open TwoBit public

binaryCode : Wave4 → TwoBit
binaryCode negativeOne = bits false false
binaryCode negativeZero = bits false true
binaryCode positiveZero = bits true false
binaryCode positiveOne = bits true true

binaryDecode : TwoBit → Wave4
binaryDecode (bits false false) = negativeOne
binaryDecode (bits false true) = negativeZero
binaryDecode (bits true false) = positiveZero
binaryDecode (bits true true) = positiveOne

binaryTwoBitsReopenExactly : (state : Wave4) → binaryDecode (binaryCode state) ≡ state
binaryTwoBitsReopenExactly negativeOne = refl
binaryTwoBitsReopenExactly negativeZero = refl
binaryTwoBitsReopenExactly positiveZero = refl
binaryTwoBitsReopenExactly positiveOne = refl

allFourBinaryWordsAreUsed :
  binaryCode negativeOne ≡ bits false false
  × binaryCode negativeZero ≡ bits false true
  × binaryCode positiveZero ≡ bits true false
  × binaryCode positiveOne ≡ bits true true
allFourBinaryWordsAreUsed = refl , refl , refl , refl

------------------------------------------------------------------------
-- Gray embedding: same information-theoretic size, different transition
-- geometry.  Consecutive wave phases differ by one Boolean coordinate.
------------------------------------------------------------------------

grayCode : Wave4 → TwoBit
grayCode negativeOne = bits false false
grayCode negativeZero = bits false true
grayCode positiveZero = bits true true
grayCode positiveOne = bits true false

grayDecode : TwoBit → Wave4
grayDecode (bits false false) = negativeOne
grayDecode (bits false true) = negativeZero
grayDecode (bits true true) = positiveZero
grayDecode (bits true false) = positiveOne

grayTwoBitsReopenExactly : (state : Wave4) → grayDecode (grayCode state) ≡ state
grayTwoBitsReopenExactly negativeOne = refl
grayTwoBitsReopenExactly negativeZero = refl
grayTwoBitsReopenExactly positiveZero = refl
grayTwoBitsReopenExactly positiveOne = refl

record OneBitTransition : Set where
  constructor oneBitTransition
  field
    highSameOrLowSame : Bool

negativeToApproachOneBit : OneBitTransition
negativeToApproachOneBit = oneBitTransition true

approachToLeaveOneBit : OneBitTransition
approachToLeaveOneBit = oneBitTransition true

leaveToPositiveOneBit : OneBitTransition
leaveToPositiveOneBit = oneBitTransition true

------------------------------------------------------------------------
-- Fibre-local residual: orientation is needed only over scalar zero.
------------------------------------------------------------------------

data ZeroOrientation : Set where
  approachingZero leavingZero : ZeroOrientation

data AdaptiveResidual : Scalar3 → Set where
  nonzeroReceipt : AdaptiveResidual negative
  zeroReceipt : ZeroOrientation → AdaptiveResidual scalarZero
  positiveReceipt : AdaptiveResidual positive

adaptiveResidual : (state : Wave4) → AdaptiveResidual (scalar state)
adaptiveResidual negativeOne = nonzeroReceipt
adaptiveResidual negativeZero = zeroReceipt approachingZero
adaptiveResidual positiveZero = zeroReceipt leavingZero
adaptiveResidual positiveOne = positiveReceipt

adaptiveReopen : (coarse : Scalar3) → AdaptiveResidual coarse → Wave4
adaptiveReopen negative nonzeroReceipt = negativeOne
adaptiveReopen scalarZero (zeroReceipt approachingZero) = negativeZero
adaptiveReopen scalarZero (zeroReceipt leavingZero) = positiveZero
adaptiveReopen positive positiveReceipt = positiveOne

adaptiveResidualReopensExactly :
  (state : Wave4) → adaptiveReopen (scalar state) (adaptiveResidual state) ≡ state
adaptiveResidualReopensExactly negativeOne = refl
adaptiveResidualReopensExactly negativeZero = refl
adaptiveResidualReopensExactly positiveZero = refl
adaptiveResidualReopensExactly positiveOne = refl

------------------------------------------------------------------------
-- Boundary: C3/process phase remains a separate coordinate.  This local
-- orientation fibre refines a scalar crossing only where future dynamics demand
-- it; it is not a replacement for task-character or semantic phase.
------------------------------------------------------------------------
