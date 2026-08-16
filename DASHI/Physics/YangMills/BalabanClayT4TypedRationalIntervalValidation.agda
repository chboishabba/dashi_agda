module DASHI.Physics.YangMills.BalabanClayT4TypedRationalIntervalValidation where

------------------------------------------------------------------------
-- Focused T4 validation root for the arithmetic layer beneath the literal
-- Brillouin-box evaluator.  The source-facing transcendental/diagram leaves
-- remain separate; this root records that the rational recursion itself no
-- longer needs an opaque soundness token.
------------------------------------------------------------------------

import DASHI.Physics.YangMills.BalabanClayT4PositiveDenominatorQuotientEndpointsExact as Quotient
import DASHI.Physics.YangMills.BalabanClayT4TypedRationalExpressionIntervalExact as Typed

positiveReciprocalAntitoneLevel =
  Quotient.positiveDenominatorReciprocalAntitoneLevel

positiveQuotientEnclosureLevel =
  Quotient.positiveDenominatorQuotientEnclosureLevel

addSubtractNegateSoundLevel =
  Typed.rationalIntervalAddSubtractNegateSoundLevel

fourCornerMultiplySoundLevel =
  Typed.rationalIntervalFourCornerMultiplySoundLevel

positiveDivisionSoundLevel =
  Typed.rationalIntervalPositiveDivisionSoundLevel

recursiveDiagramExpressionSoundLevel =
  Typed.typedDiagramExpressionRecursiveSoundnessLevel
