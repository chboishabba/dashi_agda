{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.BalabanYM4WardQuarticResponseCanonicalChoiceExact where

------------------------------------------------------------------------
-- ROW A: FIXED WARD FLOOR REMOVES b FROM THE QUARTIC-RESPONSE SOURCE PACKAGE
--
-- The Gaussian producer is already calibrated algebraically to
--
--                     b_Ward = 1 / 8388608.
--
-- Once the same-object patch/jet identification lands, the quartic-response
-- small-coupling choice therefore depends only on four finite nonnegative source
-- constants:
--
--                     C, L_local, R, D.
--
-- This adapter fixes b=b_Ward, proves b<=1 by exact rational arithmetic, and
-- reuses the generic canonical theorem.  The resulting cap is positive, <=1,
-- and satisfies
--
--                (C + L_local + 4 R D) gamma < b_Ward.
------------------------------------------------------------------------

open import Data.Rational.Base as ℚ using (ℚ; 0ℚ; 1ℚ; _≤_; _<_)
import Data.Rational.Properties as ℚP
open import Relation.Nullary.Decidable using (toWitness)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanYM4RowAWardFloorCanonicalGateExact as Ward
import DASHI.Physics.YangMills.BalabanYM4QuarticResponseCanonicalChoiceExact as Choice

record WardQuarticResponseConstants : Set where
  field
    interactionConstant localDerivative : ℚ
    responseCoefficient sourceCoefficient : ℚ

    interactionConstantNonnegative : 0ℚ ≤ interactionConstant
    localDerivativeNonnegative : 0ℚ ≤ localDerivative
    responseCoefficientNonnegative : 0ℚ ≤ responseCoefficient
    sourceCoefficientNonnegative : 0ℚ ≤ sourceCoefficient

open WardQuarticResponseConstants public

wardFloorAtMostOne : Ward.wardGaussianFloor ≤ 1ℚ
wardFloorAtMostOne =
  toWitness {a? = Ward.wardGaussianFloor ℚP.≤? 1ℚ} _

asFiniteQuarticResponseConstants :
  WardQuarticResponseConstants → Choice.FiniteQuarticResponseConstants
asFiniteQuarticResponseConstants dataSet = record
  { Choice.FiniteQuarticResponseConstants.gaussianFloor = Ward.wardGaussianFloor
  ; Choice.FiniteQuarticResponseConstants.interactionConstant =
      interactionConstant dataSet
  ; Choice.FiniteQuarticResponseConstants.localDerivative =
      localDerivative dataSet
  ; Choice.FiniteQuarticResponseConstants.responseCoefficient =
      responseCoefficient dataSet
  ; Choice.FiniteQuarticResponseConstants.sourceCoefficient =
      sourceCoefficient dataSet
  ; Choice.FiniteQuarticResponseConstants.gaussianFloorPositive =
      Ward.wardGaussianFloorPositive
  ; Choice.FiniteQuarticResponseConstants.gaussianFloorAtMostOne =
      wardFloorAtMostOne
  ; Choice.FiniteQuarticResponseConstants.interactionConstantNonnegative =
      interactionConstantNonnegative dataSet
  ; Choice.FiniteQuarticResponseConstants.localDerivativeNonnegative =
      localDerivativeNonnegative dataSet
  ; Choice.FiniteQuarticResponseConstants.responseCoefficientNonnegative =
      responseCoefficientNonnegative dataSet
  ; Choice.FiniteQuarticResponseConstants.sourceCoefficientNonnegative =
      sourceCoefficientNonnegative dataSet
  }

wardQuarticResponseGamma : WardQuarticResponseConstants → ℚ
wardQuarticResponseGamma dataSet =
  Choice.canonicalQuarticResponseGamma
    (asFiniteQuarticResponseConstants dataSet)

wardQuarticResponseGammaPositive :
  (dataSet : WardQuarticResponseConstants) →
  0ℚ < wardQuarticResponseGamma dataSet
wardQuarticResponseGammaPositive dataSet =
  Choice.canonicalQuarticResponseGammaPositive
    (asFiniteQuarticResponseConstants dataSet)

wardQuarticResponseGammaAtMostOne :
  (dataSet : WardQuarticResponseConstants) →
  wardQuarticResponseGamma dataSet ≤ 1ℚ
wardQuarticResponseGammaAtMostOne dataSet =
  Choice.canonicalQuarticResponseGammaAtMostOne
    (asFiniteQuarticResponseConstants dataSet)

wardQuarticResponsePaysLinearGate :
  (dataSet : WardQuarticResponseConstants) →
  (interactionConstant dataSet + localDerivative dataSet
    + DASHI.Physics.YangMills.BalabanYM4QuarticResponseCanonicalGateExact.fourℚ
        * responseCoefficient dataSet * sourceCoefficient dataSet)
    * wardQuarticResponseGamma dataSet
  < Ward.wardGaussianFloor
wardQuarticResponsePaysLinearGate dataSet =
  Choice.canonicalQuarticResponsePaysLinearGate
    (asFiniteQuarticResponseConstants dataSet)

wardQuarticResponseCanonicalChoiceLevel : ProofLevel
wardQuarticResponseCanonicalChoiceLevel = machineChecked

wardQuarticResponseFloorAtMostOneLevel : ProofLevel
wardQuarticResponseFloorAtMostOneLevel = machineChecked

-- Source-facing Row-A numeric package is now just C,L_local,R,D.  The Ward floor
-- and every small-coupling arithmetic condition are fixed downstream.
literalWardQuarticResponseConstantsLevel : ProofLevel
literalWardQuarticResponseConstantsLevel = conditional
