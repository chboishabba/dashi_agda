module DASHI.Physics.QuantumVacuum.BishopPolarJacobianSameTrigWeldCompilerExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

import Real as Bishop

import DASHI.Analysis.BishopPolarJacobianDeterminantExact as Determinant
import DASHI.Analysis.BishopRound11ClassicalTrigObjectWeldExact as Shared
import DASHI.Analysis.BishopRound11FactorDerivativeInterchangeExact as Trig
import DASHI.Foundations.BishopPowerSeriesElementaryBridgeExact as Elementary
import DASHI.Physics.QuantumVacuum.BishopPolarCoordinateDerivativeCompilerExact as Coordinates

------------------------------------------------------------------------
-- ONE SHARED TRIG WELD -> FULL POINTWISE BISHOP POLAR JACOBIAN RECEIPT
------------------------------------------------------------------------

record BishopPolarJacobianReceipt
    (P : Trig.Round11FactorInterchangeProblem)
    (radius theta : Bishop.ℝ) : Set₁ where
  field
    derivativeEntries :
      Coordinates.BishopPolarCoordinateDerivativeReceipt P radius theta

    pythagorean :
      Bishop._≃_
        (Bishop._+_
          (Bishop._*_
            (Elementary.bishopSin (Trig.dataSet P) theta)
            (Elementary.bishopSin (Trig.dataSet P) theta))
          (Bishop._*_
            (Elementary.bishopCos (Trig.dataSet P) theta)
            (Elementary.bishopCos (Trig.dataSet P) theta)))
        Bishop.1ℝ

    determinantEqualsRadius :
      Bishop._≃_
        (Determinant.bishopPolarDeterminant
          radius
          (Elementary.bishopCos (Trig.dataSet P) theta)
          (Elementary.bishopSin (Trig.dataSet P) theta))
        radius

    reading : String

open BishopPolarJacobianReceipt public

compileBishopPolarJacobian :
  ∀ {P} →
  (W : Shared.Round11ClassicalTrigObjectWeld P) →
  (radius theta : Bishop.ℝ) →
  BishopPolarJacobianReceipt P radius theta
compileBishopPolarJacobian {P} W radius theta =
  let
    derivativeAuthority = Shared.compileRound11DerivativeAuthority P W
    pyth = Shared.compileRound11Pythagorean P W theta
  in record
    { derivativeEntries =
        Coordinates.compileBishopPolarCoordinateDerivatives
          derivativeAuthority radius theta
    ; pythagorean = pyth
    ; determinantEqualsRadius =
        Determinant.polarDeterminantIsRadius
          radius
          (Elementary.bishopCos (Trig.dataSet P) theta)
          (Elementary.bishopSin (Trig.dataSet P) theta)
          pyth
    ; reading =
        "One classical/Bishop sine-cosine object weld compiles the four Bishop polar derivatives, Pythagorean identity, and det(D Phi)=radius on the same local trigonometric object."
    }

record Status : Set where
  field
    sharedTrigWeldReusedForDerivativeAndPythagorean : Bool
    fourPolarDerivativeEntriesCompilerOwned : Bool
    bishopDeterminantRadiusCompilerOwned : Bool
    remainingPolarPaymentIsMeasureTheoretic : Bool

    sharedTrigWeldReusedForDerivativeAndPythagoreanIsTrue :
      sharedTrigWeldReusedForDerivativeAndPythagorean ≡ true
    fourPolarDerivativeEntriesCompilerOwnedIsTrue :
      fourPolarDerivativeEntriesCompilerOwned ≡ true
    bishopDeterminantRadiusCompilerOwnedIsTrue :
      bishopDeterminantRadiusCompilerOwned ≡ true
    remainingPolarPaymentIsMeasureTheoreticIsTrue :
      remainingPolarPaymentIsMeasureTheoretic ≡ true

open Status public

canonicalStatus : Status
canonicalStatus = record
  { sharedTrigWeldReusedForDerivativeAndPythagorean = true
  ; fourPolarDerivativeEntriesCompilerOwned = true
  ; bishopDeterminantRadiusCompilerOwned = true
  ; remainingPolarPaymentIsMeasureTheoretic = true
  ; sharedTrigWeldReusedForDerivativeAndPythagoreanIsTrue = refl
  ; fourPolarDerivativeEntriesCompilerOwnedIsTrue = refl
  ; bishopDeterminantRadiusCompilerOwnedIsTrue = refl
  ; remainingPolarPaymentIsMeasureTheoreticIsTrue = refl
  }
