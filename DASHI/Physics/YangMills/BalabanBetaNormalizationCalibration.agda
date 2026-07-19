module DASHI.Physics.YangMills.BalabanBetaNormalizationCalibration where

open import Agda.Builtin.Equality using (_≡_)

record BetaNormalizationCalibration (Scalar : Set) : Set₁ where
  field
    extractedBeta referenceBeta residual : Scalar
    add : Scalar → Scalar → Scalar
    calibrationEquation : extractedBeta ≡ add referenceBeta residual

open BetaNormalizationCalibration public
