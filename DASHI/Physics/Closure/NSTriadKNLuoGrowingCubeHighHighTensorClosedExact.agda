module DASHI.Physics.Closure.NSTriadKNLuoGrowingCubeHighHighTensorClosedExact where

------------------------------------------------------------------------
-- PROVENANCE
--
-- Authors: Hajer Bahouri; Jean-Yves Chemin; Raphael Danchin.
-- Title: "Fourier Analysis and Nonlinear Partial Differential Equations".
-- DOI: 10.1007/978-3-642-16830-7.
--
-- Authors: Augustin-Louis Cauchy; Hermann Amandus Schwarz.
-- Title: finite Cauchy--Schwarz inequality.
-- DOI: not applicable to the nineteenth-century result.
--
-- PURPOSE
-- Compose the growing-cube Leray/Fourier producer with the repository's
-- checked tensor Holder theorem:
--
--   HMinusOneSquared
--     <= 125 * 8^q * tensorL1Squared
--     <= 125 * 8^q * leftL2Squared * rightL2Squared.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Nat using (Nat)
open import Data.Rational.Base using
  (ℚ; 0ℚ; _*_; _≤_; nonNegative)
import Data.Rational.Properties as ℚₚ
open import Relation.Binary.PropositionalEquality using (subst)

import DASHI.Physics.Closure.NSTriadKNLuoGrowingCubeHighHighClosedExact as HH
import DASHI.Physics.Closure.NSTriadKNLuoGrowingCubeBernsteinExact as Bernstein
import DASHI.Physics.Closure.NSTriadKNLuoFiniteTensorHolderExact as Tensor
import DASHI.Physics.Closure.NSTriadKNLuoIntegerCubeSupportCapacityExact as Capacity
import DASHI.Physics.Closure.NSTriadKNRationalFiniteGeometricEnvelope as Geo

scaleCoefficient : Nat → ℚ
scaleCoefficient shell =
  Capacity.oneTwentyFive * Capacity.eightPower shell

scaleCoefficientNonnegative :
  (shell : Nat) → 0ℚ ≤ scaleCoefficient shell
scaleCoefficientNonnegative shell =
  let
    powerNN =
      Geo.powNonnegative
        Capacity.eight shell Capacity.eightNonnegative
    instance
      constantNN = nonNegative Capacity.oneTwentyFiveNonnegative
      powerNNI = nonNegative powerNN
      productNN =
        ℚₚ.nonNeg*nonNeg⇒nonNeg
          Capacity.oneTwentyFive
          (Capacity.eightPower shell)
  in
  ℚₚ.nonNegative⁻¹ (scaleCoefficient shell)

record GrowingCubeHighHighTensorData (shell : Nat) : Set₁ where
  constructor growing-cube-high-high-tensor-data
  field
    highHighData : HH.GrowingCubeHighHighData shell
    tensorData : Tensor.FiniteTensorHolderData
    tensorInputMeaning :
      Bernstein.commonInputL1Squared
        (HH.bernsteinData highHighData)
      ≡ Tensor.tensorL1Squared tensorData

open GrowingCubeHighHighTensorData public

growingCubeHighHighTensorSquareBound :
  (shell : Nat) →
  (dataSet : GrowingCubeHighHighTensorData shell) →
  HH.finiteHMinusOneSquared shell (highHighData dataSet)
  ≤ scaleCoefficient shell
    * (Tensor.leftL2Squared (tensorData dataSet)
      * Tensor.rightL2Squared (tensorData dataSet))
growingCubeHighHighTensorSquareBound shell dataSet =
  let
    producer =
      HH.growingCubeHighHighSquareBound
        shell
        (highHighData dataSet)

    inputAdjusted :
      HH.finiteHMinusOneSquared shell (highHighData dataSet)
      ≤ scaleCoefficient shell
        * Tensor.tensorL1Squared (tensorData dataSet)
    inputAdjusted =
      subst
        (λ inputSquare →
          HH.finiteHMinusOneSquared shell (highHighData dataSet)
          ≤ scaleCoefficient shell * inputSquare)
        (tensorInputMeaning dataSet)
        producer

    holderScaled :
      scaleCoefficient shell * Tensor.tensorL1Squared (tensorData dataSet)
      ≤ scaleCoefficient shell
        * (Tensor.leftL2Squared (tensorData dataSet)
          * Tensor.rightL2Squared (tensorData dataSet))
    holderScaled =
      let instance scaleNN =
        nonNegative (scaleCoefficientNonnegative shell)
      in
      ℚₚ.*-monoˡ-≤-nonNeg
        (scaleCoefficient shell)
        (Tensor.finiteTensorHolderSquare (tensorData dataSet))
  in
  ℚₚ.≤-trans inputAdjusted holderScaled
