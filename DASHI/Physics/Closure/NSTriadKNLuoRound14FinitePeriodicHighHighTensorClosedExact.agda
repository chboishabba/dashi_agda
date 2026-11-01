module DASHI.Physics.Closure.NSTriadKNLuoRound14FinitePeriodicHighHighTensorClosedExact where

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
-- Finish the finite periodic HH1 chain by composing the concrete coefficient
-- estimate with the repository's Gram-defect proof of tensor Holder:
--
--   HMinusOneSquared
--     <= outputScaleCubed * tensorL1Squared
--     <= outputScaleCubed * leftL2Squared * rightL2Squared.
--
-- No tensor Holder or support-count estimate remains as a free field.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_)
open import Data.Rational.Base using
  (ℚ; 0ℚ; _*_; _≤_; nonNegative)
import Data.Rational.Properties as ℚₚ
open import Relation.Binary.PropositionalEquality using (subst; sym)

import DASHI.Physics.Closure.NSTriadKNLuoRound14FinitePeriodicHighHighClosedExact as HH
import DASHI.Physics.Closure.NSTriadKNLuoFiniteDyadicBernsteinRealizationExact as Bernstein
import DASHI.Physics.Closure.NSTriadKNLuoFiniteTensorHolderExact as Tensor

record FinitePeriodicHighHighTensorData (Slot : Set) : Set₁ where
  constructor finite-periodic-high-high-tensor-data
  field
    periodicData : HH.FinitePeriodicHighHighClosedData Slot
    tensorData : Tensor.FiniteTensorHolderData

    outputScaleNonnegative :
      0ℚ ≤ Bernstein.outputScaleCubed
        (HH.bernsteinData periodicData)

    tensorInputMeaning :
      Bernstein.commonInputL1Squared
        (HH.bernsteinData periodicData)
      ≡ Tensor.tensorL1Squared tensorData

open FinitePeriodicHighHighTensorData public

finitePeriodicHighHighTensorSquareBound :
  ∀ {Slot : Set}
    (dataSet : FinitePeriodicHighHighTensorData Slot) →
  HH.finiteHMinusOneSquared (periodicData dataSet)
  ≤ Bernstein.outputScaleCubed
      (HH.bernsteinData (periodicData dataSet))
    * (Tensor.leftL2Squared (tensorData dataSet)
      * Tensor.rightL2Squared (tensorData dataSet))
finitePeriodicHighHighTensorSquareBound dataSet =
  let
    periodicBound :
      HH.finiteHMinusOneSquared (periodicData dataSet)
      ≤ Bernstein.outputScaleCubed
          (HH.bernsteinData (periodicData dataSet))
        * Bernstein.commonInputL1Squared
          (HH.bernsteinData (periodicData dataSet))
    periodicBound =
      HH.finitePeriodicHighHighHMinusOneSquareBound
        (periodicData dataSet)

    inputAdjusted :
      HH.finiteHMinusOneSquared (periodicData dataSet)
      ≤ Bernstein.outputScaleCubed
          (HH.bernsteinData (periodicData dataSet))
        * Tensor.tensorL1Squared (tensorData dataSet)
    inputAdjusted =
      subst
        (λ inputSquare →
          HH.finiteHMinusOneSquared (periodicData dataSet)
          ≤ Bernstein.outputScaleCubed
              (HH.bernsteinData (periodicData dataSet))
            * inputSquare)
        (tensorInputMeaning dataSet)
        periodicBound

    holderScaled :
      Bernstein.outputScaleCubed
          (HH.bernsteinData (periodicData dataSet))
        * Tensor.tensorL1Squared (tensorData dataSet)
      ≤ Bernstein.outputScaleCubed
          (HH.bernsteinData (periodicData dataSet))
        * (Tensor.leftL2Squared (tensorData dataSet)
          * Tensor.rightL2Squared (tensorData dataSet))
    holderScaled =
      let
        instance
          scaleIsNonnegative =
            nonNegative (outputScaleNonnegative dataSet)
      in
      ℚₚ.*-monoˡ-≤-nonNeg
        (Bernstein.outputScaleCubed
          (HH.bernsteinData (periodicData dataSet)))
        (Tensor.finiteTensorHolderSquare (tensorData dataSet))
  in
  ℚₚ.≤-trans inputAdjusted holderScaled
