module DASHI.Physics.Closure.NSTriadKNLuoFinitePeriodicHighHighLowProducerExact where

------------------------------------------------------------------------
-- PROVENANCE
--
-- Authors: Hajer Bahouri; Jean-Yves Chemin; Raphael Danchin.
-- Title: "Fourier Analysis and Nonlinear Partial Differential Equations".
-- DOI: 10.1007/978-3-642-16830-7.
--
-- Author: Loukas Grafakos.
-- Title: "Classical Fourier Analysis".
-- DOI: 10.1007/978-1-4939-1194-3.
--
-- PURPOSE
-- Compose the actual finite periodic Fourier ingredients of HH1 in squared
-- form:
--
--   ||Delta_q P div F||_(H^-1)^2
--     <= ||Delta_q F||_2^2
--     <= lambda_q^3 ||F||_1^2
--     <= lambda_q^3 ||f||_2^2 ||g||_2^2.
--
-- The first two inequalities are proved by the imported finite mode modules.
-- The only remaining producer field is tensor Holder, which is kept explicit
-- because it depends on the concrete tensor carrier used by the continuum
-- realization.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.List using (List)
open import Data.Rational.Base using
  (ℚ; 0ℚ; _*_; _≤_; nonNegative)
import Data.Rational.Properties as ℚₚ
open import Relation.Binary.PropositionalEquality using (subst)

import DASHI.Physics.Closure.NSTriadKNLuoFinitePeriodicLerayDivergenceExact as Leray
import DASHI.Physics.Closure.NSTriadKNLuoFinitePeriodicBernsteinSupportExact as Bernstein

record PeriodicHighHighLowProducerData : Set₁ where
  constructor periodic-high-high-low-producer-data
  field
    lerayModes : List Leray.PeriodicLerayMode
    bernsteinData : Bernstein.FinitePeriodicBernsteinData
    leftL2Squared rightL2Squared : ℚ

    outputScaleCubedNonnegative :
      0ℚ ≤ Bernstein.outputScaleCubed bernsteinData

    parsevalBridge :
      Leray.sumTensorModeSquared lerayModes
      ≡ Bernstein.outputL2Squared (Bernstein.modes bernsteinData)

    tensorHolderSquareBound :
      Bernstein.inputL1Squared bernsteinData
      ≤ leftL2Squared * rightL2Squared

open PeriodicHighHighLowProducerData public

periodicHighHighLowSquareBound :
  (dataSet : PeriodicHighHighLowProducerData) →
  Leray.sumHMinusOneSquared (lerayModes dataSet)
  ≤ Bernstein.outputScaleCubed (bernsteinData dataSet)
      * (leftL2Squared dataSet * rightL2Squared dataSet)
periodicHighHighLowSquareBound dataSet =
  let
    projectionStep :
      Leray.sumHMinusOneSquared (lerayModes dataSet)
      ≤ Bernstein.outputL2Squared
          (Bernstein.modes (bernsteinData dataSet))
    projectionStep =
      subst
        (λ upper →
          Leray.sumHMinusOneSquared (lerayModes dataSet) ≤ upper)
        (parsevalBridge dataSet)
        (Leray.finitePeriodicLerayCancellation (lerayModes dataSet))

    bernsteinStep :
      Bernstein.outputL2Squared
        (Bernstein.modes (bernsteinData dataSet))
      ≤ Bernstein.outputScaleCubed (bernsteinData dataSet)
          * Bernstein.inputL1Squared (bernsteinData dataSet)
    bernsteinStep =
      Bernstein.finitePeriodicBernsteinSquare (bernsteinData dataSet)

    scaledHolder :
      Bernstein.outputScaleCubed (bernsteinData dataSet)
        * Bernstein.inputL1Squared (bernsteinData dataSet)
      ≤ Bernstein.outputScaleCubed (bernsteinData dataSet)
          * (leftL2Squared dataSet * rightL2Squared dataSet)
    scaledHolder =
      let
        instance
          outputScaleIsNonnegative =
            nonNegative (outputScaleCubedNonnegative dataSet)
      in
      ℚₚ.*-monoˡ-≤-nonNeg
        (Bernstein.outputScaleCubed (bernsteinData dataSet))
        (tensorHolderSquareBound dataSet)
  in
  ℚₚ.≤-trans
    projectionStep
    (ℚₚ.≤-trans bernsteinStep scaledHolder)
