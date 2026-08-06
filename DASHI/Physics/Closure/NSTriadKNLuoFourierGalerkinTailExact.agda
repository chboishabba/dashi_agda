module DASHI.Physics.Closure.NSTriadKNLuoFourierGalerkinTailExact where

------------------------------------------------------------------------
-- PROVENANCE
--
-- Author: Roger Temam.
-- Title: "Navier-Stokes Equations: Theory and Numerical Analysis".
-- DOI: 10.1090/chel/343.
--
-- Author: John G. Heywood.
-- Title: "An Error Estimate Uniform in Time for Spectral Galerkin
-- Approximations of the Navier-Stokes Problem".
-- DOI: 10.2140/pjm.1982.98.333.
--
-- Authors: Hajer Bahouri; Jean-Yves Chemin; Raphaël Danchin.
-- Title: "Fourier Analysis and Nonlinear Partial Differential Equations".
-- DOI: 10.1007/978-3-642-16830-7.
--
-- PURPOSE
-- Prove the finite weighted Fourier-tail theorem that underlies the physical
-- Galerkin estimate
--
--   ||(I-P_N)u||_{H^m}²
--     <= N^{-2(s-m)} ||u||_{H^s}².
--
-- The theorem is stated in its exact reusable form: each retained tail mode
-- carries a target weight bounded by one common decay factor times its source
-- weight.  The global estimate is then proved by finite induction, including
-- the coefficient-square weight.  No convergence or compactness assumption is
-- hidden in the summation step.
------------------------------------------------------------------------

open import Agda.Builtin.List using (List; []; _∷_)
open import Data.Rational.Base using
  (ℚ; 0ℚ; _+_; _*_; _≤_; nonNegative)
import Data.Rational.Properties as ℚₚ
open import Data.Rational.Tactic.RingSolver using (solve)
open import Relation.Binary.PropositionalEquality using (subst)

import DASHI.Physics.Closure.NSTriadKNRationalOrderedFiniteL2 as L2

record FourierTailMode (decay : ℚ) : Set where
  constructor fourier-tail-mode
  field
    sourceWeight targetWeight coefficientSquared : ℚ

    decayNonnegative : 0ℚ ≤ decay
    sourceWeightNonnegative : 0ℚ ≤ sourceWeight
    targetWeightNonnegative : 0ℚ ≤ targetWeight
    coefficientSquaredNonnegative : 0ℚ ≤ coefficientSquared

    tailWeightComparison :
      targetWeight ≤ decay * sourceWeight

open FourierTailMode public

sourceSobolevEnergy :
  (decay : ℚ) →
  List (FourierTailMode decay) →
  ℚ
sourceSobolevEnergy decay [] = 0ℚ
sourceSobolevEnergy decay (modeValue ∷ modes) =
  sourceWeight modeValue * coefficientSquared modeValue
  + sourceSobolevEnergy decay modes

targetTailEnergy :
  (decay : ℚ) →
  List (FourierTailMode decay) →
  ℚ
targetTailEnergy decay [] = 0ℚ
targetTailEnergy decay (modeValue ∷ modes) =
  targetWeight modeValue * coefficientSquared modeValue
  + targetTailEnergy decay modes

sourceModeEnergyNonnegative :
  ∀ {decay}
    (modeValue : FourierTailMode decay) →
  0ℚ ≤ sourceWeight modeValue * coefficientSquared modeValue
sourceModeEnergyNonnegative modeValue =
  let
    instance
      sourceNN = nonNegative (sourceWeightNonnegative modeValue)
      coefficientNN = nonNegative (coefficientSquaredNonnegative modeValue)
      productNN =
        ℚₚ.nonNeg*nonNeg⇒nonNeg
          (sourceWeight modeValue)
          (coefficientSquared modeValue)
  in
  ℚₚ.nonNegative⁻¹
    (sourceWeight modeValue * coefficientSquared modeValue)

scaledSourceWeightNonnegative :
  ∀ {decay}
    (modeValue : FourierTailMode decay) →
  0ℚ ≤ decay * sourceWeight modeValue
scaledSourceWeightNonnegative {decay} modeValue =
  let
    instance
      decayNN = nonNegative (decayNonnegative modeValue)
      sourceNN = nonNegative (sourceWeightNonnegative modeValue)
      productNN =
        ℚₚ.nonNeg*nonNeg⇒nonNeg
          decay
          (sourceWeight modeValue)
  in
  ℚₚ.nonNegative⁻¹ (decay * sourceWeight modeValue)

sourceSobolevEnergyNonnegative :
  (decay : ℚ) →
  (modes : List (FourierTailMode decay)) →
  0ℚ ≤ sourceSobolevEnergy decay modes
sourceSobolevEnergyNonnegative decay [] = ℚₚ.≤-refl
sourceSobolevEnergyNonnegative decay (modeValue ∷ modes) =
  L2.addNonnegative
    (sourceModeEnergyNonnegative modeValue)
    (sourceSobolevEnergyNonnegative decay modes)

localTailModeBound :
  ∀ {decay}
    (modeValue : FourierTailMode decay) →
  targetWeight modeValue * coefficientSquared modeValue
  ≤ decay * (sourceWeight modeValue * coefficientSquared modeValue)
localTailModeBound {decay} modeValue =
  let
    multiplied :
      targetWeight modeValue * coefficientSquared modeValue
      ≤ (decay * sourceWeight modeValue)
        * coefficientSquared modeValue
    multiplied =
      L2.nonnegativeProductMonotone
        (targetWeightNonnegative modeValue)
        (coefficientSquaredNonnegative modeValue)
        (scaledSourceWeightNonnegative modeValue)
        (coefficientSquaredNonnegative modeValue)
        (tailWeightComparison modeValue)
        ℚₚ.≤-refl

    reassociate :
      (decay * sourceWeight modeValue)
        * coefficientSquared modeValue
      ≡ decay
        * (sourceWeight modeValue * coefficientSquared modeValue)
    reassociate =
      solve
        (decay
        ∷ sourceWeight modeValue
        ∷ coefficientSquared modeValue
        ∷ [])
  in
  subst
    (λ upper →
      targetWeight modeValue * coefficientSquared modeValue
      ≤ upper)
    reassociate
    multiplied

fourierGalerkinTailBound :
  (decay : ℚ) →
  (modes : List (FourierTailMode decay)) →
  targetTailEnergy decay modes
  ≤ decay * sourceSobolevEnergy decay modes
fourierGalerkinTailBound decay [] = ℚₚ.≤-refl
fourierGalerkinTailBound decay (modeValue ∷ modes) =
  let
    local = localTailModeBound modeValue
    tail = fourierGalerkinTailBound decay modes
    summed = ℚₚ.+-mono-≤ local tail

    factorized :
      decay
        * (sourceWeight modeValue * coefficientSquared modeValue)
      + decay * sourceSobolevEnergy decay modes
      ≡ decay
        * ( sourceWeight modeValue * coefficientSquared modeValue
          + sourceSobolevEnergy decay modes)
    factorized =
      solve
        ( decay
        ∷ sourceWeight modeValue
        ∷ coefficientSquared modeValue
        ∷ sourceSobolevEnergy decay modes
        ∷ [])
  in
  subst
    (λ upper →
      targetWeight modeValue * coefficientSquared modeValue
        + targetTailEnergy decay modes
      ≤ upper)
    factorized
    summed

record GalerkinSobolevTailData : Set₁ where
  constructor galerkin-sobolev-tail-data
  field
    decay : ℚ
    modes : List (FourierTailMode decay)

open GalerkinSobolevTailData public

physicalGalerkinTailEstimate :
  (dataSet : GalerkinSobolevTailData) →
  targetTailEnergy (decay dataSet) (modes dataSet)
  ≤ decay dataSet
    * sourceSobolevEnergy (decay dataSet) (modes dataSet)
physicalGalerkinTailEstimate dataSet =
  fourierGalerkinTailBound
    (decay dataSet)
    (modes dataSet)
