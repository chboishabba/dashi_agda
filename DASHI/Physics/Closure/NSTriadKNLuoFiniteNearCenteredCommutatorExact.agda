module DASHI.Physics.Closure.NSTriadKNLuoFiniteNearCenteredCommutatorExact where

------------------------------------------------------------------------
-- PROVENANCE
--
-- Authors: Peter Constantin; Weinan E; Edriss S. Titi.
-- Title: "Onsager's Conjecture on the Energy Conservation for Solutions of
-- Euler's Equation".
-- Communications in Mathematical Physics 165 (1994), 207--209.
-- DOI: 10.1007/BF02099744.
--
-- Author: Darko Mitrović.
-- Title: "A High-Frequency Tail Condition and a Diagnostic Iteration for
-- the Navier--Stokes Equations".
-- arXiv:2411.02568.
-- DOI: none assigned in the cited preprint version.
--
-- PURPOSE
-- Compose the two independently derived finite gains:
--
--   centered spatial remainder <= secondMoment * curvature,
--   terminal half-kernel mass = 2 * windowRoot.
--
-- The resulting near contribution is bounded by their product.  A second
-- theorem transports a physical moment envelope into the same estimate.  No
-- assumption that the moment envelope follows from energy alone is hidden.
------------------------------------------------------------------------

open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.List using ([]; _∷_)
open import Data.Rational.Base using
  (ℚ; 0ℚ; _*_; _≤_; nonNegative)
import Data.Rational.Properties as ℚₚ
open import Data.Rational.Tactic.RingSolver using (solve)
open import Relation.Binary.PropositionalEquality using (subst)

import DASHI.Physics.Closure.NSTriadKNLuoFiniteNearWindowHalfKernelExact as Window

record NearCenteredCommutatorData : Set where
  constructor near-centered-commutator-data
  field
    windowExponent : Nat
    remainderMagnitude secondMoment curvature : ℚ

    halfKernelNonnegative :
      0ℚ ≤ Window.halfKernelMass windowExponent

    curvatureNonnegative : 0ℚ ≤ curvature

    centeredRemainderBound :
      remainderMagnitude ≤ secondMoment * curvature

open NearCenteredCommutatorData public

nearContribution : NearCenteredCommutatorData → ℚ
nearContribution inputs =
  Window.halfKernelMass (windowExponent inputs)
  * remainderMagnitude inputs

nearCenteredCommutatorBound :
  (inputs : NearCenteredCommutatorData) →
  nearContribution inputs
  ≤ Window.halfKernelMass (windowExponent inputs)
      * secondMoment inputs * curvature inputs
nearCenteredCommutatorBound inputs =
  let
    scaled :
      Window.halfKernelMass (windowExponent inputs)
        * remainderMagnitude inputs
      ≤ Window.halfKernelMass (windowExponent inputs)
        * (secondMoment inputs * curvature inputs)
    scaled =
      let
        instance
          halfKernelIsNonnegative =
            nonNegative (halfKernelNonnegative inputs)
      in
      ℚₚ.*-monoˡ-≤-nonNeg
        (Window.halfKernelMass (windowExponent inputs))
        (centeredRemainderBound inputs)

    targetMeaning :
      Window.halfKernelMass (windowExponent inputs)
        * (secondMoment inputs * curvature inputs)
      ≡ Window.halfKernelMass (windowExponent inputs)
          * secondMoment inputs * curvature inputs
    targetMeaning =
      solve
        ( Window.halfKernelMass (windowExponent inputs)
        ∷ secondMoment inputs
        ∷ curvature inputs
        ∷ []
        )
  in
  subst
    (λ upper → nearContribution inputs ≤ upper)
    targetMeaning
    scaled

nearCenteredWithMomentEnvelope :
  (inputs : NearCenteredCommutatorData) →
  (momentEnvelope : ℚ) →
  secondMoment inputs ≤ momentEnvelope →
  nearContribution inputs
  ≤ Window.halfKernelMass (windowExponent inputs)
      * momentEnvelope * curvature inputs
nearCenteredWithMomentEnvelope inputs momentEnvelope momentBound =
  let
    first = nearCenteredCommutatorBound inputs

    halfScaled :
      Window.halfKernelMass (windowExponent inputs)
        * secondMoment inputs
      ≤ Window.halfKernelMass (windowExponent inputs)
        * momentEnvelope
    halfScaled =
      let
        instance
          halfKernelIsNonnegative =
            nonNegative (halfKernelNonnegative inputs)
      in
      ℚₚ.*-monoˡ-≤-nonNeg
        (Window.halfKernelMass (windowExponent inputs))
        momentBound

    scaledMoment :
      Window.halfKernelMass (windowExponent inputs)
        * secondMoment inputs * curvature inputs
      ≤ Window.halfKernelMass (windowExponent inputs)
        * momentEnvelope * curvature inputs
    scaledMoment =
      let
        instance
          curvatureIsNonnegative =
            nonNegative (curvatureNonnegative inputs)
      in
      ℚₚ.*-monoʳ-≤-nonNeg
        (curvature inputs)
        halfScaled
  in
  ℚₚ.≤-trans first scaledMoment
