module DASHI.Physics.Closure.NSTriadKNHeterochiralPhaseDampingPaymentRound105Exact where

------------------------------------------------------------------------
-- PRIMARY SOURCES / CONTEXT
--
-- Author: Fabian Waleffe.
-- Title: "The nature of triad interactions in homogeneous turbulence".
-- Physics of Fluids A 4 (1992), 350--363.
-- DOI: 10.1063/1.858309.
--
-- Authors: J. M. Manley; H. E. Rowe.
-- Title: "Some General Properties of Nonlinear Elements-Part I. General
-- Energy Relations".
-- Proceedings of the IRE 44(7) (1956), 904--913.
-- DOI: 10.1109/JRPROC.1956.275145.
--
-- ROUND105 / DIRECT PHASE-DAMPING PAYMENT
--
-- Round102 gives, for the minority-k mixed-helicity orientation,
--
--   P = 2 r_k (r_q-r_p) A.
--
-- Round105 reverse triangle gives r_q-r_p <= r_k.  The literal Waleffe
-- amplitude tangent from Round94 has viscous damping rate
--
--   gamma = nu (r_k^2+r_p^2+r_q^2).
--
-- Therefore on the adverse orientation A>=0, r_q-r_p>=0,
--
--   nu P <= 2 gamma A.
--
-- This is the key dimensional comparison needed to turn the scalar
-- damped-forced amplitude equation into a payment for critical production.
-- It bypasses the generic Round96 D*X excess currency on this literal Waleffe
-- channel.  The cyclic minority-p and minority-q statements are identical.
--
-- No division by viscosity is introduced: the theorem keeps the robust form
-- `nu * production <= 2 * dampingRate * amplitude`.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using ([]; _∷_)
import Data.Integer.Base as Int
open import Data.Rational.Base using
  (ℚ; 0ℚ; _+_; _-_; _*_; _≤_; NonNegative; nonNegative)
import Data.Rational.Properties as ℚP
open import Data.Rational.Tactic.RingSolver using (solve)
open import Relation.Binary.PropositionalEquality using (subst)

import DASHI.Physics.Closure.NSTriadKNHeterochiralReverseTriangleRound105Exact as Triangle

two : ℚ
two = Int.+ 2 / 1

twoNonnegative : 0ℚ ≤ two
twoNonnegative = ℚP.<⇒≤ (ℚP.positive⁻¹ two)

square : ℚ → ℚ
square x = x * x

record AdverseMinorityKPhaseDatum : Set where
  constructor adverse-minority-k-phase-datum
  field
    radii : Triangle.TriangleRadii
    viscosity amplitude : ℚ
    viscosityNonnegative : 0ℚ ≤ viscosity
    amplitudeNonnegative : 0ℚ ≤ amplitude
    majorityDifferenceNonnegative :
      0ℚ ≤ Triangle.radiusQ radii - Triangle.radiusP radii

open AdverseMinorityKPhaseDatum public

minorityKCriticalProduction : AdverseMinorityKPhaseDatum → ℚ
minorityKCriticalProduction d =
  two * Triangle.radiusK (radii d)
    * (Triangle.radiusQ (radii d) - Triangle.radiusP (radii d))
    * amplitude d

phaseDampingRate : AdverseMinorityKPhaseDatum → ℚ
phaseDampingRate d =
  viscosity d *
    ( square (Triangle.radiusK (radii d))
    + square (Triangle.radiusP (radii d))
    + square (Triangle.radiusQ (radii d)))

minoritySquareBelowRadiusSquareSum :
  (T : Triangle.TriangleRadii) →
  square (Triangle.radiusK T)
  ≤ square (Triangle.radiusK T)
      + square (Triangle.radiusP T)
      + square (Triangle.radiusQ T)
minoritySquareBelowRadiusSquareSum T =
  let
    pSquareNN : 0ℚ ≤ square (Triangle.radiusP T)
    pSquareNN =
      let instance pNN = nonNegative (Triangle.radiusPNonnegative T)
      in ℚP.nonNegative⁻¹ (square (Triangle.radiusP T))

    qSquareNN : 0ℚ ≤ square (Triangle.radiusQ T)
    qSquareNN =
      let instance qNN = nonNegative (Triangle.radiusQNonnegative T)
      in ℚP.nonNegative⁻¹ (square (Triangle.radiusQ T))

    addP :
      square (Triangle.radiusK T)
      ≤ square (Triangle.radiusK T) + square (Triangle.radiusP T)
    addP =
      subst
        (λ left → left ≤
          square (Triangle.radiusK T) + square (Triangle.radiusP T))
        (ℚP.+-identityʳ (square (Triangle.radiusK T)))
        (ℚP.+-monoʳ-≤ (square (Triangle.radiusK T)) pSquareNN)

    addQ :
      square (Triangle.radiusK T) + square (Triangle.radiusP T)
      ≤ square (Triangle.radiusK T) + square (Triangle.radiusP T)
        + square (Triangle.radiusQ T)
    addQ =
      subst
        (λ left → left ≤
          square (Triangle.radiusK T) + square (Triangle.radiusP T)
            + square (Triangle.radiusQ T))
        (ℚP.+-identityʳ
          (square (Triangle.radiusK T) + square (Triangle.radiusP T)))
        (ℚP.+-monoʳ-≤
          (square (Triangle.radiusK T) + square (Triangle.radiusP T))
          qSquareNN)
  in
  ℚP.≤-trans addP addQ

viscosityTimesMinorityCoefficientBelowTwoDampingRate :
  (d : AdverseMinorityKPhaseDatum) →
  viscosity d
    * (two * Triangle.radiusK (radii d)
      * (Triangle.radiusQ (radii d) - Triangle.radiusP (radii d)))
  ≤ two * phaseDampingRate d
viscosityTimesMinorityCoefficientBelowTwoDampingRate d =
  let
    T = radii d
    k = Triangle.radiusK T
    p = Triangle.radiusP T
    q = Triangle.radiusQ T
    nu = viscosity d
    diff = q - p

    coefficientBound : two * k * diff ≤ two * k * k
    coefficientBound =
      Triangle.minorityKOrientedCoefficientBelowTwoKSquared
        T (majorityDifferenceNonnegative d)

    nuScaled : nu * (two * k * diff) ≤ nu * (two * k * k)
    nuScaled =
      let instance nuNN = nonNegative (viscosityNonnegative d)
      in ℚP.*-monoˡ-≤-nonNeg nu coefficientBound

    radiusSumBound : k * k ≤ k * k + p * p + q * q
    radiusSumBound = minoritySquareBelowRadiusSquareSum T

    twoNuNN : 0ℚ ≤ two * nu
    twoNuNN =
      let
        instance twoNN = nonNegative twoNonnegative
        instance nuNN = nonNegative (viscosityNonnegative d)
      in ℚP.nonNegative⁻¹ (two * nu)

    scaledRadius : (two * nu) * (k * k)
      ≤ (two * nu) * (k * k + p * p + q * q)
    scaledRadius =
      let instance factorNN = nonNegative twoNuNN
      in ℚP.*-monoˡ-≤-nonNeg (two * nu) radiusSumBound

    leftMeaning : nu * (two * k * k) ≡ (two * nu) * (k * k)
    leftMeaning = solve (nu ∷ k ∷ [])

    rightMeaning :
      (two * nu) * (k * k + p * p + q * q)
      ≡ two * phaseDampingRate d
    rightMeaning = solve (nu ∷ k ∷ p ∷ q ∷ [])
  in
  ℚP.≤-trans nuScaled
    (subst
      (λ left → left ≤ two * phaseDampingRate d)
      (sym leftMeaning)
      (subst
        (λ right → (two * nu) * (k * k) ≤ right)
        rightMeaning scaledRadius))

viscosityTimesAdverseMinorityKProductionBelowTwoDampingAmplitude :
  (d : AdverseMinorityKPhaseDatum) →
  viscosity d * minorityKCriticalProduction d
  ≤ two * phaseDampingRate d * amplitude d
viscosityTimesAdverseMinorityKProductionBelowTwoDampingAmplitude d =
  let
    coefficient =
      two * Triangle.radiusK (radii d)
        * (Triangle.radiusQ (radii d) - Triangle.radiusP (radii d))
    coefficientBound =
      viscosityTimesMinorityCoefficientBelowTwoDampingRate d
    scaled =
      let instance aNN = nonNegative (amplitudeNonnegative d)
      in ℚP.*-monoʳ-≤-nonNeg (amplitude d) coefficientBound

    leftMeaning :
      (viscosity d * coefficient) * amplitude d
      ≡ viscosity d * minorityKCriticalProduction d
    leftMeaning = solve
      ( viscosity d ∷ coefficient ∷ amplitude d
      ∷ Triangle.radiusK (radii d)
      ∷ Triangle.radiusP (radii d)
      ∷ Triangle.radiusQ (radii d) ∷ [])

    rightMeaning :
      (two * phaseDampingRate d) * amplitude d
      ≡ two * phaseDampingRate d * amplitude d
    rightMeaning = refl
  in
  subst
    (λ left → left ≤ two * phaseDampingRate d * amplitude d)
    leftMeaning
    (subst
      (λ right → (viscosity d * coefficient) * amplitude d ≤ right)
      rightMeaning scaled)

round105AdverseHeterochiralProductionPaidByPhaseDampingPointwise : Bool
round105AdverseHeterochiralProductionPaidByPhaseDampingPointwise = true

round105GenericDXCurrencyRequiredOnLiteralWaleffeCell : Bool
round105GenericDXCurrencyRequiredOnLiteralWaleffeCell = false

round105AdverseHeterochiralProductionPaidByPhaseDampingPointwiseIsTrue :
  round105AdverseHeterochiralProductionPaidByPhaseDampingPointwise ≡ true
round105AdverseHeterochiralProductionPaidByPhaseDampingPointwiseIsTrue = refl

round105GenericDXCurrencyRequiredOnLiteralWaleffeCellIsFalse :
  round105GenericDXCurrencyRequiredOnLiteralWaleffeCell ≡ false
round105GenericDXCurrencyRequiredOnLiteralWaleffeCellIsFalse = refl
