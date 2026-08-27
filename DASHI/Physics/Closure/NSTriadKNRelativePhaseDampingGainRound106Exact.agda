module DASHI.Physics.Closure.NSTriadKNRelativePhaseDampingGainRound106Exact where

------------------------------------------------------------------------
-- PRIMARY SOURCES / CONTEXT
--
-- Author: Fabian Waleffe.
-- Title: "The nature of triad interactions in homogeneous turbulence".
-- Physics of Fluids A 4 (1992), 350--363.
-- DOI: 10.1063/1.858309.
--
-- Authors: Hajer Bahouri; Jean-Yves Chemin; Raphael Danchin.
-- Title: "Fourier Analysis and Nonlinear Partial Differential Equations".
-- Springer, 2011.
-- DOI: 10.1007/978-3-642-16830-7.
--
-- ROUND106 / DO NOT THROW AWAY THE LOW/HIGH GAIN
--
-- Round105 used the safe comparison
--
--   coefficient <= 2 * (r_k^2+r_p^2+r_q^2)
--
-- and therefore paid every adverse phase cell with the same constant 2.  That
-- is correct but too lossy for the complete network: in HH->low geometry the
-- Waleffe/minority coefficient carries one or two powers of the low/high gap.
-- Those powers must survive the time integration BEFORE any fibre summation.
--
-- This file isolates the exact division-free algebra.  If
--
--   c <= g S,       c,A,g,nu,S >= 0,
--
-- then
--
--   nu (c A) <= g (nu S A).
--
-- Thus, if the positive-part amplitude equation supplies
--
--   A_+(T) + integral nu S A_+
--      <= A_+(0) + integral F_+,
--
-- the integrated production obeys
--
--   nu integral P
--      <= g A_+(0) + g integral F_+.
--
-- No division by nu or S is used.  Consequently a dyadic g=2^-d or 2^-2d
-- can be carried literally into the final network-forcing sum.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Rational.Base using
  (ℚ; 0ℚ; _+_; _*_; _≤_; NonNegative; nonNegative)
import Data.Rational.Properties as ℚP
open import Data.Rational.Tactic.RingSolver using (solve)
open import Relation.Binary.PropositionalEquality using (subst)

record RelativePhaseCoefficient : Set where
  constructor relative-phase-coefficient
  field
    coefficient dampingScale gain viscosity amplitude : ℚ
    coefficientNonnegative : 0ℚ ≤ coefficient
    dampingScaleNonnegative : 0ℚ ≤ dampingScale
    gainNonnegative : 0ℚ ≤ gain
    viscosityNonnegative : 0ℚ ≤ viscosity
    amplitudeNonnegative : 0ℚ ≤ amplitude
    coefficientBelowGainTimesDamping :
      coefficient ≤ gain * dampingScale

open RelativePhaseCoefficient public

relativePointwisePhasePayment :
  (R : RelativePhaseCoefficient) →
  viscosity R * (coefficient R * amplitude R)
  ≤ gain R * ((viscosity R * dampingScale R) * amplitude R)
relativePointwisePhasePayment R =
  let
    nu = viscosity R
    c = coefficient R
    a = amplitude R
    g = gain R
    s = dampingScale R

    nuScaled : nu * c ≤ nu * (g * s)
    nuScaled =
      let instance nuNN = nonNegative (viscosityNonnegative R)
      in ℚP.*-monoˡ-≤-nonNeg nu (coefficientBelowGainTimesDamping R)

    amplitudeScaled : (nu * c) * a ≤ (nu * (g * s)) * a
    amplitudeScaled =
      let instance aNN = nonNegative (amplitudeNonnegative R)
      in ℚP.*-monoʳ-≤-nonNeg a nuScaled

    leftMeaning : (nu * c) * a ≡ nu * (c * a)
    leftMeaning = solve (nu ∷ c ∷ a ∷ [])

    rightMeaning :
      (nu * (g * s)) * a ≡ g * ((nu * s) * a)
    rightMeaning = solve (nu ∷ g ∷ s ∷ a ∷ [])
  in
  subst
    (λ left → left ≤ g * ((nu * s) * a))
    leftMeaning
    (subst
      (λ right → (nu * c) * a ≤ right)
      rightMeaning amplitudeScaled)

record IntegratedRelativePhasePayment : Set where
  constructor integrated-relative-phase-payment
  field
    viscosity gain integratedProduction dampingArea : ℚ
    initialPositiveAmplitude terminalPositiveAmplitude positiveForcing : ℚ

    gainNonnegative : 0ℚ ≤ gain
    terminalPositiveAmplitudeNonnegative : 0ℚ ≤ terminalPositiveAmplitude

    -- This is the integrated pointwise comparison after preserving the local
    -- gap gain.  For a fixed shell/gap class, gain is constant over the fold.
    productionBelowGainTimesDamping :
      viscosity * integratedProduction ≤ gain * dampingArea

    positiveAmplitudeBalance :
      terminalPositiveAmplitude + dampingArea
      ≤ initialPositiveAmplitude + positiveForcing

open IntegratedRelativePhasePayment public

integratedRelativePhasePayment :
  (R : IntegratedRelativePhasePayment) →
  viscosity R * integratedProduction R
  ≤ gain R * initialPositiveAmplitude R
      + gain R * positiveForcing R
integratedRelativePhasePayment R =
  let
    g = gain R
    d = dampingArea R
    a0 = initialPositiveAmplitude R
    aT = terminalPositiveAmplitude R
    f = positiveForcing R

    dampingBelowEndpoints : d ≤ a0 + f
    dampingBelowEndpoints =
      let
        addTerminal : 0ℚ + d ≤ aT + d
        addTerminal =
          ℚP.+-mono-≤
            (terminalPositiveAmplitudeNonnegative R)
            ℚP.≤-refl

        dropZero : d ≤ aT + d
        dropZero =
          subst
            (λ left → left ≤ aT + d)
            (solve (d ∷ []))
            addTerminal
      in
      ℚP.≤-trans dropZero (positiveAmplitudeBalance R)

    scaled : g * d ≤ g * (a0 + f)
    scaled =
      let instance gNN = nonNegative (gainNonnegative R)
      in ℚP.*-monoˡ-≤-nonNeg g dampingBelowEndpoints

    endpoint : g * (a0 + f) ≡ g * a0 + g * f
    endpoint = solve (g ∷ a0 ∷ f ∷ [])
  in
  ℚP.≤-trans
    (productionBelowGainTimesDamping R)
    (subst (λ upper → g * d ≤ upper) endpoint scaled)

round106RelativePhaseDampingGainPreserved : Bool
round106RelativePhaseDampingGainPreserved = true

round106GapGainMayBeCarriedBeforeNetworkSummation : Bool
round106GapGainMayBeCarriedBeforeNetworkSummation = true

round106RelativePhaseDampingGainPreservedIsTrue :
  round106RelativePhaseDampingGainPreserved ≡ true
round106RelativePhaseDampingGainPreservedIsTrue = refl

round106GapGainMayBeCarriedBeforeNetworkSummationIsTrue :
  round106GapGainMayBeCarriedBeforeNetworkSummation ≡ true
round106GapGainMayBeCarriedBeforeNetworkSummationIsTrue = refl
