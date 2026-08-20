module DASHI.Physics.Closure.NSTriadKNQuarticForcingQuadraticAbsorptionNoGoExact where

------------------------------------------------------------------------
-- PRIMARY SOURCES / CONTEXT
--
-- Author: Jean Leray.
-- Title: "Sur le mouvement d'un liquide visqueux emplissant l'espace".
-- DOI: 10.1007/BF02547354.
--
-- Author: Fabian Waleffe.
-- Title: "The nature of triad interactions in homogeneous turbulence".
-- DOI: 10.1063/1.858309.
--
-- Authors: Alexey Cheskidov; Roman Shvydkoy.
-- Title: "The Regularity of Weak Solutions of the 3D Navier-Stokes Equations
-- in B^{-1}_{infinity,infinity}".
-- DOI: 10.1007/s00205-009-0265-2.
--
-- DASHI MAKE-OR-BREAK HOMOGENEITY FALSIFIER
--
-- The literal projected Galerkin nonlinearity is already proved quadratic in
-- velocity by `NSTriadKNProjectedNonlinearityQuadraticHomogeneityRound94Exact`.
-- The Waleffe network forcing inserts that quadratic vector field into the
-- derivative of a cubic phase, so every direct absolute/Hermitian majorant is
-- quartic in velocity.  The critical dissipation currency is quadratic.
--
-- Frequency gap weights such as L/H or (L/H)^2 are invariant under amplitude
-- scaling u -> a u.  They therefore cannot repair this amplitude mismatch.
-- Algebraically, if
--
--   Q4(a) = a^4,    D2(a) = a^2,
--
-- then any proposed fixed absorption coefficient theta is violated whenever
-- a^2 > theta:
--
--   theta a^2 < a^4.
--
-- Thus Schur/Cauchy/HHolder applied AFTER absolute values, even with the exact
-- HH->low gap factors, cannot by itself give an arbitrary-data estimate
--
--   quartic forcing <= theta * critical dissipation,
--
-- with theta<nu independent of amplitude.  A successful argument must retain
-- additional time/sign dynamics, produce a genuinely higher-order coercive
-- quantity, or find a cancellation before absolute majorisation.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using ([]; _∷_)
open import Data.Rational.Base using
  (ℚ; 0ℚ; _*_; _≤_; _<_; NonNegative; nonNegative; Positive; positive)
import Data.Rational.Properties as ℚP
open import Data.Rational.Tactic.RingSolver using (solve)
open import Relation.Binary.PropositionalEquality using (subst; sym)
open import Relation.Nullary.Negation.Core using (¬_)

import DASHI.Physics.Closure.NSTriadKNProjectedNonlinearityQuadraticHomogeneityRound94Exact as Quadratic

square : ℚ → ℚ
square a = a * a

quarticCost : ℚ → ℚ
quarticCost a = square a * square a

quadraticDissipation : ℚ → ℚ
quadraticDissipation a = square a

quarticCostMeaning :
  (a : ℚ) → quarticCost a ≡ (a * a) * (a * a)
quarticCostMeaning a = refl

quadraticDissipationMeaning :
  (a : ℚ) → quadraticDissipation a ≡ a * a
quadraticDissipationMeaning a = refl

fixedCoefficientFailsAboveItsAmplitudeScale :
  (theta a : ℚ) →
  0ℚ < square a →
  theta < square a →
  ¬ (quarticCost a ≤ theta * quadraticDissipation a)
fixedCoefficientFailsAboveItsAmplitudeScale theta a squarePositive thetaBelowSquare proposed =
  let
    scaledStrict : theta * square a < square a * square a
    scaledStrict =
      let instance squarePos : Positive (square a)
          squarePos = positive squarePositive
      in ℚP.*-monoʳ-<-pos (square a) thetaBelowSquare

    proposedNormalized : square a * square a ≤ theta * square a
    proposedNormalized = proposed
  in
  ℚP.<-irrefl (square a * square a)
    (ℚP.<-≤-trans scaledStrict proposedNormalized)

-- Multiplying a frequency-only gap coefficient changes the constant but not
-- the amplitude degree.  Once the weighted base quartic is nonzero, the same
-- obstruction occurs after rescaling; this scalar theorem records the exact
-- degree mismatch used by the physical audit.
weightedQuarticCost : ℚ → ℚ → ℚ
weightedQuarticCost gapWeight a = gapWeight * quarticCost a

weightedQuarticStillDegreeFour :
  (gapWeight a : ℚ) →
  weightedQuarticCost gapWeight a
  ≡ gapWeight * ((a * a) * (a * a))
weightedQuarticStillDegreeFour gapWeight a = refl

literalProjectedNonlinearityQuadraticScalingAvailable : Bool
literalProjectedNonlinearityQuadraticScalingAvailable =
  Quadratic.round94LiteralProjectedNonlinearityQuadraticHomogeneityClosed

directGapWeightedQuarticSchurCanSupplyFixedQuadraticAbsorption : Bool
directGapWeightedQuarticSchurCanSupplyFixedQuadraticAbsorption = false

amplitudeHomogeneityObstructionClosed : Bool
amplitudeHomogeneityObstructionClosed = true

literalProjectedNonlinearityQuadraticScalingAvailableIsTrue :
  literalProjectedNonlinearityQuadraticScalingAvailable ≡ true
literalProjectedNonlinearityQuadraticScalingAvailableIsTrue = refl

directGapWeightedQuarticSchurCanSupplyFixedQuadraticAbsorptionIsFalse :
  directGapWeightedQuarticSchurCanSupplyFixedQuadraticAbsorption ≡ false
directGapWeightedQuarticSchurCanSupplyFixedQuadraticAbsorptionIsFalse = refl

amplitudeHomogeneityObstructionClosedIsTrue :
  amplitudeHomogeneityObstructionClosed ≡ true
amplitudeHomogeneityObstructionClosedIsTrue = refl
