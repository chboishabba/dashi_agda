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
-- The literal projected Galerkin nonlinearity is quadratic in velocity and
-- the literal Waleffe network-forcing functional is quartic after inserting
-- that forcing into the derivative of a cubic phase.  Critical dissipation is
-- quadratic.  Frequency gap weights are invariant under u -> a u and hence
-- cannot repair this amplitude-degree mismatch.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Rational.Base using
  (ℚ; 0ℚ; _*_; _≤_; _<_; Positive; positive)
import Data.Rational.Properties as ℚP
open import Relation.Nullary.Negation.Core using (¬_)

import DASHI.Physics.Closure.NSTriadKNProjectedNonlinearityQuadraticHomogeneityRound94Exact as Quadratic
import DASHI.Physics.Closure.NSTriadKNWaleffeNetworkForcingRealQuarticHomogeneityExact as Quartic

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
  ℚP.<-irrefl (theta * square a)
    (ℚP.<-≤-trans scaledStrict proposedNormalized)

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

literalNetworkForcingQuarticScalingAvailable : Bool
literalNetworkForcingQuarticScalingAvailable =
  Quartic.round106LiteralWaleffeNetworkForcingRealQuarticHomogeneityClosed

directGapWeightedQuarticSchurCanSupplyFixedQuadraticAbsorption : Bool
directGapWeightedQuarticSchurCanSupplyFixedQuadraticAbsorption = false

amplitudeHomogeneityObstructionClosed : Bool
amplitudeHomogeneityObstructionClosed = true

literalProjectedNonlinearityQuadraticScalingAvailableIsTrue :
  literalProjectedNonlinearityQuadraticScalingAvailable ≡ true
literalProjectedNonlinearityQuadraticScalingAvailableIsTrue = refl

literalNetworkForcingQuarticScalingAvailableIsTrue :
  literalNetworkForcingQuarticScalingAvailable ≡ true
literalNetworkForcingQuarticScalingAvailableIsTrue = refl

directGapWeightedQuarticSchurCanSupplyFixedQuadraticAbsorptionIsFalse :
  directGapWeightedQuarticSchurCanSupplyFixedQuadraticAbsorption ≡ false
directGapWeightedQuarticSchurCanSupplyFixedQuadraticAbsorptionIsFalse = refl

amplitudeHomogeneityObstructionClosedIsTrue :
  amplitudeHomogeneityObstructionClosed ≡ true
amplitudeHomogeneityObstructionClosedIsTrue = refl
