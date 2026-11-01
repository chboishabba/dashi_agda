module DASHI.Physics.Closure.NSTriadKNLowMinorityLiteralGapPhaseWeightRound106Exact where

------------------------------------------------------------------------
-- PRIMARY SOURCES / CONTEXT
--
-- Author: Fabian Waleffe.
-- Title: "The nature of triad interactions in homogeneous turbulence".
-- DOI: 10.1063/1.858309.
--
-- Authors: Hajer Bahouri; Jean-Yves Chemin; Raphael Danchin.
-- Title: "Fourier Analysis and Nonlinear Partial Differential Equations".
-- DOI: 10.1007/978-3-642-16830-7.
--
-- ROUND106 / LITERAL LOW-MINORITY GAP WELD
--
-- For the minority-k mixed-helicity orientation with q>=p, Round102/105 gives
-- the literal critical coefficient
--
--   c_k = 2 k (q-p),
--
-- and the resonant reverse triangle gives c_k <= 2 k^2.  If the low/high
-- shell relation is k <= g p and the phase damping scale is
--
--   S = k^2+p^2+q^2,
--
-- then p^2 <= S and therefore
--
--   c_k <= 2 g^2 S.
--
-- This is the source-native low-minority instantiation of Round106's generic
-- relative phase theorem.  Thus every low-minority HH->low adverse episode
-- carries TWO gap powers before the signed forcing sum is assembled.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Rational.Base using
  (ℚ; 0ℚ; _+_; _-_; _*_; _≤_; NonNegative; nonNegative)
import Data.Rational.Properties as ℚP
open import Data.Rational.Tactic.RingSolver using (solve)
open import Relation.Binary.PropositionalEquality using (subst)

import DASHI.Physics.Closure.NSTriadKNHeterochiralReverseTriangleRound105Exact as Triangle
import DASHI.Physics.Closure.NSTriadKNHeterochiralGapRelativeDampingRound106Exact as Gap

two : ℚ
two = Gap.two

square : ℚ → ℚ
square x = x * x

record LowMinorityKGapDatum : Set where
  constructor low-minority-k-gap-datum
  field
    radii : Triangle.TriangleRadii
    gap : ℚ
    gapNonnegative : 0ℚ ≤ gap
    majorityDifferenceNonnegative :
      0ℚ ≤ Triangle.radiusQ radii - Triangle.radiusP radii
    lowBelowGapHighP :
      Triangle.radiusK radii ≤ gap * Triangle.radiusP radii

open LowMinorityKGapDatum public

lowMinorityKCoefficient : LowMinorityKGapDatum → ℚ
lowMinorityKCoefficient D =
  two * Triangle.radiusK (radii D)
    * (Triangle.radiusQ (radii D) - Triangle.radiusP (radii D))

phaseDampingScale : LowMinorityKGapDatum → ℚ
phaseDampingScale D =
    square (Triangle.radiusK (radii D))
  + square (Triangle.radiusP (radii D))
  + square (Triangle.radiusQ (radii D))

squareNonnegative : ∀ x → 0ℚ ≤ x → 0ℚ ≤ square x
squareNonnegative x xNN =
  let instance xNNI = nonNegative xNN
  in ℚP.nonNegative⁻¹ (x * x)

pSquaredBelowDampingScale :
  (D : LowMinorityKGapDatum) →
  square (Triangle.radiusP (radii D)) ≤ phaseDampingScale D
pSquaredBelowDampingScale D =
  let
    T = radii D
    k2NN = squareNonnegative
      (Triangle.radiusK T) (Triangle.radiusKNonnegative T)
    q2NN = squareNonnegative
      (Triangle.radiusQ T) (Triangle.radiusQNonnegative T)
    p2 = square (Triangle.radiusP T)

    addK : p2 ≤ square (Triangle.radiusK T) + p2
    addK =
      subst
        (λ left → p2 ≤ left + p2)
        (solve (p2 ∷ []))
        (ℚP.+-mono-≤ k2NN ℚP.≤-refl)

    addQ :
      square (Triangle.radiusK T) + p2
      ≤ square (Triangle.radiusK T) + p2 + square (Triangle.radiusQ T)
    addQ =
      subst
        (λ left →
          square (Triangle.radiusK T) + p2
          ≤ left + square (Triangle.radiusQ T))
        (solve (Triangle.radiusK T ∷ p2 ∷ []))
        (ℚP.+-mono-≤ ℚP.≤-refl q2NN)
  in
  ℚP.≤-trans addK addQ

lowMinorityGapGeometry :
  (D : LowMinorityKGapDatum) → Gap.GapDampingGeometry
lowMinorityGapGeometry D = record
  { Gap.low = Triangle.radiusK (radii D)
  ; Gap.high = Triangle.radiusP (radii D)
  ; Gap.gap = gap D
  ; Gap.dampingScale = phaseDampingScale D
  ; Gap.lowNonnegative = Triangle.radiusKNonnegative (radii D)
  ; Gap.highNonnegative = Triangle.radiusPNonnegative (radii D)
  ; Gap.gapNonnegative = gapNonnegative D
  ; Gap.dampingScaleNonnegative =
      let
        T = radii D
        k2NN = squareNonnegative (Triangle.radiusK T) (Triangle.radiusKNonnegative T)
        p2NN = squareNonnegative (Triangle.radiusP T) (Triangle.radiusPNonnegative T)
        q2NN = squareNonnegative (Triangle.radiusQ T) (Triangle.radiusQNonnegative T)
      in ℚP.+-mono-≤ (ℚP.+-mono-≤ k2NN p2NN) q2NN
  ; Gap.lowBelowGapHigh = lowBelowGapHighP D
  ; Gap.highSquaredBelowDamping = pSquaredBelowDampingScale D
  }

lowMinorityCoefficientBelowTwoLowSquared :
  (D : LowMinorityKGapDatum) →
  lowMinorityKCoefficient D
  ≤ two * square (Triangle.radiusK (radii D))
lowMinorityCoefficientBelowTwoLowSquared D =
  let
    base = Triangle.minorityKOrientedCoefficientBelowTwoKSquared
      (radii D) (majorityDifferenceNonnegative D)
    endpoint :
      two * Triangle.radiusK (radii D) * Triangle.radiusK (radii D)
      ≡ two * square (Triangle.radiusK (radii D))
    endpoint = solve (Triangle.radiusK (radii D) ∷ [])
  in
  subst
    (λ upper → lowMinorityKCoefficient D ≤ upper)
    endpoint base

literalLowMinorityCoefficientHasSquaredGap :
  (D : LowMinorityKGapDatum) →
  lowMinorityKCoefficient D
  ≤ (two * (gap D * gap D)) * phaseDampingScale D
literalLowMinorityCoefficientHasSquaredGap D =
  Gap.lowMinorityCoefficientHasSquaredGap
    (lowMinorityGapGeometry D)
    (lowMinorityKCoefficient D)
    (lowMinorityCoefficientBelowTwoLowSquared D)

round106LiteralLowMinoritySquaredGapPhaseWeightClosed : Bool
round106LiteralLowMinoritySquaredGapPhaseWeightClosed = true

round106LiteralLowMinoritySquaredGapPhaseWeightClosedIsTrue :
  round106LiteralLowMinoritySquaredGapPhaseWeightClosed ≡ true
round106LiteralLowMinoritySquaredGapPhaseWeightClosedIsTrue = refl
