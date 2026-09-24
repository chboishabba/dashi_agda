module DASHI.Physics.Closure.NSWholeSpaceR3DirectionalSecondMomentQGainExact where

------------------------------------------------------------------------
-- A / DIRECTIONAL SECOND MOMENT CARRIES ONE OUTPUT q = |xi|^2
--
-- The continuous state-variation route produces directional derivatives.
-- The legitimate source of one low-output q factor is therefore the ordinary
-- R^3 Cauchy identity, not an identification of the centered-resolvent shift
-- with |xi|.
--
-- For xi,v in R^3,
--
--   (xi . v)^2 <= |xi|^2 |v|^2.
--
-- Constructively we prove the exact Lagrange gap identity
--
--   |xi|^2 |v|^2 - (xi.v)^2
--     =
--       (xi_x v_y - xi_y v_x)^2
--     + (xi_x v_z - xi_z v_x)^2
--     + (xi_y v_z - xi_z v_y)^2,
--
-- and obtain the inequality from nonnegativity of squares.
--
-- Thus any physical signed derivative slot which is exactly an output
-- directional contraction automatically supplies the ONE q factor required by
-- NSWholeSpaceR3RadialFactorBudgetExact.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)

import Real as BishopReal
import RealProperties as BishopP

import DASHI.Foundations.BishopSquareNonnegativeExact as SquareNN
import DASHI.Physics.Closure.NSTriadKNEuclideanSignedFrequencyCarrierRealizationExact as Euclidean
import DASHI.Physics.Closure.NSTriadKNEuclideanViscousHeatRateExact as Heat

square : BishopReal.ℝ → BishopReal.ℝ
square x = BishopReal._*_ x x

dot :
  Euclidean.R3Frequency →
  Euclidean.R3Frequency →
  BishopReal.ℝ
dot a b =
  BishopReal._+_
    (BishopReal._*_ (Euclidean.x a) (Euclidean.x b))
    (BishopReal._+_
      (BishopReal._*_ (Euclidean.y a) (Euclidean.y b))
      (BishopReal._*_ (Euclidean.z a) (Euclidean.z b)))

crossXY :
  Euclidean.R3Frequency →
  Euclidean.R3Frequency →
  BishopReal.ℝ
crossXY a b =
  BishopReal._-_
    (BishopReal._*_ (Euclidean.x a) (Euclidean.y b))
    (BishopReal._*_ (Euclidean.y a) (Euclidean.x b))

crossXZ :
  Euclidean.R3Frequency →
  Euclidean.R3Frequency →
  BishopReal.ℝ
crossXZ a b =
  BishopReal._-_
    (BishopReal._*_ (Euclidean.x a) (Euclidean.z b))
    (BishopReal._*_ (Euclidean.z a) (Euclidean.x b))

crossYZ :
  Euclidean.R3Frequency →
  Euclidean.R3Frequency →
  BishopReal.ℝ
crossYZ a b =
  BishopReal._-_
    (BishopReal._*_ (Euclidean.y a) (Euclidean.z b))
    (BishopReal._*_ (Euclidean.z a) (Euclidean.y b))

lagrangeGap :
  Euclidean.R3Frequency →
  Euclidean.R3Frequency →
  BishopReal.ℝ
lagrangeGap a b =
  BishopReal._+_
    (square (crossXY a b))
    (BishopReal._+_
      (square (crossXZ a b))
      (square (crossYZ a b)))

lagrangeIdentity :
  (a b : Euclidean.R3Frequency) →
  BishopReal._≃_
    (BishopReal._-_
      (BishopReal._*_
        (Heat.frequencyNormSquared a)
        (Heat.frequencyNormSquared b))
      (square (dot a b)))
    (lagrangeGap a b)
lagrangeIdentity a b =
  let
    ax = Euclidean.x a
    ay = Euclidean.y a
    az = Euclidean.z a
    bx = Euclidean.x b
    by = Euclidean.y b
    bz = Euclidean.z b
    open BishopP.ℝ-Solver
  in
  solve 6
    (λ ax' ay' az' bx' by' bz' →
      (((ax' ⊗ ax') ⊕ ((ay' ⊗ ay') ⊕ (az' ⊗ az')))
       ⊗
       ((bx' ⊗ bx') ⊕ ((by' ⊗ by') ⊕ (bz' ⊗ bz'))))
      ⊖
      ((ax' ⊗ bx' ⊕ (ay' ⊗ by' ⊕ az' ⊗ bz'))
       ⊗
       (ax' ⊗ bx' ⊕ (ay' ⊗ by' ⊕ az' ⊗ bz')))
      ⊜
      ((ax' ⊗ by' ⊖ ay' ⊗ bx')
       ⊗
       (ax' ⊗ by' ⊖ ay' ⊗ bx'))
      ⊕
      (((ax' ⊗ bz' ⊖ az' ⊗ bx')
        ⊗
        (ax' ⊗ bz' ⊖ az' ⊗ bx'))
       ⊕
       ((ay' ⊗ bz' ⊖ az' ⊗ by')
        ⊗
        (ay' ⊗ bz' ⊖ az' ⊗ by'))))
    BishopP.≃-refl
    ax ay az bx by bz

lagrangeGapNonnegative :
  (a b : Euclidean.R3Frequency) →
  BishopReal.NonNegative (lagrangeGap a b)
lagrangeGapNonnegative a b =
  BishopP.nonNegx,y⇒nonNegx+y
    (SquareNN.bishopSquareNonnegative (crossXY a b))
    (BishopP.nonNegx,y⇒nonNegx+y
      (SquareNN.bishopSquareNonnegative (crossXZ a b))
      (SquareNN.bishopSquareNonnegative (crossYZ a b)))

directionalSquareBelowNormProduct :
  (output derivative : Euclidean.R3Frequency) →
  BishopReal._≤_
    (square (dot output derivative))
    (BishopReal._*_
      (Heat.frequencyNormSquared output)
      (Heat.frequencyNormSquared derivative))
directionalSquareBelowNormProduct output derivative =
  BishopP.0≤y-x⇒x≤y
    (BishopP.≤-respʳ-≃
      (BishopP.≃-symm (lagrangeIdentity output derivative))
      (BishopP.nonNegx⇒0≤x
        (lagrangeGapNonnegative output derivative)))

------------------------------------------------------------------------
-- Physical-slot adapter.
--
-- This deliberately asks only for the SAME-OBJECT identification of the
-- selected signed second-moment scalar with a directional derivative square.
-- Once supplied, the q gain is theorem-derived rather than assumed.
------------------------------------------------------------------------

record DirectionalSecondMomentSlot
    (output : Euclidean.R3Frequency)
    (secondMoment : BishopReal.ℝ) : Set where
  constructor directional-second-moment-slot
  field
    derivativeVector : Euclidean.R3Frequency

    secondMomentIsDirectionalSquare :
      BishopReal._≃_
        secondMoment
        (square (dot output derivativeVector))

open DirectionalSecondMomentSlot public

directionalSlotCarriesOutputQ :
  ∀ {output secondMoment} →
  (slot : DirectionalSecondMomentSlot output secondMoment) →
  BishopReal._≤_
    secondMoment
    (BishopReal._*_
      (Heat.frequencyNormSquared output)
      (Heat.frequencyNormSquared (derivativeVector slot)))
directionalSlotCarriesOutputQ {output} slot =
  BishopP.≤-respˡ-≃
    (secondMomentIsDirectionalSquare slot)
    (directionalSquareBelowNormProduct
      output
      (derivativeVector slot))

directionalSecondMomentQGainClosed : Bool
directionalSecondMomentQGainClosed = true

resolventShiftIdentifiedWithOutputRadius : Bool
resolventShiftIdentifiedWithOutputRadius = false

physicalDerivativeSlotIdentificationClosedHere : Bool
physicalDerivativeSlotIdentificationClosedHere = false

continuousFTCToDirectionalSlotClosedHere : Bool
continuousFTCToDirectionalSlotClosedHere = false

clayPromotion : Bool
clayPromotion = false

directionalSecondMomentQGainClosedIsTrue :
  directionalSecondMomentQGainClosed ≡ true
directionalSecondMomentQGainClosedIsTrue = refl

resolventShiftIdentifiedWithOutputRadiusIsFalse :
  resolventShiftIdentifiedWithOutputRadius ≡ false
resolventShiftIdentifiedWithOutputRadiusIsFalse = refl

clayPromotionIsFalse : clayPromotion ≡ false
