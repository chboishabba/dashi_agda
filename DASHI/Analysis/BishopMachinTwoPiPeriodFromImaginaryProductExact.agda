{-# OPTIONS --safe #-}
module DASHI.Analysis.BishopMachinTwoPiPeriodFromImaginaryProductExact where

------------------------------------------------------------------------
-- K05 MAX-CUT: TWO-MACHIN-PI PERIOD OF THE ORIGINAL ROUND11 SERIES.
--
-- This file does NOT assume the classical period of sine or cosine.
-- It uses the actual vendored Bishop sine/cosine limits, their source
-- signed-factorial term identification, and the pi-antiperiodicity
-- already derived from ONE pure-imaginary exponential Cauchy product.
--
-- Independent remaining inputs (not manufactured here):
--   * Round11ImaginaryExpMultiplicative -- native mixed Cauchy theorem
--   * cos_B(theta_M) ≃ sin_B(theta_M) -- arctan/tangent quarter bridge
--
-- Consequently this is a conditional PERIOD theorem, NOT independent
-- pi uniqueness, nor evidence that those two source inputs are closed.
--
-- Attribution: John Machin (1706); Bishop and Bridges (1985);
-- Zachary Murray (2022), Viktor Csimma/bishop; existing DASHI
-- Round11 trig, Bishop setoid congruence, and imaginary-product owners.
-- Source written; an exact Agda kernel check is still required.
------------------------------------------------------------------------

open import Data.Product.Base using (_×_; _,_)
import Real as R
import RealProperties as RP

import DASHI.Foundations.BishopMachinArctanConstructionExact as Machin
import DASHI.Foundations.BishopSineCosineSetoidCongruenceExact as TrigCong
import DASHI.Analysis.BishopMachinQuarterPhaseQuadruplicationAlgebraExact as Quad
import DASHI.Analysis.BishopRound11ImaginaryProductPythagoreanReuseExact as Product
import DASHI.Physics.YangMills.YangMillsSubmissionRound11ExactCutset as Round11

twoMachinPi : R.ℝ
twoMachinPi =
  R._+_ Machin.bishopMachinPi Machin.bishopMachinPi

reassociateTwoPi :
  (x : R.ℝ) →
  R._≃_
    (R._+_ x twoMachinPi)
    (R._+_ (R._+_ x Machin.bishopMachinPi) Machin.bishopMachinPi)
reassociateTwoPi x =
  let open RP.ℝ-Solver
  in solve 2
    (λ z p → (z ⊕ (p ⊕ p)) ⊜ ((z ⊕ p) ⊕ p))
    RP.≃-refl x Machin.bishopMachinPi

doubleNegation : (x : R.ℝ) → R._≃_ (R.-_ (R.-_ x)) x
doubleNegation x =
  let open RP.ℝ-Solver
  in solve 1 (λ z → (⊝ (⊝ z)) ⊜ z)
    RP.≃-refl x

round11SineTwoPiPeriod :
  (inputs : Round11.Round11BishopCutset) →
  (product : Product.Round11ImaginaryExpMultiplicative inputs) →
  R._≃_ (Quad.quarterCos inputs) (Quad.quarterSin inputs) →
  (x : R.ℝ) →
  R._≃_
    (Product.sinB inputs (R._+_ x twoMachinPi))
    (Product.sinB inputs x)
round11SineTwoPiPeriod inputs product quarterEqual x =
  RP.≃-trans
    (TrigCong.bishopSinCongruent
      (Round11.round11ConcreteTermIdentification inputs)
      (reassociateTwoPi x))
    (RP.≃-trans
      (Product.round11SineShiftByMachinPi
        inputs product quarterEqual
        (R._+_ x Machin.bishopMachinPi))
      (RP.≃-trans
        (RP.-‿cong
          (Product.round11SineShiftByMachinPi
            inputs product quarterEqual x))
        (doubleNegation (Product.sinB inputs x))))

round11CosineTwoPiPeriod :
  (inputs : Round11.Round11BishopCutset) →
  (product : Product.Round11ImaginaryExpMultiplicative inputs) →
  R._≃_ (Quad.quarterCos inputs) (Quad.quarterSin inputs) →
  (x : R.ℝ) →
  R._≃_
    (Product.cosB inputs (R._+_ x twoMachinPi))
    (Product.cosB inputs x)
round11CosineTwoPiPeriod inputs product quarterEqual x =
  RP.≃-trans
    (TrigCong.bishopCosCongruent
      (Round11.round11ConcreteTermIdentification inputs)
      (reassociateTwoPi x))
    (RP.≃-trans
      (Product.round11CosineShiftByMachinPi
        inputs product quarterEqual
        (R._+_ x Machin.bishopMachinPi))
      (RP.≃-trans
        (RP.-‿cong
          (Product.round11CosineShiftByMachinPi
            inputs product quarterEqual x))
        (doubleNegation (Product.cosB inputs x))))

-- Both periodicities are for the SAME selected Round11 Bishop data.
-- Neither replaces the independent positive-least-period theorem.
round11TwoPiPeriodPair :
  (inputs : Round11.Round11BishopCutset) →
  (product : Product.Round11ImaginaryExpMultiplicative inputs) →
  (quarterEqual :
    R._≃_ (Quad.quarterCos inputs) (Quad.quarterSin inputs)) →
  (x : R.ℝ) →
  (R._≃_
    (Product.sinB inputs (R._+_ x twoMachinPi))
    (Product.sinB inputs x))
  ×
  (R._≃_
    (Product.cosB inputs (R._+_ x twoMachinPi))
    (Product.cosB inputs x))
round11TwoPiPeriodPair inputs product quarterEqual x =
  round11SineTwoPiPeriod inputs product quarterEqual x
  ,
  round11CosineTwoPiPeriod inputs product quarterEqual x
