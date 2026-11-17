{-# OPTIONS --safe #-}
module DASHI.Analysis.BishopMachinPiComplementReflectionFromImaginaryProductExact where

------------------------------------------------------------------------
-- K05-PI: SAME-SOURCE MACHIN COMPLEMENT REFLECTION.
--
-- This file is NOT a new pi or an assumed classical trigonometric law.
-- The actual Round11 Bishop sine/cosine have source-verified odd/even
-- parity, and the original imaginary Cauchy product + quarter-angle
-- equality already produce the pi_M anti-periodicity.
--
-- Therefore, without any added sign, differentiation, or positivity
-- hypothesis, the same original source series satisfy
--
--   sin_B(pi_M - x) ~=  sin_B(x),
--   cos_B(pi_M - x) ~= -cos_B(x).
--
-- The only remaining mathematical input is exactly the original
-- imaginary Cauchy product and quarter-angle law, not a new extra
-- semantic identity. This removes the need to independently prove a
-- reflection law while extending local first-quadrant sine positivity
-- to the full (0,pi_M) branch.
--
-- Source: Bishop/Bridges, Murray, Csimma, Machin (1706);
-- implementation reuses DASHI Round11 term parity/limit and
-- BishopRound11ImaginaryProductPythagoreanReuseExact.
--
-- Source-written, not yet Agda-kernel receipted.
------------------------------------------------------------------------

import Real as R
import RealProperties as RP

import DASHI.Foundations.BishopMachinArctanConstructionExact as Machin
import DASHI.Foundations.BishopSineCosineSetoidCongruenceExact as TrigCong
import DASHI.Analysis.BishopMachinQuarterPhaseQuadruplicationAlgebraExact as Quad
import DASHI.Analysis.BishopRound11ImaginaryProductPythagoreanReuseExact as Product
import DASHI.Physics.YangMills.BalabanBishopSeriesParityAndLimitExact as Parity
import DASHI.Physics.YangMills.YangMillsSubmissionRound11ExactCutset as Round11

machinComplement : R.ℝ → R.ℝ
machinComplement x = R._-_ Machin.bishopMachinPi x

machinComplementAsNegativePlusPi :
  (x : R.ℝ) →
  R._≃_
    (machinComplement x)
    (R._+_ (R.-_ x) Machin.bishopMachinPi)
machinComplementAsNegativePlusPi x =
  let open RP.ℝ-Solver
  in solve 2
    (λ p z → (p ⊖ z) ⊜ ((⊝ z) ⊕ p))
    RP.≃-refl Machin.bishopMachinPi x

machinComplementInvolutive :
  (x : R.ℝ) →
  R._≃_ (machinComplement (machinComplement x)) x
machinComplementInvolutive x =
  let open RP.ℝ-Solver
  in solve 2
    (λ p z → p ⊖ (p ⊖ z) ⊜ z)
    RP.≃-refl Machin.bishopMachinPi x

round11SineMachinComplement :
  (inputs : Round11.Round11BishopCutset) →
  (product : Product.Round11ImaginaryExpMultiplicative inputs) →
  R._≃_ (Quad.quarterCos inputs) (Quad.quarterSin inputs) →
  (x : R.ℝ) →
  R._≃_
    (Product.sinB inputs (machinComplement x))
    (Product.sinB inputs x)
round11SineMachinComplement inputs product quarterEqual x =
  RP.≃-trans
    (TrigCong.bishopSinCongruent
      (Round11.round11ConcreteTermIdentification inputs)
      (machinComplementAsNegativePlusPi x))
    (RP.≃-trans
      (Product.round11SineShiftByMachinPi
        inputs product quarterEqual (R.-_ x))
      (RP.≃-trans
        (RP.-‿cong
          (Parity.bishopSinNeg
            (Round11.round11ParityInputs inputs) x))
        (RP.neg-involutive (Product.sinB inputs x))))

round11CosineMachinComplement :
  (inputs : Round11.Round11BishopCutset) →
  (product : Product.Round11ImaginaryExpMultiplicative inputs) →
  R._≃_ (Quad.quarterCos inputs) (Quad.quarterSin inputs) →
  (x : R.ℝ) →
  R._≃_
    (Product.cosB inputs (machinComplement x))
    (R.-_ (Product.cosB inputs x))
round11CosineMachinComplement inputs product quarterEqual x =
  RP.≃-trans
    (TrigCong.bishopCosCongruent
      (Round11.round11ConcreteTermIdentification inputs)
      (machinComplementAsNegativePlusPi x))
    (RP.≃-trans
      (Product.round11CosineShiftByMachinPi
        inputs product quarterEqual (R.-_ x))
      (RP.-‿cong
        (Parity.bishopCosNeg
          (Round11.round11ParityInputs inputs) x)))
