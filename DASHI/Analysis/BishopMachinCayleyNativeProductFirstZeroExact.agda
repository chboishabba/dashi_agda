{-# OPTIONS --safe #-}
module DASHI.Analysis.BishopMachinCayleyNativeProductFirstZeroExact where

------------------------------------------------------------------------
-- K05-PRODUCT + K05-PI: NO ABSTRACT PRODUCT ASSUMPTION AT THE END.
--
-- The ORIGINAL Round11 mixed signed-factorial theorem has already been
-- source-written in BishopRound11SignedFactorialDegreeBinomialExact:
--   originalImaginaryExponentialMultiplicative inputs x y
-- directly provides exp(ix)*exp(iy) ~= exp(i(x+y)).
--
-- The original consumer uses the reverse orientation, so the entire
-- alleged "remaining product premise" is paid by one setoid symmetry.
-- The selected Cayley-to-first-zero theorem can then discharge the
-- first positive sine zero from ONLY its actual original Bishop
-- arctangent-to-Cayley phase evaluation.
--
-- IMPORTANT: kernel acceptance of this entire imported chain is not
-- established by writing this file. No postulates/holes, no second
-- complex carrier, and no artificial source-specific product axiom.
------------------------------------------------------------------------

import Real as R

import DASHI.Analysis.BishopSetoidComplexExact as C
import DASHI.Analysis.BishopRound11ImaginaryProductPythagoreanReuseExact as Product
import DASHI.Foundations.BishopRound11SignedFactorialDegreeBinomialExact as Signed
import DASHI.Analysis.BishopMachinCayleyHalfPhaseToFirstZeroExact as Cayley
import DASHI.Analysis.BishopMachinFirstPositiveSineZeroFromNativePhaseExact as First
import DASHI.Physics.YangMills.YangMillsSubmissionRound11ExactCutset as Round11

originalNativeImaginaryExpProduct :
  (inputs : Round11.Round11BishopCutset) →
  Product.Round11ImaginaryExpMultiplicative inputs
originalNativeImaginaryExpProduct inputs x y =
  C.≈C-sym
    (Signed.originalImaginaryExponentialMultiplicative
      inputs x y)

-- No additional global sign, Pythagorean, quarter-angle, double-angle,
-- complex product or first-zero assumptions.
originalNativeFirstPositiveSineZeroFromCayley :
  (inputs : Round11.Round11BishopCutset) →
  Cayley.OriginalMachinCayleySameObjectEvaluation inputs →
  First.SourceMachinFirstPositiveSineZero inputs
originalNativeFirstPositiveSineZeroFromCayley inputs cayleyEvaluation =
  Cayley.sourceMachinFirstPositiveZeroFromSameObjectCayley
    inputs
    (originalNativeImaginaryExpProduct inputs)
    cayleyEvaluation
