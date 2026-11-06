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
import DASHI.Analysis.BishopRiemannComplexAboveTwoBaselExact as Region
import DASHI.Analysis.BishopRiemannDirichletExponentialTermExact as Terms
import DASHI.Analysis.BishopK04dNatLogFromOriginalGapExact as NativeLog
import DASHI.Analysis.BishopDirichletUniformBaselTailsExact as Uniform
import DASHI.Foundations.BishopExponentialSeriesConvergenceExact as Exp
import DASHI.Foundations.BishopCubicTranslationIteratedExact as NatReal
import DASHI.Moonshine.BishopRound11MachinSetoidComplexInstanceExact as Route
open import Agda.Builtin.Nat using (Nat; suc)
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


------------------------------------------------------------------------
-- K04d-CONTINUITY: remove the parallel phase-modulus/Pythagorean
-- authority from the original region-wide Basel bound as well.
-- The only remaining mathematical input is the selected original
-- exponential-of-Nat-log inverse, sourced from K04d-LOG.
------------------------------------------------------------------------

sourceRegionBaselFromNativeSignedFactorials :
  (inputs : Round11.Round11BishopCutset) →
  ((n : Nat) →
    R._≃_
      (Exp.bishopExp (Terms.sourceCanonicalNatLogCandidate n))
      (NatReal.natReal (suc n))) →
  Uniform.RegionBaselDomination
    (Terms.bishopDirichletExponentialTerm
      (Route.round11MachinTranscendentals inputs)
      Terms.sourceCanonicalNatLogCandidate)
    Region.sourceAboveTwoRegion
sourceRegionBaselFromNativeSignedFactorials inputs inverse =
  Product.sourceRegionWideFromSingleImaginaryProduct
    inputs inverse (originalNativeImaginaryExpProduct inputs)


------------------------------------------------------------------------
-- K04d LOG -> K04d CONTINUITY PAYOFF:
-- no separately postulated Nat-index exp/log inverse family, and no
-- separately postulated imaginary-exponential product/Pythagorean.
-- The Basel majorant is compiled from ONE actual source-native
-- exp_B(-L(x))=1-x theorem, via exact canonical Nat specialization.
------------------------------------------------------------------------

sourceRegionBaselFromOneNativeLogIdentity :
  (inputs : Round11.Round11BishopCutset) →
  NativeLog.OriginalBishopNegativeLogExponentialGap →
  Uniform.RegionBaselDomination
    (Terms.bishopDirichletExponentialTerm
      (Route.round11MachinTranscendentals inputs)
      Terms.sourceCanonicalNatLogCandidate)
    Region.sourceAboveTwoRegion
sourceRegionBaselFromOneNativeLogIdentity inputs originalLogIdentity =
  sourceRegionBaselFromNativeSignedFactorials
    inputs
    (NativeLog.sourceCanonicalNatLogAllIndicesExpInverse
      originalLogIdentity)
