{-# OPTIONS --safe #-}
module DASHI.Analysis.BishopK04dK05NativeProductDischargeExact where

------------------------------------------------------------------------
-- K05-PRODUCT: SOURCE-WRITTEN DISCHARGE ON THE SELECTED ROUND11
-- BISHOP CARRIER, WITH NO PRODUCT, PYTHAGOREAN OR MODULUS PREMISES.
--
-- This is a direct terminal consumer of the original signed factorial
-- coefficient theorem and its native complex Cauchy triangle limit.
-- It also pays the trig side of the K04d Basel-region certificate,
-- so that K04d requires only its actual original source log inverse.
--
-- This file does not assert LOG or the two atan-Cayley evaluations:
-- those still need infinite source composition and evaluation proofs.
-- Original authors/credit: Bishop & Bridges; Murray/Csimma Bishop;
-- Newton/Cauchy, Machin; DASHI Round11 signed factorial owners.
------------------------------------------------------------------------

open import Agda.Builtin.Nat using (Nat; suc)
open import Data.Product.Base using (_×_; _,_)

import Real as R

import DASHI.Analysis.BishopSetoidComplexExact as C
import DASHI.Analysis.BishopImaginaryProductPythagoreanReuseExact as Product
import DASHI.Analysis.BishopMachinCayleyNativeProductFirstZeroExact as Native
import DASHI.Analysis.BishopMachinTwoPointCayleyCompositionExact as TwoPoint
import DASHI.Analysis.BishopMachinFirstPositiveSineZeroFromNativePhaseExact as First
import DASHI.Analysis.BishopK04dNatLogFromOriginalGapExact as Log
import DASHI.Analysis.BishopRiemannComplexAboveTwoBaselExact as Region
import DASHI.Analysis.BishopRiemannDirichletExponentialTermExact as Terms
import DASHI.Analysis.BishopDirichletUniformBaselTailsExact as Tails
import DASHI.Foundations.BishopSignedFactorialDegreeBinomialExact as Signed
import DASHI.Moonshine.BishopMachinSetoidComplexInstanceExact as Route
import DASHI.Physics.YangMills.YangMillsSubmissionBishopCutsetExact as Round11

-- The native factorial coefficient theorem produces the ORIGINAL
-- imaginary exponential product without any user-supplied hypothesis.
sourceImaginaryProduct :
  (inputs : Round11.BishopCutset) →
  Product.Round11ImaginaryExpMultiplicative inputs
sourceImaginaryProduct = Native.originalNativeImaginaryExpProduct

-- Both addition laws are genuine values of the Round11 power series.
sourceSineCosineAddition :
  (inputs : Round11.BishopCutset) →
  (x y : R.ℝ) →
  C.BishopSineAdditionAt
    (Route.machinTranscendentals inputs) x y
  ×
  C.BishopCosineAdditionAt
    (Route.machinTranscendentals inputs) x y
sourceSineCosineAddition =
  Signed.originalSineCosineAdditionFromNativeFactorials

-- No independent Pythagorean premise: evaluate the same product
-- at the anti-diagonal and use the original Round11 parity laws.
sourcePythagorean :
  (inputs : Round11.BishopCutset) →
  (theta : R.ℝ) →
  let c = Product.cosB inputs theta
      s = Product.sinB inputs theta
  in
  R._≃_ (R._+_ (R._*_ c c) (R._*_ s s)) R.1ℝ
sourcePythagorean inputs theta =
  Product.round11PythagoreanFromImaginaryProduct
    inputs (sourceImaginaryProduct inputs) theta

sourcePhaseBounds :
  (inputs : Round11.BishopCutset) →
  (theta : R.ℝ) →
  (R._≤_ (R.∣ Product.cosB inputs theta ∣) R.1ℝ)
  ×
  (R._≤_ (R.∣ Product.sinB inputs theta ∣) R.1ℝ)
sourcePhaseBounds inputs theta =
  Product.round11ModulusFromImaginaryProduct
    inputs (sourceImaginaryProduct inputs) theta

-- K04d's region-wide *source* Basel domination now consumes only
-- the actual negative-log exponential-gap theorem. Every trig
-- modulus, product, and Pythagorean input is supplied above.
sourceBaselRegionFromLogIdentity :
  (inputs : Round11.BishopCutset) →
  Log.OriginalBishopNegativeLogExponentialGap →
  Tails.RegionBaselDomination
    (Terms.bishopDirichletExponentialTerm
      (Route.machinTranscendentals inputs)
      Terms.sourceCanonicalNatLogCandidate)
    Region.sourceAboveTwoRegion
sourceBaselRegionFromLogIdentity =
  Native.sourceRegionBaselFromOneNativeLogIdentity

-- K05-PI's global positive-first-zero consumer has NO further
-- algebraic, product, sign or quarter-angle hypotheses once the
-- two *actual original* atan/exponential values are supplied.
sourceFirstPositiveZeroFromTwoOriginalAtans :
  (inputs : Round11.BishopCutset) →
  TwoPoint.OriginalAtanFiveCayleyEvaluation inputs →
  TwoPoint.OriginalAtan239CayleyEvaluation inputs →
  First.SourceMachinFirstPositiveSineZero inputs
sourceFirstPositiveZeroFromTwoOriginalAtans =
  TwoPoint.originalMachinFirstPositiveSineZeroFromTwoAtanCayleyValues
