{-# OPTIONS --safe #-}
module DASHI.Analysis.BishopRound11ImaginaryProductPythagoreanReuseExact where

------------------------------------------------------------------------
-- K04d / K05 SAME-OBJECT MAX-CUT REUSE.
--
-- One source-native pure-imaginary exponential multiplication theorem
-- implies BOTH original Bishop trig additions (Cartesian projections).
-- Cosine addition at (theta,-theta) plus already-owned native parity
-- and cosine-zero proves the ORIGINAL Pythagorean identity.
--
-- Thus the entire variable-s complex Basel comparison may consume
-- the single mixed signed-factorial Cauchy-product theorem, not a
-- SECOND independently assumed Pythagorean theorem. The remaining
-- exp_B(L_n)=n+1 is still an independent genuine analytic obligation.
--
-- No postulates, axioms, generic classical trig equations or
-- alternate real/complex carriers are introduced in this source.
--
-- Attribution: Bishop & Bridges (constructive reals);
-- Zachary Murray and Viktor Csimma (vendor/bishop);
-- existing DASHI Round11, imaginary-phase, and Dirichlet owners.
------------------------------------------------------------------------

open import Agda.Builtin.Nat using (Nat; suc)
open import Data.Product.Base using (_×_; proj₁; proj₂)

import Real as R
import RealProperties as RP
import DASHI.Analysis.BishopSetoidComplexExact as C
import DASHI.Analysis.BishopMachinQuarterPhaseQuadruplicationAlgebraExact as Quad
import DASHI.Foundations.BishopMachinQuarterAngleBranchExact as Quarter
import DASHI.Foundations.BishopMachinArctanConstructionExact as Machin
import DASHI.Analysis.BishopRiemannComplexAboveTwoBaselExact as Region
import DASHI.Analysis.BishopRiemannDirichletExponentialTermExact as Terms
import DASHI.Analysis.BishopRiemannDirichletBaselSameObjectExact as Dirichlet
import DASHI.Analysis.BishopDirichletUniformBaselTailsExact as Uniform
import DASHI.Analysis.BishopRound11TrigModulusFromPythagoreanExact as Modulus
import DASHI.Foundations.BishopRound11TrigAtZeroExact as Origin
import DASHI.Foundations.BishopPowerSeriesElementaryBridgeExact as E
import DASHI.Foundations.BishopExponentialSeriesConvergenceExact as Exp
import DASHI.Foundations.BishopCubicTranslationIteratedExact as NatReal
import DASHI.Moonshine.BishopRound11MachinSetoidComplexInstanceExact as Route
import DASHI.Physics.YangMills.YangMillsSubmissionRound11ExactCutset as Round11

-- The Round11 zero-angle owner keeps these local abbreviations private.
-- Give THIS source a transparent abbreviation of the same literal terms.
sinB cosB : Round11.Round11BishopCutset → R.ℝ → R.ℝ
sinB inputs = E.bishopSin (Round11.elementarySeries inputs)
cosB inputs = E.bishopCos (Round11.elementarySeries inputs)

Round11ImaginaryExpMultiplicative :
  Round11.Round11BishopCutset → Set
Round11ImaginaryExpMultiplicative inputs =
  (x y : R.ℝ) →
  let T = Route.round11MachinTranscendentals inputs
  in
  C._≈C_
    (C.expC T
      (C.pureImaginary (R._+_ x y)))
    (C._*C_
      (C.expC T (C.pureImaginary x))
      (C.expC T (C.pureImaginary y)))

-- The true Pythagorean identity is DERIVED using only the
-- anti-diagonal instance of the original source product.
round11PythagoreanFromImaginaryProduct :
  (inputs : Round11.Round11BishopCutset) →
  Round11ImaginaryExpMultiplicative inputs →
  (theta : R.ℝ) →
  let
    c = cosB inputs theta
    s = sinB inputs theta
  in
  R._≃_
    (R._+_ (R._*_ c c) (R._*_ s s))
    R.1ℝ
round11PythagoreanFromImaginaryProduct inputs product theta =
  Origin.round11PythagoreanFromCosineAdditionOpposite inputs theta
    (proj₂
      (C.imaginaryExponentialProductGivesAddition
        (Route.round11MachinTranscendentals inputs)
        theta (R.- theta)
        (product theta (R.- theta))))

-- The same ONE Cauchy-product obligation now produces the
-- original Round11 phase magnitude bounds used by Dirichlet.
round11ModulusFromImaginaryProduct :
  (inputs : Round11.Round11BishopCutset) →
  Round11ImaginaryExpMultiplicative inputs →
  (theta : R.ℝ) →
  (R._≤_ (R.∣ cosB inputs theta ∣) R.1ℝ)
  ×
  (R._≤_ (R.∣ sinB inputs theta ∣) R.1ℝ)
round11ModulusFromImaginaryProduct inputs product theta =
  Modulus.round11ModulusFromPythagorean
    inputs theta
    (round11PythagoreanFromImaginaryProduct inputs product theta)

-- The constructed original Dirichlet series now depends on exactly:
--   1. Native exponential inverse at the canonical Nat logs.
--   2. Native pure-imaginary exp multiplicativity, which also
--      yields full sine/cosine addition and the Pythagorean law.
-- No THIRD trig-modulus or arbitrary-zeta authority is present.
sourceRegionWideFromSingleImaginaryProduct :
  (inputs : Round11.Round11BishopCutset) →
  ((n : Nat) →
    R._≃_
      (Exp.bishopExp (Terms.sourceCanonicalNatLogCandidate n))
      (NatReal.natReal (suc n))) →
  Round11ImaginaryExpMultiplicative inputs →
  Uniform.RegionBaselDomination
    (Terms.bishopDirichletExponentialTerm
      (Route.round11MachinTranscendentals inputs)
      Terms.sourceCanonicalNatLogCandidate)
    Region.sourceAboveTwoRegion
sourceRegionWideFromSingleImaginaryProduct inputs inverse product =
  Region.sourceRegionWideBaselCertificate inputs inverse
    (round11PythagoreanFromImaginaryProduct inputs product)


------------------------------------------------------------------------
-- K05: SOURCE-NATIVE DOUBLE-ANGLE FROM THE SAME SINGLE IMAGINARY
-- CAUCHY PRODUCT. Reuse the independently compiled fourfold Machin
-- polynomial / original-Round11-sine-cosine commuting square.
------------------------------------------------------------------------

round11DoubleAngleFromImaginaryProduct :
  (inputs : Round11.Round11BishopCutset) →
  Round11ImaginaryExpMultiplicative inputs →
  Quad.Round11BishopDoubleAngle inputs
round11DoubleAngleFromImaginaryProduct inputs product = record
  { Quad.sineDouble = λ point →
      let
        laws = C.imaginaryExponentialProductGivesAddition
          (Route.round11MachinTranscendentals inputs)
          point point
          (product point point)
        sineAt = Quad.round11Sine inputs point
        cosineAt = Quad.round11Cos inputs point
      in
      RP.≃-trans
        (proj₁ laws)
        (RP.≃-trans
          (RP.+-comm
            (R._*_ sineAt cosineAt)
            (R._*_ cosineAt sineAt))
          (RP.≃-symm
            (Quad.sinDoubleAsCrossSum cosineAt sineAt)))
  ; Quad.cosineDouble = λ point →
      proj₂
        (C.imaginaryExponentialProductGivesAddition
          (Route.round11MachinTranscendentals inputs)
          point point
          (product point point))
  }

-- At the ORIGINAL Machin angle, exact sin(pi_M)=0 and
-- cos(pi_M)=-1 follow from the same product law and only the
-- separately owed atan/tan QUARTER semantic relation cos θ=sin θ.
-- The Pythagorean is now DERIVED, not passed as a second hypothesis.
round11MachinTrigEndpointFromImaginaryProduct :
  (inputs : Round11.Round11BishopCutset) →
  (product : Round11ImaginaryExpMultiplicative inputs) →
  R._≃_
    (Quad.quarterCos inputs)
    (Quad.quarterSin inputs) →
  (R._≃_
    (Quad.round11Sine inputs Machin.bishopMachinPi) R.0ℝ)
  ×
  (R._≃_
    (Quad.round11Cos inputs Machin.bishopMachinPi)
    (R.-_ R.1ℝ))
round11MachinTrigEndpointFromImaginaryProduct
    inputs product quarterCosEqualsSin =
  Quad.actualMachinTrigEndpointFromDoubleAngle
    inputs
    (round11DoubleAngleFromImaginaryProduct inputs product)
    quarterCosEqualsSin
    (round11PythagoreanFromImaginaryProduct
      inputs product Quarter.machinQuarterAngle)
