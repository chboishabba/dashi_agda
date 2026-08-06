module DASHI.Physics.YangMills.BalabanP33BishopSU2AdDexpNumeratorBoundsExact where

------------------------------------------------------------------------
-- PRIMARY SOURCES
--
-- Brian C. Hall,
-- "Lie Groups, Lie Algebras, and Representations: An Elementary
-- Introduction", second edition, Springer, 2015.
-- DOI: 10.1007/978-3-319-13467-3.
--
-- Ethan Eade,
-- "Derivative of the Exponential Map", technical note, 2018 revision.
-- No DOI recorded.
--
-- Zachary Murray,
-- "Constructive Analysis in the Agda Proof Assistant",
-- B.Sc. Honours thesis, Dalhousie University, 2022.
-- arXiv:2205.08354. No DOI assigned.
--
-- DASHI CONTRIBUTION
--
-- Turn the concrete Bishop Taylor defects into the exact scalar numerators
-- appearing in the SU(2) Cayley--Hamilton norm budgets.  For 0 <= t <= 1/2,
--
--   sin t + (1 - cos t) <= t + t^2/2,
--
-- and
--
--   (1 - cos t) + (t - sin t) <= t^2/2 + t^3/6
--                              = t (t/2 + t^2/6).
--
-- The first is exactly the scaled Ad(exp X)-I coefficient budget.  The second
-- is the numerator of the dexp_X-I budget before the removable division by t.
-- Both are derived from the checked alternating series, not supplied as
-- trigonometric assumptions.
------------------------------------------------------------------------

open import Agda.Builtin.Nat using (zero; suc)
open import Data.Integer.Base using (+_)
open import Data.Rational.Unnormalised as ℚ using (ℚᵘ; _/_)

import Real as BishopReal
import RealProperties as BishopProperties

import DASHI.Foundations.BishopPowerSeriesElementaryBridgeExact as Elementary
import DASHI.Physics.YangMills.BalabanBishopConcreteSineCosineInterlacingExact as Concrete
import DASHI.Physics.YangMills.BalabanBishopAlternatingInterlacingFromDecreasingTermsExact as Alternating
import DASHI.Physics.YangMills.BalabanBishopAlternatingBracketFromMonotoneLimitsExact as Interlacing
import DASHI.Physics.YangMills.BalabanP33BishopTaylorPolynomialFormExact as Taylor
open import DASHI.Physics.YangMills.CompactLieProofLevel

oneSixth oneHalf : ℚᵘ
oneSixth = + 1 / 6
oneHalf = + 1 / 2

bishopOneSixth bishopOneHalf : BishopReal.ℝ
bishopOneSixth = BishopReal._⋆ oneSixth
bishopOneHalf = BishopReal._⋆ oneHalf

square cube : BishopReal.ℝ → BishopReal.ℝ
square value = BishopReal._*_ value value
cube value = BishopReal._*_ (square value) value

adScalarNumerator :
  Elementary.BishopElementaryPowerSeriesData →
  BishopReal.ℝ → BishopReal.ℝ
adScalarNumerator dataSet value =
  BishopReal._+_
    (Elementary.bishopSin dataSet value)
    (BishopReal._-_ BishopReal.1ℝ
      (Elementary.bishopCos dataSet value))

adTaylorEnvelope : BishopReal.ℝ → BishopReal.ℝ
adTaylorEnvelope value =
  BishopReal._+_ value
    (BishopReal._*_ bishopOneHalf (square value))

dexpScalarNumerator :
  Elementary.BishopElementaryPowerSeriesData →
  BishopReal.ℝ → BishopReal.ℝ
dexpScalarNumerator dataSet value =
  BishopReal._+_
    (BishopReal._-_ BishopReal.1ℝ
      (Elementary.bishopCos dataSet value))
    (BishopReal._-_ value
      (Elementary.bishopSin dataSet value))

dexpTaylorEnvelope : BishopReal.ℝ → BishopReal.ℝ
dexpTaylorEnvelope value =
  BishopReal._+_
    (BishopReal._*_ bishopOneHalf (square value))
    (BishopReal._*_ bishopOneSixth (cube value))

dexpLinearizedEnvelope : BishopReal.ℝ → BishopReal.ℝ
dexpLinearizedEnvelope value =
  BishopReal._+_
    (BishopReal._*_ bishopOneHalf value)
    (BishopReal._*_ bishopOneSixth (square value))

adScalarNumeratorBelowTaylorEnvelope :
  ∀ {dataSet value} →
  Concrete.ConcreteHalfBallSeriesInputs dataSet value →
  BishopReal._≤_
    (adScalarNumerator dataSet value)
    (adTaylorEnvelope value)
adScalarNumeratorBelowTaylorEnvelope inputs =
  let
    polynomial = Taylor.polynomialTaylorBounds inputs
    defects = Taylor.defectTaylorBounds inputs
  in
  BishopProperties.+-mono-≤
    (Taylor.sineLinearUpper polynomial)
    (Taylor.cosineDefectBelowQuadratic defects)

dexpScalarNumeratorBelowTaylorEnvelope :
  ∀ {dataSet value} →
  Concrete.ConcreteHalfBallSeriesInputs dataSet value →
  BishopReal._≤_
    (dexpScalarNumerator dataSet value)
    (dexpTaylorEnvelope value)
dexpScalarNumeratorBelowTaylorEnvelope inputs =
  let defects = Taylor.defectTaylorBounds inputs
  in
  BishopProperties.+-mono-≤
    (Taylor.cosineDefectBelowQuadratic defects)
    (Taylor.sineDefectBelowCubic defects)

dexpTaylorEnvelopeFactorization : ∀ value →
  BishopReal._≃_
    (dexpTaylorEnvelope value)
    (BishopReal._*_ value (dexpLinearizedEnvelope value))
dexpTaylorEnvelopeFactorization value =
  let open BishopProperties.ℝ-Solver
  in solve 1
    (λ t →
      (Κ oneHalf ⊗ (t ⊗ t))
        ⊕ (Κ oneSixth ⊗ ((t ⊗ t) ⊗ t))
      ⊜ t ⊗ ((Κ oneHalf ⊗ t)
        ⊕ (Κ oneSixth ⊗ (t ⊗ t))))
    BishopProperties.≃-refl value

adScalarNumeratorNonnegative :
  ∀ {dataSet value} →
  Concrete.ConcreteHalfBallSeriesInputs dataSet value →
  BishopReal._≤_ BishopReal.0ℝ
    (adScalarNumerator dataSet value)
adScalarNumeratorNonnegative inputs =
  let
    concrete = Concrete.concreteSineCosineInterlacing inputs
    sineData = Concrete.sineAlternatingSeriesData inputs
    defects = Taylor.defectTaylorBounds inputs
  in
  BishopProperties.+-mono-≤
    (BishopProperties.≤-trans
      (Alternating.lowerPartialNonnegative sineData (suc zero))
      (Interlacing.lowerPartialBelowRepresentedLimit
        (Interlacing.sineInterlacing concrete) (suc zero)))
    (Taylor.cosineDefectNonnegative defects)

dexpScalarNumeratorNonnegative :
  ∀ {dataSet value} →
  Concrete.ConcreteHalfBallSeriesInputs dataSet value →
  BishopReal._≤_ BishopReal.0ℝ
    (dexpScalarNumerator dataSet value)
dexpScalarNumeratorNonnegative inputs =
  let defects = Taylor.defectTaylorBounds inputs
  in
  BishopProperties.+-mono-≤
    (Taylor.cosineDefectNonnegative defects)
    (Taylor.sineDefectNonnegative defects)

p33BishopAdScalarNumeratorLevel : ProofLevel
p33BishopAdScalarNumeratorLevel = machineChecked

p33BishopDexpScalarNumeratorLevel : ProofLevel
p33BishopDexpScalarNumeratorLevel = machineChecked
