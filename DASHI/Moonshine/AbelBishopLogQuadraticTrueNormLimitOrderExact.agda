module DASHI.Moonshine.AbelBishopLogQuadraticTrueNormLimitOrderExact where

------------------------------------------------------------------------
-- ORIGINAL BISHOP LOG(1+w): FINITE COMPLEX TRIANGLE -> ACTUAL LIMIT.
--
-- P1.L most important mathematical cut: avoid the tempting, unjustified
-- extra assumption that Euclidean norms of the partial sums converge.
-- The EXISTING Bishop componentwise log-series convergence gives
--   re(R2_n) -> re(R2) and im(R2_n) -> im(R2).
-- Native Bishop real product/addition limit laws directly imply
--   N(R2_n) -> N(R2), where N(z) = re(z)^2 + im(z)^2.
--
-- Take the already-proved FINITE sharp norm bound
--   ||R2_n(w)|| <= (|w|^2/2)/(1-|w|).
-- Square using positivity, pass the squared inequality to the
-- limit via ORIGINAL Sequence.xₙ≤yₙ⇒limxₙ≤limyₙ, then use the
-- existing Balaban R4 scalar rootMonotone/rootOfSquare laws.
--
-- This proves, on the SAME original Bishop complex log limit,
-- the desired true-displacement inequality:
--   ||log_B(1+w)-w|| <= (|w|^2/2)/(1-|w|)
-- whenever N(w)<=ratio², 0<=ratio<1.
--
-- No independent norm-limit axiom, no new log, no selected radius
-- equality, no geometric-majorant record, no fake square roots.
-- The existing BishopSquareRootCalculus input REMAINS UNINHABITED;
-- local pinned Agda 2.9 typechecking still pending.
------------------------------------------------------------------------

open import Agda.Builtin.Nat using (Nat; suc)

import Real as BishopReal
import RealProperties as BishopP
import Sequence as BishopSequence

import DASHI.Analysis.BishopComplexSeriesConvergenceExact as Complex
import DASHI.Analysis.BishopComplexNormSquarePowerEnvelopeExact as Norm
import DASHI.Analysis.BishopComplexNormSquareUpperPowerEnvelopeExact as Upper
import DASHI.Moonshine.AbelBishopKoenigsComponentwiseCompletionExact as Completion
import DASHI.Analysis.BishopComplexConstantMultiplicationConvergenceExact as Continuity
import DASHI.Physics.YangMills.BalabanP33BishopR4ChordMetricFromSquareRootExact as R4
import DASHI.Physics.YangMills.BalabanStepVBishopFiniteGeometricExact as BishopStepV
import DASHI.Foundations.BishopFiniteDegreeOneGeometricBoundExact as Unit
import DASHI.Foundations.BishopSquareNonnegativeExact as SquareNN
import DASHI.Moonshine.AbelBishopLogQuadraticHalfCoefficientExact as Half
import DASHI.Moonshine.AbelBishopLogQuadraticFiniteTailExact as Finite
import DASHI.Moonshine.AbelBishopLogQuadraticUpperDiskSeriesLimitExact as UpperTail
import DASHI.Moonshine.AbelBishopLogQuadraticTrueNormFiniteMajorantExact as Majorant
import DASHI.Moonshine.AbelBishopLogQuadraticTrueNormGeometricBoundExact as Geometric

-- This is a GENUINE consequence of existing scalar convergence algebra,
-- for EVERY original Bishop complex sequence. In particular it does
-- not assume that sqrt is continuous or that complex norms converge.
originalBishopNormSquareLimitFromComponents :
  (values : Nat → Complex.BishopComplex) →
  (limit : Complex.BishopComplex) →
  Completion.OriginalBishopPointwiseComplexConverges values limit →
  BishopSequence._ConvergesTo_
    (λ n → Norm.normSqC (values n))
    (Norm.normSqC limit)
originalBishopNormSquareLimitFromComponents values limit convergence =
  let
    realLimit = Complex.re limit
    imagLimit = Complex.im limit

    realSquaredConverges =
      BishopSequence.xₙyₙ→x₀y₀
        (realLimit , Completion.realConverges convergence)
        (realLimit , Completion.realConverges convergence)

    imagSquaredConverges =
      BishopSequence.xₙyₙ→x₀y₀
        (imagLimit , Completion.imaginaryConverges convergence)
        (imagLimit , Completion.imaginaryConverges convergence)
  in
  BishopSequence.xₙ+yₙ→x₀+y₀
    (Norm.square realLimit , realSquaredConverges)
    (Norm.square imagLimit , imagSquaredConverges)

-- Geometric comparison value, with an ACTUAL Bishop inverse and the
-- original true radius r. This is NOT a free "majorant" scalar input.
originalBishopSharpQuadraticValue :
  (roots : R4.BishopSquareRootCalculus) →
  ∀ w →
  (rLessOne :
    BishopReal._<_ (Majorant.trueBishopRadius roots w)
      BishopReal.1ℝ) →
  BishopReal.ℝ
originalBishopSharpQuadraticValue roots w rLessOne =
  let
    radius = Majorant.trueBishopRadius roots w
    inputs = Geometric.originalBishopTrueNormGeometricInputs
      roots w rLessOne
  in
  BishopReal._*_
    (BishopReal._*_ Half.bishopHalf (Norm.square radius))
    (BishopStepV.bishopGeometricUniformBound inputs)

originalBishopSharpQuadraticValueNonnegative :
  (roots : R4.BishopSquareRootCalculus) →
  ∀ w →
  (rLessOne :
    BishopReal._<_ (Majorant.trueBishopRadius roots w)
      BishopReal.1ℝ) →
  BishopReal.NonNegative
    (originalBishopSharpQuadraticValue roots w rLessOne)
originalBishopSharpQuadraticValueNonnegative roots w rLessOne =
  let
    radius = Majorant.trueBishopRadius roots w
    inputs = Geometric.originalBishopTrueNormGeometricInputs
      roots w rLessOne
    scaleNN =
      BishopP.nonNegx,y⇒nonNegx*y
        Half.bishopHalfNonnegative
        (SquareNN.bishopSquareNonnegative radius)
    inversePositive =
      BishopStepV.bishopGeometricUniformBoundPositive inputs
  in BishopP.nonNegx,y⇒nonNegx*y
    scaleNN
    (BishopP.pos⇒nonNeg
      (BishopP.0<x⇒posx inversePositive))

-- The finite bound is Euclidean, but order comparison works on
-- REAL norm squares. This lemma uses the original rooted square law
-- and ordered-real multiplication monotonicity, not sqrt continuity.
originalBishopFiniteQuadraticNormSquareUpper :
  (roots : R4.BishopSquareRootCalculus) →
  ∀ w →
  (rLessOne :
    BishopReal._<_ (Majorant.trueBishopRadius roots w)
      BishopReal.1ℝ) →
  ∀ n →
  BishopReal._≤_
    (Norm.normSqC (Finite.originalBishopLogQuadraticTailPrefix w n))
    (Norm.square
      (originalBishopSharpQuadraticValue roots w rLessOne))
originalBishopFiniteQuadraticNormSquareUpper roots w rLessOne n =
  let
    prefix = Finite.originalBishopLogQuadraticTailPrefix w n
    prefixNN = Upper.normSquareNonnegative prefix
    rootedNN =
      R4.rootNonnegative roots (Norm.normSqC prefix) prefixNN
    bound = originalBishopSharpQuadraticValue roots w rLessOne
    boundNN = originalBishopSharpQuadraticValueNonnegative
      roots w rLessOne
    finiteBound =
      Geometric.originalBishopQuadraticFiniteTrueNormGeometricBound
        roots w rLessOne n
  in
  BishopP.≤-respˡ-≃
    (BishopP.≃-symm
      (R4.rootSquare roots (Norm.normSqC prefix) prefixNN))
    (BishopP.*-mono-≤
      rootedNN rootedNN finiteBound finiteBound)

-- This is the ACTUAL requested order-closed limit step. It uses the
-- original upper-disk Bishop series limit from the old module,
-- not a newly chosen limit or an oracle for norm convergence.
originalBishopUpperDiskRemainderNormSquareUpper :
  (roots : R4.BishopSquareRootCalculus) →
  ∀ {w ratio} →
  (interval : Unit.BishopUnitIntervalRatio ratio) →
  (disk : Upper.BishopComplexNormSquareUpperRadius w ratio) →
  (rLessOne :
    BishopReal._<_ (Majorant.trueBishopRadius roots w)
      BishopReal.1ℝ) →
  BishopReal._≤_
    (Norm.normSqC
      (UpperTail.originalBishopUpperDiskQuadraticRemainder interval disk))
    (Norm.square
      (originalBishopSharpQuadraticValue roots w rLessOne))
originalBishopUpperDiskRemainderNormSquareUpper
    roots {w} interval disk rLessOne =
  let
    partials = Finite.originalBishopLogQuadraticTailPrefix w
    limit = UpperTail.originalBishopUpperDiskQuadraticRemainder
      interval disk
    bound = originalBishopSharpQuadraticValue roots w rLessOne
    sourceConverges =
      UpperTail.originalBishopUpperDiskQuadraticTailConverges
        interval disk
    squaredConverges =
      originalBishopNormSquareLimitFromComponents
        partials limit sourceConverges
  in
  BishopSequence.xₙ≤yₙ⇒limxₙ≤limyₙ
    (originalBishopFiniteQuadraticNormSquareUpper
      roots w rLessOne)
    (Norm.normSqC limit , squaredConverges)
    (Norm.square bound ,
      Continuity.originalBishopConstantSequenceConverges
        (Norm.square bound))

-- From a SOURCE-WRITTEN original closed-disk certificate, recover
-- r=||w|| <= ratio. No exact-radius equation is assumed on w.
originalBishopTrueNormBelowUpperDiskRadius :
  (roots : R4.BishopSquareRootCalculus) →
  ∀ {w ratio} →
  Upper.BishopComplexNormSquareUpperRadius w ratio →
  BishopReal._≤_
    (Majorant.trueBishopRadius roots w) ratio
originalBishopTrueNormBelowUpperDiskRadius roots {w} {ratio} disk =
  BishopP.≤-respʳ-≃
    (BishopP.≃-trans
      (R4.rootOfSquare roots ratio)
      (BishopP.nonNegx⇒∣x∣≃x
        (Upper.radiusNonnegative disk)))
    (R4.rootMonotone roots
      (Upper.normSquareNonnegative w)
      (Upper.normSqBelowRadiusSquare disk))

-- The genuinely selected upper disk already has ratio<1, so the
-- root true norm is strictly below one without an extra hypothesis.
originalBishopTrueNormBelowOneFromDisk :
  (roots : R4.BishopSquareRootCalculus) →
  ∀ {w ratio} →
  (interval : Unit.BishopUnitIntervalRatio ratio) →
  (disk : Upper.BishopComplexNormSquareUpperRadius w ratio) →
  BishopReal._<_ (Majorant.trueBishopRadius roots w) BishopReal.1ℝ
originalBishopTrueNormBelowOneFromDisk roots interval disk =
  BishopP.≤-<-trans
    (originalBishopTrueNormBelowUpperDiskRadius roots disk)
    (Unit.ratioBelowOne interval)

-- P1.L SOURCE RESULT:
-- The ACTUAL canonical Bishop log(1+w)-w (not an arbitrary complex
-- sequence, selected radius or assumed principal-branch derivative)
-- satisfies the sharp true-displacement quadratic remainder bound.
originalBishopUpperDiskLogQuadraticTrueNormBound :
  (roots : R4.BishopSquareRootCalculus) →
  ∀ {w ratio} →
  (interval : Unit.BishopUnitIntervalRatio ratio) →
  (disk : Upper.BishopComplexNormSquareUpperRadius w ratio) →
  let
    inside = originalBishopTrueNormBelowOneFromDisk roots interval disk
  in BishopReal._≤_
    (Majorant.trueBishopRadius roots
      (UpperTail.originalBishopUpperDiskQuadraticRemainder interval disk))
    (originalBishopSharpQuadraticValue roots w inside)
originalBishopUpperDiskLogQuadraticTrueNormBound roots {w}
    interval disk =
  let
    inside = originalBishopTrueNormBelowOneFromDisk
      roots interval disk
    limit = UpperTail.originalBishopUpperDiskQuadraticRemainder
      interval disk
    upper = originalBishopSharpQuadraticValue roots w inside
    upperNN = originalBishopSharpQuadraticValueNonnegative
      roots w inside
    squaredBound =
      originalBishopUpperDiskRemainderNormSquareUpper
        roots interval disk inside
  in
  BishopP.≤-respʳ-≃
    (BishopP.≃-trans
      (R4.rootOfSquare roots upper)
      (BishopP.nonNegx⇒∣x∣≃x upperNN))
    (R4.rootMonotone roots
      (Upper.normSquareNonnegative limit)
      squaredBound)
