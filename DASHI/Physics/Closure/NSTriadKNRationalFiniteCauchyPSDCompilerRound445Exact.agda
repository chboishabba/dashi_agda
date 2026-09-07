module DASHI.Physics.Closure.NSTriadKNRationalFiniteCauchyPSDCompilerRound445Exact where

------------------------------------------------------------------------
-- ROUND445 / CONSTRUCT FINITE RATIONAL CAUCHY PSD BY STRUCTURAL RECURSION
--
-- R443 proves the exact Cauchy Schur-complement entry identity.
-- R444 proves the generic finite rank-one quadratic split and diagonal scaling.
-- This file composes them and removes the last caller-supplied finite
-- decomposition certificate.
--
-- For positive rational rates x_i and arbitrary rational coefficients z_i,
--
--        Q = sum_{i,j} z_i z_j / (x_i+x_j) >= 0.
--
-- The implementation uses the symmetric recursive representation of the full
-- double sum.  At head rate x,
--
--   Q = Kxx (z_x + 2x S)^2 + Q_tail(d_i z_i),
--
-- where S=sum_i K(x,x_i)z_i and
-- d_i=(x_i-x)K(x,x_i).  The recursive call is structurally on the tail.
--
-- Each point also retains one scalar coefficient.  The main theorem still
-- quantifies over arbitrary coefficient functions; the retained coordinate is
-- only a lossless adapter for later Complex3 coordinate lifts.
--
-- No exponential, improper integral, matrix determinant, square root,
-- spectral theorem, or external positivity theorem is used.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Data.Rational.Base using
  (ℚ; 0ℚ; 1ℚ; Positive; NonNegative; _+_; _-_; _*_; _≤_; nonNegative)
import Data.Rational.Properties as ℚP
open import Data.Rational.Tactic.RingSolver using (solve)
open import Relation.Binary.PropositionalEquality using (cong; cong₂; subst; sym; trans)

import DASHI.Physics.Closure.NSTriadKNRationalOrderedFiniteL2 as Rational
import DASHI.Physics.Closure.NSTriadKNRationalCauchySchurComplementRound443Exact as R443
import DASHI.Physics.Closure.NSTriadKNFiniteKernelRankOneQuadraticSplitRound444Exact as R444

record PositiveRatePoint : Set where
  constructor positive-rate-point
  field
    rate storedCoefficient : ℚ
    ratePositive : Positive rate

open PositiveRatePoint public

cauchyKernel : PositiveRatePoint → PositiveRatePoint → ℚ
cauchyKernel left right = R443.cauchyEntry (rate left) (rate right)

cauchyQuadratic :
  (PositiveRatePoint → ℚ) → List PositiveRatePoint → ℚ
cauchyQuadratic = R444.quadraticForm cauchyKernel

storedCauchyQuadratic : List PositiveRatePoint → ℚ
storedCauchyQuadratic = cauchyQuadratic storedCoefficient

headBeta : PositiveRatePoint → ℚ
headBeta head = (1ℚ + 1ℚ) * rate head

headU : PositiveRatePoint → PositiveRatePoint → ℚ
headU head cell = cauchyKernel head cell

headD : PositiveRatePoint → PositiveRatePoint → ℚ
headD head cell =
  (rate cell - rate head) * cauchyKernel head cell

transformedCoefficient :
  PositiveRatePoint →
  (PositiveRatePoint → ℚ) →
  PositiveRatePoint → ℚ
transformedCoefficient head z cell = headD head cell * z cell

headCoupling :
  PositiveRatePoint →
  (PositiveRatePoint → ℚ) →
  List PositiveRatePoint → ℚ
headCoupling head z rest = R444.linearSum (headU head) z rest

headPivot :
  PositiveRatePoint →
  (PositiveRatePoint → ℚ) →
  List PositiveRatePoint → ℚ
headPivot head z rest =
  cauchyKernel head head
    * (z head + headBeta head * headCoupling head z rest)
    * (z head + headBeta head * headCoupling head z rest)

headKernelSplit :
  (head left right : PositiveRatePoint) →
  cauchyKernel left right
  ≡ headBeta head * headU head left * headU head right
    + R444.scaledKernel cauchyKernel (headD head) left right
headKernelSplit head left right =
  R443.cauchySchurEntryIdentity
    (rate head) (rate left) (rate right)
    (ratePositive head) (ratePositive left) (ratePositive right)

headBetaInverseLaw :
  (head : PositiveRatePoint) →
  cauchyKernel head head * headBeta head ≡ 1ℚ
headBetaInverseLaw head =
  let
    x = rate head
    k = cauchyKernel head head
    base : k * (x + x) ≡ 1ℚ
    base = R443.cauchyEntryInverseLaw x x (ratePositive head) (ratePositive head)
    betaMeaning : headBeta head ≡ x + x
    betaMeaning = solve (x ∷ [])
  in
  trans (cong (k *_) betaMeaning) base

completeSquareFromInverse :
  (k beta z s : ℚ) →
  k * beta ≡ 1ℚ →
  k * z * z
    + (1ℚ + 1ℚ) * z * s
    + beta * s * s
  ≡ k * (z + beta * s) * (z + beta * s)
completeSquareFromInverse k beta z s inverseLaw =
  let
    expanded :
      k * (z + beta * s) * (z + beta * s)
      ≡ k * z * z
        + (1ℚ + 1ℚ) * (k * beta) * z * s
        + (k * beta) * beta * s * s
    expanded = solve (k ∷ beta ∷ z ∷ s ∷ [])

    killInverse :
      k * z * z
        + (1ℚ + 1ℚ) * (k * beta) * z * s
        + (k * beta) * beta * s * s
      ≡ k * z * z
        + (1ℚ + 1ℚ) * 1ℚ * z * s
        + 1ℚ * beta * s * s
    killInverse =
      cong₂ _+_
        (cong₂ _+_
          refl
          (cong (λ selected → (1ℚ + 1ℚ) * selected * z * s) inverseLaw))
        (cong (λ selected → selected * beta * s * s) inverseLaw)

    normalized :
      k * z * z
        + (1ℚ + 1ℚ) * 1ℚ * z * s
        + 1ℚ * beta * s * s
      ≡ k * z * z
        + (1ℚ + 1ℚ) * z * s
        + beta * s * s
    normalized = solve (k ∷ beta ∷ z ∷ s ∷ [])
  in
  sym (trans expanded (trans killInverse normalized))

tailCauchySchurSplit :
  (head : PositiveRatePoint) →
  (z : PositiveRatePoint → ℚ) →
  (rest : List PositiveRatePoint) →
  cauchyQuadratic z rest
  ≡ headBeta head * headCoupling head z rest * headCoupling head z rest
    + cauchyQuadratic (transformedCoefficient head z) rest
tailCauchySchurSplit head z rest =
  trans
    (R444.quadraticRankOneSplit
      cauchyKernel
      (R444.scaledKernel cauchyKernel (headD head))
      (headU head)
      z
      (headBeta head)
      (headKernelSplit head)
      rest)
    (cong
      (λ selected →
        headBeta head * headCoupling head z rest * headCoupling head z rest
        + selected)
      (R444.quadraticDiagonalScaling cauchyKernel (headD head) z rest))

headCauchySchurDecomposition :
  (head : PositiveRatePoint) →
  (rest : List PositiveRatePoint) →
  (z : PositiveRatePoint → ℚ) →
  cauchyQuadratic z (head ∷ rest)
  ≡ headPivot head z rest
    + cauchyQuadratic (transformedCoefficient head z) rest
headCauchySchurDecomposition head rest z =
  let
    s = headCoupling head z rest
    k = cauchyKernel head head
    beta = headBeta head
    tailSplit = tailCauchySchurSplit head z rest

    exposeTail :
      cauchyQuadratic z (head ∷ rest)
      ≡
      (k * z head * z head + (1ℚ + 1ℚ) * z head * s)
      + (beta * s * s
          + cauchyQuadratic (transformedCoefficient head z) rest)
    exposeTail = cong
      (λ selected →
        (k * z head * z head + (1ℚ + 1ℚ) * z head * s) + selected)
      tailSplit

    regroup :
      (k * z head * z head + (1ℚ + 1ℚ) * z head * s)
      + (beta * s * s
          + cauchyQuadratic (transformedCoefficient head z) rest)
      ≡
      (k * z head * z head
        + (1ℚ + 1ℚ) * z head * s
        + beta * s * s)
      + cauchyQuadratic (transformedCoefficient head z) rest
    regroup = solve
      ( k ∷ beta ∷ z head ∷ s
      ∷ cauchyQuadratic (transformedCoefficient head z) rest ∷ [])

    square = completeSquareFromInverse
      k beta (z head) s (headBetaInverseLaw head)
  in
  trans exposeTail
    (trans regroup (cong₂ _+_ square refl))

headPivotNonnegative :
  (head : PositiveRatePoint) →
  (rest : List PositiveRatePoint) →
  (z : PositiveRatePoint → ℚ) →
  0ℚ ≤ headPivot head z rest
headPivotNonnegative head rest z =
  let
    k = cauchyKernel head head
    form = z head + headBeta head * headCoupling head z rest
    kPositive = R443.cauchyEntryPositive
      (rate head) (rate head) (ratePositive head) (ratePositive head)
    kNN = ℚP.<⇒≤ (ℚP.positive⁻¹ k)
    squareNN = Rational.squareNonnegative form
    instance
      kNNI : NonNegative k
      kNNI = nonNegative kNN
      squareNNI : NonNegative (form * form)
      squareNNI = nonNegative squareNN
      productNNI = ℚP.nonNeg*nonNeg⇒nonNeg k (form * form)
    raw : 0ℚ ≤ k * (form * form)
    raw = ℚP.nonNegative⁻¹ (k * (form * form))
    reassociate : k * (form * form) ≡ k * form * form
    reassociate = solve (k ∷ form ∷ [])
  in
  subst (0ℚ ≤_) reassociate raw

finiteCauchyQuadraticNonnegative :
  (items : List PositiveRatePoint) →
  (z : PositiveRatePoint → ℚ) →
  0ℚ ≤ cauchyQuadratic z items
finiteCauchyQuadraticNonnegative [] z = ℚP.≤-refl
finiteCauchyQuadraticNonnegative (head ∷ rest) z =
  let
    pivotNN = headPivotNonnegative head rest z
    tailNN = finiteCauchyQuadraticNonnegative
      rest (transformedCoefficient head z)
    summed = Rational.addNonnegative pivotNN tailNN
  in
  subst
    (0ℚ ≤_)
    (sym (headCauchySchurDecomposition head rest z))
    summed

storedCauchyQuadraticNonnegative :
  (items : List PositiveRatePoint) →
  0ℚ ≤ storedCauchyQuadratic items
storedCauchyQuadraticNonnegative items =
  finiteCauchyQuadraticNonnegative items storedCoefficient

round445FiniteRationalCauchyPSDClosed : Bool
round445FiniteRationalCauchyPSDClosed = true

round445CallerSuppliedSchurDecompositionRequired : Bool
round445CallerSuppliedSchurDecompositionRequired = false

round445ImproperIntegralUsed : Bool
round445ImproperIntegralUsed = false

round445ExponentialUsed : Bool
round445ExponentialUsed = false

round445SpectralTheoremUsed : Bool
round445SpectralTheoremUsed = false

round445PhysicalComplex3LiftClosed : Bool
round445PhysicalComplex3LiftClosed = false

round445PackageAClosed : Bool
round445PackageAClosed = false

round445ClayPromotion : Bool
round445ClayPromotion = false

round445FiniteRationalCauchyPSDClosedIsTrue :
  round445FiniteRationalCauchyPSDClosed ≡ true
round445FiniteRationalCauchyPSDClosedIsTrue = refl

round445CallerSuppliedSchurDecompositionRequiredIsFalse :
  round445CallerSuppliedSchurDecompositionRequired ≡ false
round445CallerSuppliedSchurDecompositionRequiredIsFalse = refl
