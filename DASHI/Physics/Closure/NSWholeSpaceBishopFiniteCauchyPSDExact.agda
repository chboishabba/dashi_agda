module DASHI.Physics.Closure.NSWholeSpaceBishopFiniteCauchyPSDExact where

------------------------------------------------------------------------
-- A / FINITE BISHOP-REAL CAUCHY RESOLVENT PSD
--
-- Bishop-real port of periodic R443--R445.
--
-- For positive rates x_i and arbitrary Bishop-real coefficients z_i,
--
--     Q = sum_{i,j} z_i z_j / (x_i+x_j) >= 0.
--
-- The proof is the exact finite Schur recursion:
--
--   K(a,b)
--     ~= 2 x K(x,a)K(x,b)
--       + d_x(a) K(a,b) d_x(b),
--
--   d_x(a) = (a-x)K(x,a),
--
-- followed by the generic Bishop finite rank-one compiler.  No Laplace
-- transform, improper integral, matrix determinant, square root, or spectral
-- theorem is used.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Data.Rational.Unnormalised using (_/_; +_; Κ)

import Inverse as BishopInverse
import Real as BishopReal
import RealProperties as BishopP

import DASHI.Foundations.BishopGeometricReciprocalSquareFromCrossExact as Reciprocal
import DASHI.Physics.Closure.NSWholeSpaceBishopFiniteKernelRankOneExact as Finite

record PositiveRatePoint : Set where
  constructor positive-rate-point
  field
    rate coefficient : BishopReal.ℝ
    ratePositive : BishopReal._<_ BishopReal.0ℝ rate

open PositiveRatePoint public

sumPositive :
  ∀ {left right} →
  BishopReal._<_ BishopReal.0ℝ left →
  BishopReal._<_ BishopReal.0ℝ right →
  BishopReal._<_ BishopReal.0ℝ (BishopReal._+_ left right)
sumPositive leftPositive rightPositive =
  BishopP.posx⇒0<x
    (BishopP.posx,y⇒posx+y
      (BishopP.0<x⇒posx leftPositive)
      (BishopP.0<x⇒posx rightPositive))

sumNonzero :
  ∀ {left right} →
  BishopReal._<_ BishopReal.0ℝ left →
  BishopReal._<_ BishopReal.0ℝ right →
  BishopReal._≄0 (BishopReal._+_ left right)
sumNonzero leftPositive rightPositive =
  Reciprocal.xNonzero
    (sumPositive leftPositive rightPositive)

cauchyEntry :
  PositiveRatePoint →
  PositiveRatePoint →
  BishopReal.ℝ
cauchyEntry left right =
  BishopInverse._⁻¹
    (BishopReal._+_ (rate left) (rate right))
    (sumNonzero (ratePositive left) (ratePositive right))

cauchyEntryInverseLaw :
  (left right : PositiveRatePoint) →
  BishopReal._≃_
    (BishopReal._*_
      (cauchyEntry left right)
      (BishopReal._+_ (rate left) (rate right)))
    BishopReal.1ℝ
cauchyEntryInverseLaw left right =
  BishopInverse.*-inverseˡ
    (BishopReal._+_ (rate left) (rate right))
    (sumNonzero (ratePositive left) (ratePositive right))

cauchyEntryPositive :
  (left right : PositiveRatePoint) →
  BishopReal._<_ BishopReal.0ℝ (cauchyEntry left right)
cauchyEntryPositive left right =
  BishopInverse.0<x⇒0<x⁻¹
    (sumNonzero (ratePositive left) (ratePositive right))
    (sumPositive (ratePositive left) (ratePositive right))

cauchyEntryNonnegative :
  (left right : PositiveRatePoint) →
  BishopReal.NonNegative (cauchyEntry left right)
cauchyEntryNonnegative left right =
  BishopP.pos⇒nonNeg
    (BishopP.0<x⇒posx
      (cauchyEntryPositive left right))

cauchyQuadratic :
  (PositiveRatePoint → BishopReal.ℝ) →
  List PositiveRatePoint →
  BishopReal.ℝ
cauchyQuadratic = Finite.quadraticForm cauchyEntry

storedCauchyQuadratic :
  List PositiveRatePoint → BishopReal.ℝ
storedCauchyQuadratic =
  cauchyQuadratic coefficient

headBeta : PositiveRatePoint → BishopReal.ℝ
headBeta head =
  BishopReal._*_
    (BishopReal._+_ BishopReal.1ℝ BishopReal.1ℝ)
    (rate head)

headU :
  PositiveRatePoint →
  PositiveRatePoint →
  BishopReal.ℝ
headU head cell = cauchyEntry head cell

headD :
  PositiveRatePoint →
  PositiveRatePoint →
  BishopReal.ℝ
headD head cell =
  BishopReal._*_
    (BishopReal._-_ (rate cell) (rate head))
    (cauchyEntry head cell)

transformedCoefficient :
  PositiveRatePoint →
  (PositiveRatePoint → BishopReal.ℝ) →
  PositiveRatePoint →
  BishopReal.ℝ
transformedCoefficient head z cell =
  BishopReal._*_ (headD head cell) (z cell)

headCoupling :
  PositiveRatePoint →
  (PositiveRatePoint → BishopReal.ℝ) →
  List PositiveRatePoint →
  BishopReal.ℝ
headCoupling head z rest =
  Finite.linearSum (headU head) z rest

headPivot :
  PositiveRatePoint →
  (PositiveRatePoint → BishopReal.ℝ) →
  List PositiveRatePoint →
  BishopReal.ℝ
headPivot head z rest =
  let
    form =
      BishopReal._+_
        (z head)
        (BishopReal._*_
          (headBeta head)
          (headCoupling head z rest))
  in
  BishopReal._*_
    (cauchyEntry head head)
    (BishopReal._*_ form form)

------------------------------------------------------------------------
-- Exact Schur entry identity.
------------------------------------------------------------------------

headKernelSplit :
  (head left right : PositiveRatePoint) →
  BishopReal._≃_
    (cauchyEntry left right)
    (BishopReal._+_
      (BishopReal._*_
        (headBeta head)
        (BishopReal._*_
          (headU head left)
          (headU head right)))
      (Finite.scaledKernel
        cauchyEntry
        (headD head)
        left right))
headKernelSplit head left right =
  let
    x = rate head
    a = rate left
    b = rate right
    kxa = cauchyEntry head left
    kxb = cauchyEntry head right
    kab = cauchyEntry left right

    lawXA = cauchyEntryInverseLaw head left
    lawXB = cauchyEntryInverseLaw head right

    rhs =
      BishopReal._+_
        (BishopReal._*_
          (headBeta head)
          (BishopReal._*_ kxa kxb))
        (Finite.scaledKernel
          cauchyEntry
          (headD head)
          left right)

    open BishopP.ℝ-Solver

    factor :
      BishopReal._≃_
        rhs
        (BishopReal._*_
          (BishopReal._*_
            (BishopReal._*_
              kxa
              (BishopReal._+_ x a))
            (BishopReal._*_
              kxb
              (BishopReal._+_ x b)))
          kab)
    factor =
      solve 6
        (λ x' a' b' kxa' kxb' kab' →
          ((Κ (+ 2 / 1) ⊗ x') ⊗ (kxa' ⊗ kxb'))
          ⊕
          (((a' ⊖ x') ⊗ kxa')
            ⊗
            (kab' ⊗ ((b' ⊖ x') ⊗ kxb')))
          ⊜
          ((kxa' ⊗ (x' ⊕ a'))
            ⊗
            (kxb' ⊗ (x' ⊕ b')))
            ⊗ kab')
        BishopP.≃-refl
        x a b kxa kxb kab
  in
  BishopP.≃-symm
    (BishopP.≃-trans
      factor
      (BishopP.≃-trans
        (BishopP.*-cong
          (BishopP.*-cong lawXA lawXB)
          BishopP.≃-refl)
        (BishopP.*-identityˡ kab)))

------------------------------------------------------------------------
-- Complete square and recursive PSD.
------------------------------------------------------------------------

headBetaInverseLaw :
  (head : PositiveRatePoint) →
  BishopReal._≃_
    (BishopReal._*_
      (cauchyEntry head head)
      (headBeta head))
    BishopReal.1ℝ
headBetaInverseLaw head =
  let
    x = rate head
    k = cauchyEntry head head
    base = cauchyEntryInverseLaw head head
    betaMeaning :
      BishopReal._≃_
        (headBeta head)
        (BishopReal._+_ x x)
    betaMeaning =
      let open BishopP.ℝ-Solver
      in solve 1
        (λ x' →
          (Κ (+ 2 / 1) ⊗ x')
          ⊜ x' ⊕ x')
        BishopP.≃-refl x
  in
  BishopP.≃-trans
    (BishopP.*-congˡ betaMeaning)
    base

completeSquareFromInverse :
  (k beta z s : BishopReal.ℝ) →
  BishopReal._≃_ (BishopReal._*_ k beta) BishopReal.1ℝ →
  BishopReal._≃_
    (BishopReal._+_
      (BishopReal._+_
        (BishopReal._*_
          (BishopReal._*_ k z) z)
        (BishopReal._*_
          (BishopReal._+_ BishopReal.1ℝ BishopReal.1ℝ)
          (BishopReal._*_ z s)))
      (BishopReal._*_
        (BishopReal._*_ beta s) s))
    (BishopReal._*_
      (BishopReal._*_ k
        (BishopReal._+_
          z
          (BishopReal._*_ beta s)))
      (BishopReal._+_
        z
        (BishopReal._*_ beta s)))
completeSquareFromInverse k beta z s inverseLaw =
  let open BishopP.ℝ-Solver
  in
  BishopP.≃-trans
    (solve 4
      (λ k' b' z' s' →
        ((k' ⊗ z') ⊗ z')
        ⊕ ((Κ (+ 2 / 1) ⊗ z') ⊗ s')
        ⊕ ((b' ⊗ s') ⊗ s')
        ⊜
        ((k' ⊗ z') ⊗ z')
        ⊕
        ((Κ (+ 2 / 1) ⊗ (k' ⊗ b'))
          ⊗ (z' ⊗ s'))
        ⊕
        (((k' ⊗ b') ⊗ b')
          ⊗ (s' ⊗ s')))
      BishopP.≃-refl
      k beta z s)
    (BishopP.≃-trans
      (BishopP.+-cong
        (BishopP.+-cong
          BishopP.≃-refl
          (BishopP.*-cong
            BishopP.≃-refl
            (BishopP.*-cong
              inverseLaw BishopP.≃-refl)))
        (BishopP.*-cong
          (BishopP.*-cong
            inverseLaw BishopP.≃-refl)
          BishopP.≃-refl))
      (let open BishopP.ℝ-Solver
       in solve 4
        (λ k' b' z' s' →
          ((k' ⊗ z') ⊗ z')
          ⊕ ((Κ (+ 2 / 1) ⊗ z') ⊗ s')
          ⊕ ((b' ⊗ s') ⊗ s')
          ⊜
          (k' ⊗ (z' ⊕ (b' ⊗ s')))
            ⊗ (z' ⊕ (b' ⊗ s')))
        BishopP.≃-refl
        k beta z s))

tailCauchySchurSplit :
  (head : PositiveRatePoint) →
  (z : PositiveRatePoint → BishopReal.ℝ) →
  (rest : List PositiveRatePoint) →
  BishopReal._≃_
    (cauchyQuadratic z rest)
    (BishopReal._+_
      (BishopReal._*_
        (headBeta head)
        (BishopReal._*_
          (headCoupling head z rest)
          (headCoupling head z rest)))
      (cauchyQuadratic
        (transformedCoefficient head z)
        rest))
tailCauchySchurSplit head z rest =
  BishopP.≃-trans
    (Finite.quadraticRankOneSplit
      cauchyEntry
      (Finite.scaledKernel cauchyEntry (headD head))
      (headU head)
      z
      (headBeta head)
      (headKernelSplit head)
      rest)
    (BishopP.+-cong
      BishopP.≃-refl
      (Finite.quadraticDiagonalScaling
        cauchyEntry
        (headD head)
        z
        rest))

headCauchySchurDecomposition :
  (head : PositiveRatePoint) →
  (rest : List PositiveRatePoint) →
  (z : PositiveRatePoint → BishopReal.ℝ) →
  BishopReal._≃_
    (cauchyQuadratic z (head ∷ rest))
    (BishopReal._+_
      (headPivot head z rest)
      (cauchyQuadratic
        (transformedCoefficient head z)
        rest))
headCauchySchurDecomposition head rest z =
  let
    k = cauchyEntry head head
    beta = headBeta head
    s = headCoupling head z rest
    tail = tailCauchySchurSplit head z rest
    square =
      completeSquareFromInverse
        k beta (z head) s
        (headBetaInverseLaw head)
    open BishopP.ℝ-Solver
  in
  BishopP.≃-trans
    (BishopP.+-cong
      BishopP.≃-refl
      tail)
    (BishopP.≃-trans
      (solve 5
        (λ a b c d e →
          (a ⊕ b) ⊕ (c ⊕ d)
          ⊜ (a ⊕ b ⊕ c) ⊕ d)
        BishopP.≃-refl
        (BishopReal._*_
          (BishopReal._*_ k (z head))
          (z head))
        (BishopReal._*_
          (BishopReal._+_ BishopReal.1ℝ BishopReal.1ℝ)
          (BishopReal._*_
            (z head) s))
        (BishopReal._*_
          (BishopReal._*_ beta s) s)
        (cauchyQuadratic
          (transformedCoefficient head z)
          rest)
        BishopReal.0ℝ)
      (BishopP.+-cong square BishopP.≃-refl))

headPivotNonnegative :
  (head : PositiveRatePoint) →
  (rest : List PositiveRatePoint) →
  (z : PositiveRatePoint → BishopReal.ℝ) →
  BishopReal.NonNegative (headPivot head z rest)
headPivotNonnegative head rest z =
  let
    form =
      BishopReal._+_
        (z head)
        (BishopReal._*_
          (headBeta head)
          (headCoupling head z rest))
  in
  BishopP.nonNegx,y⇒nonNegx*y
    (cauchyEntryNonnegative head head)
    (BishopP.nonNegSquare form)

finiteCauchyQuadraticNonnegative :
  (items : List PositiveRatePoint) →
  (z : PositiveRatePoint → BishopReal.ℝ) →
  BishopReal.NonNegative (cauchyQuadratic z items)
finiteCauchyQuadraticNonnegative [] z =
  BishopP.0≤x⇒nonNegx BishopP.≤-refl
finiteCauchyQuadraticNonnegative (head ∷ rest) z =
  let
    pivotNN = headPivotNonnegative head rest z
    tailNN =
      finiteCauchyQuadraticNonnegative
        rest
        (transformedCoefficient head z)
    sumNN =
      BishopP.nonNegx,y⇒nonNegx+y
        pivotNN tailNN
  in
  BishopP.0≤x⇒nonNegx
    (BishopP.≤-respʳ-≃
      (BishopP.≃-symm
        (headCauchySchurDecomposition
          head rest z))
      (BishopP.nonNegx⇒0≤x sumNN))

storedCauchyQuadraticNonnegative :
  (items : List PositiveRatePoint) →
  BishopReal.NonNegative
    (storedCauchyQuadratic items)
storedCauchyQuadraticNonnegative items =
  finiteCauchyQuadraticNonnegative
    items coefficient

finiteBishopCauchyPSDClosed : Bool
finiteBishopCauchyPSDClosed = true

callerSuppliedSchurDecompositionRequired : Bool
callerSuppliedSchurDecompositionRequired = false

laplaceRepresentationUsed : Bool
laplaceRepresentationUsed = false

improperIntegralUsed : Bool
improperIntegralUsed = false

spectralTheoremUsed : Bool
spectralTheoremUsed = false

continuumLimitTakenHere : Bool
continuumLimitTakenHere = false

clayPromotion : Bool
clayPromotion = false

finiteBishopCauchyPSDClosedIsTrue :
  finiteBishopCauchyPSDClosed ≡ true
finiteBishopCauchyPSDClosedIsTrue = refl

callerSuppliedSchurDecompositionRequiredIsFalse :
  callerSuppliedSchurDecompositionRequired ≡ false
callerSuppliedSchurDecompositionRequiredIsFalse = refl

laplaceRepresentationUsedIsFalse :
  laplaceRepresentationUsed ≡ false
laplaceRepresentationUsedIsFalse = refl

continuumLimitTakenHereIsFalse :
  continuumLimitTakenHere ≡ false
continuumLimitTakenHereIsFalse = refl

clayPromotionIsFalse : clayPromotion ≡ false
clayPromotionIsFalse = refl
