module DASHI.Physics.Closure.NSWholeSpaceBishopFiniteCauchyPSDExact where

------------------------------------------------------------------------
-- A / FINITE BISHOP-REAL CAUCHY RESOLVENT PSD
--
-- Port the exact finite Schur-complement mechanism of R443--R445 from the
-- periodic rational backend to the Bishop-real backend used by whole-space A.
--
-- For positive rates lambda_i and arbitrary Bishop-real coefficients z_i,
--
--        Q = sum_{i,j} z_i z_j / (lambda_i + lambda_j) >= 0.
--
-- No Laplace representation, improper integral, spectral theorem, square root,
-- or measure theory is used.  This is finite ordered-field algebra only.
--
-- Consequently every finite/simple-function approximation of A's continuous
-- Cauchy-resolvent Gram form can carry a theorem-level nonnegative certificate
-- before the continuum/measure limit is taken.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Data.Rational.Unnormalised using (_/_; +_; Κ)

import Inverse as BishopInverse
import Real as BishopReal
import RealProperties as BishopP

import DASHI.Foundations.BishopGeometricReciprocalSquareFromCrossExact as Reciprocal

two : BishopReal.ℝ
two = BishopReal._+_ BishopReal.1ℝ BishopReal.1ℝ

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
  Reciprocal.xNonzero (sumPositive leftPositive rightPositive)

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
  BishopReal._<_ BishopReal.0ℝ
    (cauchyEntry left right)
cauchyEntryPositive left right =
  BishopInverse.0<x⇒0<x⁻¹
    (sumNonzero (ratePositive left) (ratePositive right))
    (sumPositive (ratePositive left) (ratePositive right))

cauchyEntryNonnegative :
  (left right : PositiveRatePoint) →
  BishopReal.NonNegative (cauchyEntry left right)
cauchyEntryNonnegative left right =
  BishopP.pos⇒nonNeg
    (BishopP.0<x⇒posx (cauchyEntryPositive left right))

linearSum :
  (PositiveRatePoint → BishopReal.ℝ) →
  (PositiveRatePoint → BishopReal.ℝ) →
  List PositiveRatePoint →
  BishopReal.ℝ
linearSum u z [] = BishopReal.0ℝ
linearSum u z (cell ∷ rest) =
  BishopReal._+_
    (BishopReal._*_ (u cell) (z cell))
    (linearSum u z rest)

quadraticForm :
  (PositiveRatePoint → PositiveRatePoint → BishopReal.ℝ) →
  (PositiveRatePoint → BishopReal.ℝ) →
  List PositiveRatePoint →
  BishopReal.ℝ
quadraticForm kernel z [] = BishopReal.0ℝ
quadraticForm kernel z (head ∷ rest) =
  BishopReal._+_
    (BishopReal._+_
      (BishopReal._*_
        (kernel head head)
        (BishopReal._*_ (z head) (z head)))
      (BishopReal._*_
        two
        (BishopReal._*_
          (z head)
          (linearSum (kernel head) z rest))))
    (quadraticForm kernel z rest)

cauchyQuadratic :
  (PositiveRatePoint → BishopReal.ℝ) →
  List PositiveRatePoint →
  BishopReal.ℝ
cauchyQuadratic = quadraticForm cauchyEntry

headBeta : PositiveRatePoint → BishopReal.ℝ
headBeta head = BishopReal._*_ two (rate head)

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
  linearSum (headU head) z rest

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
      (BishopReal._*_
        (headD head left)
        (BishopReal._*_
          (cauchyEntry left right)
          (headD head right))))
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
    lawAB = cauchyEntryInverseLaw left right

    open BishopP.ℝ-Solver

    algebra :
      BishopReal._≃_
        (BishopReal._+_
          (BishopReal._*_
            (headBeta head)
            (BishopReal._*_ kxa kxb))
          (BishopReal._*_
            (headD head left)
            (BishopReal._*_ kab (headD head right))))
        kab
    algebra =
      BishopP.≃-trans
        (solve 6
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
          x a b kxa kxb kab)
        (BishopP.≃-trans
          (BishopP.*-cong
            (BishopP.*-cong lawXA lawXB)
            BishopP.≃-refl)
          (BishopP.*-identityˡ kab))
  in
  BishopP.≃-symm algebra

scaledKernel :
  (PositiveRatePoint → PositiveRatePoint → BishopReal.ℝ) →
  (PositiveRatePoint → BishopReal.ℝ) →
  PositiveRatePoint →
  PositiveRatePoint →
  BishopReal.ℝ
scaledKernel kernel scale left right =
  BishopReal._*_
    (scale left)
    (BishopReal._*_
      (kernel left right)
      (scale right))

scaledQuadratic :
  (kernel : PositiveRatePoint → PositiveRatePoint → BishopReal.ℝ) →
  (scale z : PositiveRatePoint → BishopReal.ℝ) →
  (items : List PositiveRatePoint) →
  BishopReal._≃_
    (quadraticForm (scaledKernel kernel scale) z items)
    (quadraticForm kernel
      (λ cell → BishopReal._*_ (scale cell) (z cell))
      items)
scaledQuadratic kernel scale z [] = BishopP.≃-refl
scaledQuadratic kernel scale z (head ∷ rest) =
  let
    tail = scaledQuadratic kernel scale z rest
    row :
      BishopReal._≃_
        (linearSum
          (scaledKernel kernel scale head)
          z rest)
        (BishopReal._*_
          (scale head)
          (linearSum kernel
            (λ cell → BishopReal._*_ (scale cell) (z cell))
            rest))
    row = scaledRow kernel scale z head rest
    open BishopP.ℝ-Solver
  in
  BishopP.≃-trans
    (BishopP.+-cong
      (BishopP.+-cong
        (solve 3
          (λ khh sh zh →
            (sh ⊗ (khh ⊗ sh)) ⊗ (zh ⊗ zh)
            ⊜
            khh ⊗ ((sh ⊗ zh) ⊗ (sh ⊗ zh)))
          BishopP.≃-refl
          (kernel head head) (scale head) (z head))
        (BishopP.*-congˡ
          (BishopP.*-cong
            BishopP.≃-refl
            (BishopP.*-congˡ row))))
      tail)
    BishopP.≃-refl
  where
  scaledRow :
    (kernel : PositiveRatePoint → PositiveRatePoint → BishopReal.ℝ) →
    (scale z : PositiveRatePoint → BishopReal.ℝ) →
    (head : PositiveRatePoint) →
    (rest : List PositiveRatePoint) →
    BishopReal._≃_
      (linearSum
        (scaledKernel kernel scale head)
        z rest)
      (BishopReal._*_
        (scale head)
        (linearSum kernel
          (λ cell → BishopReal._*_ (scale cell) (z cell))
          rest))
  scaledRow kernel scale z head [] =
    BishopP.≃-symm (BishopP.*-zeroʳ (scale head))
  scaledRow kernel scale z head (cell ∷ rest) =
    let
      tail = scaledRow kernel scale z head rest
      open BishopP.ℝ-Solver
    in
    BishopP.≃-trans
      (BishopP.+-cong
        (solve 4
          (λ sh sc k zc →
            (sh ⊗ (k ⊗ sc)) ⊗ zc
            ⊜ sh ⊗ (k ⊗ (sc ⊗ zc)))
          BishopP.≃-refl
          (scale head) (scale cell)
          (kernel head cell) (z cell))
        tail)
      (BishopP.≃-symm
        (BishopP.*-distribˡ-+
          (scale head)
          (BishopReal._*_
            (kernel head cell)
            (BishopReal._*_
              (scale cell) (z cell)))
          (linearSum kernel
            (λ selected →
              BishopReal._*_
                (scale selected) (z selected))
            rest)))

rankOneQuadraticSplit :
  (kernel residual :
    PositiveRatePoint → PositiveRatePoint → BishopReal.ℝ) →
  (u z : PositiveRatePoint → BishopReal.ℝ) →
  (beta : BishopReal.ℝ) →
  ((left right : PositiveRatePoint) →
    BishopReal._≃_
      (kernel left right)
      (BishopReal._+_
        (BishopReal._*_
          beta
          (BishopReal._*_
            (u left) (u right)))
        (residual left right))) →
  (items : List PositiveRatePoint) →
  BishopReal._≃_
    (quadraticForm kernel z items)
    (BishopReal._+_
      (BishopReal._*_
        beta
        (BishopReal._*_
          (linearSum u z items)
          (linearSum u z items)))
      (quadraticForm residual z items))
rankOneQuadraticSplit kernel residual u z beta split [] =
  let open BishopP.ℝ-Solver
  in solve 1
    (λ b → Κ (+ 0 / 1) ⊜ (b ⊗ (Κ (+ 0 / 1) ⊗ Κ (+ 0 / 1))) ⊕ Κ (+ 0 / 1))
    BishopP.≃-refl beta
rankOneQuadraticSplit kernel residual u z beta split (head ∷ rest) =
  let
    tail = rankOneQuadraticSplit kernel residual u z beta split rest
    row = rankOneRowSplit kernel residual u z beta split head rest
    open BishopP.ℝ-Solver
  in
  BishopP.≃-trans
    (BishopP.+-cong
      (BishopP.+-cong
        (BishopP.*-congˡ
          (BishopP.*-congˡ
            (split head head)))
        (BishopP.*-congˡ
          (BishopP.*-congˡ row)))
      tail)
    (solve 6
      (λ b uh zh su sr q →
        (((b ⊗ (uh ⊗ uh)) ⊕ sr)
          ⊗ (zh ⊗ zh))
        ⊕
        ((Κ (+ 2 / 1) ⊗ zh)
          ⊗ ((b ⊗ (uh ⊗ su)) ⊕ sr))
        ⊕
        ((b ⊗ (su ⊗ su)) ⊕ q)
        ⊜
        (b ⊗ ((uh ⊗ zh ⊕ su) ⊗ (uh ⊗ zh ⊕ su)))
        ⊕
        (sr ⊗ (zh ⊗ zh)
          ⊕ (Κ (+ 2 / 1) ⊗ zh) ⊗ sr
          ⊕ q))
      BishopP.≃-refl
      beta (u head) (z head)
      (linearSum u z rest)
      (linearSum (residual head) z rest)
      (quadraticForm residual z rest))
  where
  rankOneRowSplit :
    (kernel residual :
      PositiveRatePoint → PositiveRatePoint → BishopReal.ℝ) →
    (u z : PositiveRatePoint → BishopReal.ℝ) →
    (beta : BishopReal.ℝ) →
    ((left right : PositiveRatePoint) →
      BishopReal._≃_
        (kernel left right)
        (BishopReal._+_
          (BishopReal._*_
            beta
            (BishopReal._*_
              (u left) (u right)))
          (residual left right))) →
    (head : PositiveRatePoint) →
    (rest : List PositiveRatePoint) →
    BishopReal._≃_
      (linearSum (kernel head) z rest)
      (BishopReal._+_
        (BishopReal._*_
          beta
          (BishopReal._*_
            (u head)
            (linearSum u z rest)))
        (linearSum (residual head) z rest))
  rankOneRowSplit kernel residual u z beta split head [] =
    let open BishopP.ℝ-Solver
    in solve 2
      (λ b uh →
        Κ (+ 0 / 1)
        ⊜ (b ⊗ (uh ⊗ Κ (+ 0 / 1))) ⊕ Κ (+ 0 / 1))
      BishopP.≃-refl beta (u head)
  rankOneRowSplit kernel residual u z beta split head (cell ∷ rest) =
    let
      tail =
        rankOneRowSplit kernel residual u z beta split head rest
      open BishopP.ℝ-Solver
    in
    BishopP.≃-trans
      (BishopP.+-cong
        (BishopP.*-congˡ (split head cell))
        tail)
      (solve 6
        (λ b uh uc zc su sr →
          ((b ⊗ (uh ⊗ uc) ⊕ sr) ⊗ zc)
          ⊕
          ((b ⊗ (uh ⊗ su)) ⊕ sr)
          ⊜
          (b ⊗
            (uh ⊗ ((uc ⊗ zc) ⊕ su)))
          ⊕ ((sr ⊗ zc) ⊕ sr))
        BishopP.≃-refl
        beta (u head) (u cell) (z cell)
        (linearSum u z rest)
        (linearSum (residual head) z rest))

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
    (rankOneQuadraticSplit
      cauchyEntry
      (scaledKernel cauchyEntry (headD head))
      (headU head)
      z
      (headBeta head)
      (headKernelSplit head)
      rest)
    (BishopP.+-cong
      BishopP.≃-refl
      (scaledQuadratic cauchyEntry (headD head) z rest))

headBetaInverseLaw :
  (head : PositiveRatePoint) →
  BishopReal._≃_
    (BishopReal._*_
      (cauchyEntry head head)
      (headBeta head))
    BishopReal.1ℝ
headBetaInverseLaw head =
  let open BishopP.ℝ-Solver
      base = cauchyEntryInverseLaw head head
  in
  BishopP.≃-trans
    (BishopP.*-congˡ
      (solve 1
        (λ x → Κ (+ 2 / 1) ⊗ x ⊜ x ⊕ x)
        BishopP.≃-refl
        (rate head)))
    base

completeSquare :
  (head : PositiveRatePoint) →
  (z : PositiveRatePoint → BishopReal.ℝ) →
  (rest : List PositiveRatePoint) →
  BishopReal._≃_
    (BishopReal._+_
      (BishopReal._+_
        (BishopReal._*_
          (cauchyEntry head head)
          (BishopReal._*_ (z head) (z head)))
        (BishopReal._*_
          two
          (BishopReal._*_
            (z head)
            (headCoupling head z rest))))
      (BishopReal._*_
        (headBeta head)
        (BishopReal._*_
          (headCoupling head z rest)
          (headCoupling head z rest))))
    (headPivot head z rest)
completeSquare head z rest =
  let
    k = cauchyEntry head head
    beta = headBeta head
    zz = z head
    s = headCoupling head z rest
    inverseLaw = headBetaInverseLaw head
    open BishopP.ℝ-Solver
  in
  BishopP.≃-trans
    (solve 4
      (λ k' b' z' s' →
        (k' ⊗ (z' ⊗ z'))
        ⊕ (Κ (+ 2 / 1) ⊗ (z' ⊗ s'))
        ⊕ (b' ⊗ (s' ⊗ s'))
        ⊜
        (k' ⊗ (z' ⊗ z'))
        ⊕
        ((Κ (+ 2 / 1) ⊗ (k' ⊗ b')) ⊗ (z' ⊗ s'))
        ⊕
        (((k' ⊗ b') ⊗ b') ⊗ (s' ⊗ s')))
      BishopP.≃-refl k beta zz s)
    (BishopP.≃-trans
      (BishopP.+-cong
        (BishopP.+-cong
          BishopP.≃-refl
          (BishopP.*-congˡ
            (BishopP.*-cong
              BishopP.≃-refl inverseLaw)))
        (BishopP.*-congˡ
          (BishopP.*-congˡ inverseLaw)))
      (let open BishopP.ℝ-Solver
       in solve 4
        (λ k' b' z' s' →
          (k' ⊗ (z' ⊗ z'))
          ⊕ (Κ (+ 2 / 1) ⊗ (z' ⊗ s'))
          ⊕ (b' ⊗ (s' ⊗ s'))
          ⊜
          k' ⊗ ((z' ⊕ (b' ⊗ s')) ⊗
                 (z' ⊕ (b' ⊗ s'))))
        BishopP.≃-refl k beta zz s))

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
    tail = tailCauchySchurSplit head z rest
    open BishopP.ℝ-Solver
  in
  BishopP.≃-trans
    (BishopP.+-cong
      BishopP.≃-refl
      tail)
    (BishopP.≃-trans
      (solve 4
        (λ a b c d →
          (a ⊕ b) ⊕ (c ⊕ d)
          ⊜ (a ⊕ b ⊕ c) ⊕ d)
        BishopP.≃-refl
        (BishopReal._*_
          (cauchyEntry head head)
          (BishopReal._*_ (z head) (z head)))
        (BishopReal._*_
          two
          (BishopReal._*_
            (z head) (headCoupling head z rest)))
        (BishopReal._*_
          (headBeta head)
          (BishopReal._*_
            (headCoupling head z rest)
            (headCoupling head z rest)))
        (cauchyQuadratic
          (transformedCoefficient head z)
          rest))
      (BishopP.+-cong
        (completeSquare head z rest)
        BishopP.≃-refl))

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
    sumNN = BishopP.nonNegx,y⇒nonNegx+y pivotNN tailNN
  in
  BishopP.0≤x⇒nonNegx
    (BishopP.≤-respʳ-≃
      (BishopP.≃-symm
        (headCauchySchurDecomposition head rest z))
      (BishopP.nonNegx⇒0≤x sumNN))

storedCauchyQuadratic :
  List PositiveRatePoint → BishopReal.ℝ
storedCauchyQuadratic items =
  cauchyQuadratic coefficient items

storedCauchyQuadraticNonnegative :
  (items : List PositiveRatePoint) →
  BishopReal.NonNegative (storedCauchyQuadratic items)
storedCauchyQuadraticNonnegative items =
  finiteCauchyQuadraticNonnegative items coefficient

finiteBishopCauchyPSDClosed : Bool
finiteBishopCauchyPSDClosed = true

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

laplaceRepresentationUsedIsFalse :
  laplaceRepresentationUsed ≡ false
laplaceRepresentationUsedIsFalse = refl

continuumLimitTakenHereIsFalse :
  continuumLimitTakenHere ≡ false
continuumLimitTakenHereIsFalse = refl

clayPromotionIsFalse : clayPromotion ≡ false
clayPromotionIsFalse = refl
