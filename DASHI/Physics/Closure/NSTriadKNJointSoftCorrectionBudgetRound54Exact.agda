module DASHI.Physics.Closure.NSTriadKNJointSoftCorrectionBudgetRound54Exact where

------------------------------------------------------------------------
-- PRIMARY SOURCES / CONTEXT
--
-- Author: William Henry Young.
-- Title: "On the Multiplication of Successions of Fourier Constants".
-- DOI: 10.1098/rspa.1912.0086.
--
-- Authors: Augustin-Louis Cauchy; Hermann Amandus Schwarz.
-- Result: Cauchy--Schwarz inequality; classical result, no DOI applicable.
--
-- DASHI CONTRIBUTION
--
-- Round 53 proves that soft-owner critical coefficients enter the fixed-shift
-- correction through their SUM.  Therefore their globally admissible Young
-- splits must be allocated jointly.
--
-- On the repository's exact rational carrier we avoid introducing irrational
-- square roots.  For three soft channels with division-free Young numerators
--
--   c_i <= epsilon_i B_i,
--
-- this module proves the exact joint necessary condition
--
--   c_Com + c_kernel + c_HHg
--     <= (epsilon_Com + epsilon_kernel + epsilon_HHg)
--          (B_Com + B_kernel + B_HHg).
--
-- Hence an aggregate correction cap B_soft <= B_* implies the immediate
-- rational kill-test
--
--   c_total <= epsilon_total B_*.
--
-- Over the real carrier the sharper optimizer is
--   epsilon_total >= (sum sqrt(c_i))^2 / B_*.
-- That sharpening is intentionally not faked in Q when the c_i do not possess
-- rational square roots (notably c_Com = 133/1024).
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using ([]; _∷_)
open import Data.Rational.Base using (ℚ; 0ℚ; _+_; _*_; _≤_; nonNegative)
import Data.Rational.Properties as ℚP
open import Data.Rational.Tactic.RingSolver using (solve)
open import Relation.Binary.PropositionalEquality using (subst; sym)

nonnegativeProduct :
  ∀ {left right : ℚ} →
  0ℚ ≤ left → 0ℚ ≤ right → 0ℚ ≤ left * right
nonnegativeProduct {left} {right} leftNN rightNN =
  let
    instance
      leftNNI = nonNegative leftNN
      rightNNI = nonNegative rightNN
      productNNI = ℚP.nonNeg*nonNeg⇒nonNeg left right
  in
  ℚP.nonNegative⁻¹ (left * right)

addNonnegative :
  ∀ {left right : ℚ} →
  0ℚ ≤ left → 0ℚ ≤ right → 0ℚ ≤ left + right
addNonnegative {left} leftNN rightNN =
  subst
    (λ lower → lower ≤ left + _)
    (sym (ℚP.+-identityʳ left))
    (ℚP.+-monoʳ-≤ left rightNN)

record ThreeSoftYoungAllocation : Set where
  field
    epsilonCom epsilonKernel epsilonHHGood : ℚ
    bCom bKernel bHHGood : ℚ
    cCom cKernel cHHGood : ℚ

    epsilonComNonnegative : 0ℚ ≤ epsilonCom
    epsilonKernelNonnegative : 0ℚ ≤ epsilonKernel
    epsilonHHGoodNonnegative : 0ℚ ≤ epsilonHHGood

    bComNonnegative : 0ℚ ≤ bCom
    bKernelNonnegative : 0ℚ ≤ bKernel
    bHHGoodNonnegative : 0ℚ ≤ bHHGood

    comYoungCleared : cCom ≤ epsilonCom * bCom
    kernelYoungCleared : cKernel ≤ epsilonKernel * bKernel
    hhGoodYoungCleared : cHHGood ≤ epsilonHHGood * bHHGood

open ThreeSoftYoungAllocation public

softEtaTotal : ThreeSoftYoungAllocation → ℚ
softEtaTotal allocation =
  epsilonCom allocation
  + epsilonKernel allocation
  + epsilonHHGood allocation

softCriticalTotal : ThreeSoftYoungAllocation → ℚ
softCriticalTotal allocation =
  bCom allocation
  + bKernel allocation
  + bHHGood allocation

softNumeratorTotal : ThreeSoftYoungAllocation → ℚ
softNumeratorTotal allocation =
  cCom allocation
  + cKernel allocation
  + cHHGood allocation

softEtaTotalNonnegative :
  (allocation : ThreeSoftYoungAllocation) →
  0ℚ ≤ softEtaTotal allocation
softEtaTotalNonnegative allocation =
  addNonnegative
    (addNonnegative
      (epsilonComNonnegative allocation)
      (epsilonKernelNonnegative allocation))
    (epsilonHHGoodNonnegative allocation)

softCriticalTotalNonnegative :
  (allocation : ThreeSoftYoungAllocation) →
  0ℚ ≤ softCriticalTotal allocation
softCriticalTotalNonnegative allocation =
  addNonnegative
    (addNonnegative
      (bComNonnegative allocation)
      (bKernelNonnegative allocation))
    (bHHGoodNonnegative allocation)

sumYoungNumeratorsBelowDiagonalProducts :
  (allocation : ThreeSoftYoungAllocation) →
  softNumeratorTotal allocation
  ≤ epsilonCom allocation * bCom allocation
    + epsilonKernel allocation * bKernel allocation
    + epsilonHHGood allocation * bHHGood allocation
sumYoungNumeratorsBelowDiagonalProducts allocation =
  ℚP.+-mono-≤
    (ℚP.+-mono-≤
      (comYoungCleared allocation)
      (kernelYoungCleared allocation))
    (hhGoodYoungCleared allocation)

crossProductsNonnegative :
  (allocation : ThreeSoftYoungAllocation) →
  0ℚ ≤
    epsilonCom allocation * bKernel allocation
    + epsilonCom allocation * bHHGood allocation
    + epsilonKernel allocation * bCom allocation
    + epsilonKernel allocation * bHHGood allocation
    + epsilonHHGood allocation * bCom allocation
    + epsilonHHGood allocation * bKernel allocation
crossProductsNonnegative allocation =
  addNonnegative
    (addNonnegative
      (addNonnegative
        (addNonnegative
          (addNonnegative
            (nonnegativeProduct
              (epsilonComNonnegative allocation)
              (bKernelNonnegative allocation))
            (nonnegativeProduct
              (epsilonComNonnegative allocation)
              (bHHGoodNonnegative allocation)))
          (nonnegativeProduct
            (epsilonKernelNonnegative allocation)
            (bComNonnegative allocation)))
        (nonnegativeProduct
          (epsilonKernelNonnegative allocation)
          (bHHGoodNonnegative allocation)))
      (nonnegativeProduct
        (epsilonHHGoodNonnegative allocation)
        (bComNonnegative allocation)))
    (nonnegativeProduct
      (epsilonHHGoodNonnegative allocation)
      (bKernelNonnegative allocation))

diagonalProductsBelowProductOfTotals :
  (allocation : ThreeSoftYoungAllocation) →
  epsilonCom allocation * bCom allocation
    + epsilonKernel allocation * bKernel allocation
    + epsilonHHGood allocation * bHHGood allocation
  ≤ softEtaTotal allocation * softCriticalTotal allocation
diagonalProductsBelowProductOfTotals allocation =
  let
    diagonal =
      epsilonCom allocation * bCom allocation
      + epsilonKernel allocation * bKernel allocation
      + epsilonHHGood allocation * bHHGood allocation
    cross =
      epsilonCom allocation * bKernel allocation
      + epsilonCom allocation * bHHGood allocation
      + epsilonKernel allocation * bCom allocation
      + epsilonKernel allocation * bHHGood allocation
      + epsilonHHGood allocation * bCom allocation
      + epsilonHHGood allocation * bKernel allocation

    addCross : diagonal ≤ diagonal + cross
    addCross =
      subst
        (λ lower → lower ≤ diagonal + cross)
        (sym (ℚP.+-identityʳ diagonal))
        (ℚP.+-monoʳ-≤ diagonal (crossProductsNonnegative allocation))

    expanded :
      diagonal + cross
      ≡ softEtaTotal allocation * softCriticalTotal allocation
    expanded = solve
      ( epsilonCom allocation
      ∷ epsilonKernel allocation
      ∷ epsilonHHGood allocation
      ∷ bCom allocation
      ∷ bKernel allocation
      ∷ bHHGood allocation
      ∷ [])
  in
  subst (λ upper → diagonal ≤ upper) expanded addCross

jointYoungNecessaryProductBound :
  (allocation : ThreeSoftYoungAllocation) →
  softNumeratorTotal allocation
  ≤ softEtaTotal allocation * softCriticalTotal allocation
jointYoungNecessaryProductBound allocation =
  ℚP.≤-trans
    (sumYoungNumeratorsBelowDiagonalProducts allocation)
    (diagonalProductsBelowProductOfTotals allocation)

record AggregateSoftCorrectionCap
    (allocation : ThreeSoftYoungAllocation) : Set where
  field
    bCap : ℚ
    bCapNonnegative : 0ℚ ≤ bCap
    totalCriticalBelowCap : softCriticalTotal allocation ≤ bCap

open AggregateSoftCorrectionCap public

jointYoungKillTest :
  ∀ {allocation}
    (cap : AggregateSoftCorrectionCap allocation) →
  softNumeratorTotal allocation
  ≤ softEtaTotal allocation * bCap cap
jointYoungKillTest {allocation} cap =
  let
    scaled :
      softEtaTotal allocation * softCriticalTotal allocation
      ≤ softEtaTotal allocation * bCap cap
    scaled =
      let instance etaNNI = nonNegative (softEtaTotalNonnegative allocation)
      in ℚP.*-monoˡ-≤-nonNeg
        (softEtaTotal allocation)
        (totalCriticalBelowCap cap)
  in
  ℚP.≤-trans (jointYoungNecessaryProductBound allocation) scaled

softOwnersMustBeAllocatedAgainstAggregateCap : Bool
softOwnersMustBeAllocatedAgainstAggregateCap = true

rationalJointKillTestConstructed : Bool
rationalJointKillTestConstructed = true

sharpSquareRootOptimizerRequiresRealCarrier : Bool
sharpSquareRootOptimizerRequiresRealCarrier = true

softOwnersMustBeAllocatedAgainstAggregateCapIsTrue :
  softOwnersMustBeAllocatedAgainstAggregateCap ≡ true
softOwnersMustBeAllocatedAgainstAggregateCapIsTrue = refl

rationalJointKillTestConstructedIsTrue :
  rationalJointKillTestConstructed ≡ true
rationalJointKillTestConstructedIsTrue = refl

sharpSquareRootOptimizerRequiresRealCarrierIsTrue :
  sharpSquareRootOptimizerRequiresRealCarrier ≡ true
sharpSquareRootOptimizerRequiresRealCarrierIsTrue = refl
