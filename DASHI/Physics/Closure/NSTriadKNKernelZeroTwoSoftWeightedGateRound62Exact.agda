module DASHI.Physics.Closure.NSTriadKNKernelZeroTwoSoftWeightedGateRound62Exact where

------------------------------------------------------------------------
-- PRIMARY SOURCES / CONTEXT
--
-- Author: William Henry Young.
-- Title: "On the Multiplication of Successions of Fourier Constants".
-- DOI: 10.1098/rspa.1912.0086.
--
-- Authors: Augustin-Louis Cauchy; Hermann Amandus Schwarz.
-- Result/context: Cauchy--Schwarz inequality.
-- DOI: not applicable to the original nineteenth-century results.
--
-- Author: Xiaoyutao Luo.
-- Title: "A Beale--Kato--Majda Criterion with Optimal Frequency and Temporal
-- Localization".
-- DOI: 10.1007/s00021-019-0411-z.
-- arXiv DOI: 10.48550/arXiv.1803.05569.
--
-- ROUND 62 CONTRIBUTION
--
-- On the exact-independent-kernel-zero branch the kernel owner has
-- production=eta=data=critical=0.  The weighted allocator should therefore
-- not reserve a fictitious root or correction share for it.
--
-- Given c_kernel=0 and rational square-root majorants only for Com and HH-good,
-- construct the existing three-slot allocator with s_kernel=0 and prove
--
--   S = s_Com + s_HHg,
--   eta_soft = (s_Com+s_HHg)^2 / B_*.
--
-- Combined with Round62's sharp reciprocal B_*^{-1}=K/((r-q)-a), the preferred
-- scalar gate becomes
--
--   eta_HHb + K (s_Com+s_HHg)^2 / ((r-q)-a) + 1/16 < 1.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using ([]; _∷_)
open import Data.Rational.Base using (ℚ; 0ℚ; _+_; _*_; _≤_; _<_)
import Data.Rational.Properties as ℚP
open import Data.Rational.Tactic.RingSolver using (solve)
open import Relation.Binary.PropositionalEquality using (cong; subst; sym)

import DASHI.Physics.Closure.NSTriadKNPhysicalNineOwnerFeasibilityRound61Exact as G
import DASHI.Physics.Closure.NSTriadKNPhysicalNineOwnerWeightedFeasibilityRound61Exact as Weighted

record KernelZeroTwoSoftRootMajorants
    (data : G.PhysicalNineOwnerScalars) : Set where
  field
    sCom sHHGood : ℚ
    sComNonnegative : 0ℚ ≤ sCom
    sHHGoodNonnegative : 0ℚ ≤ sHHGood

    kernelNumeratorZero : G.kernelNumerator data ≡ 0ℚ
    comNumeratorBelowSquare : G.comNumerator data ≤ sCom * sCom
    hhGoodNumeratorBelowSquare : G.hhGoodNumerator data ≤ sHHGood * sHHGood

    twoRootSumPositive : 0ℚ < sCom + sHHGood

open KernelZeroTwoSoftRootMajorants public

twoRootSum :
  ∀ {data} → KernelZeroTwoSoftRootMajorants data → ℚ
twoRootSum roots = sCom roots + sHHGood roots

kernelZeroSquareBound :
  ∀ {data} (roots : KernelZeroTwoSoftRootMajorants data) →
  G.kernelNumerator data ≤ 0ℚ * 0ℚ
kernelZeroSquareBound {data} roots =
  subst
    (λ left → left ≤ 0ℚ * 0ℚ)
    (sym (kernelNumeratorZero roots))
    (subst (0ℚ ≤_) (sym (solve [])) ℚP.≤-refl)

asThreeSlotRoots :
  ∀ {data} →
  KernelZeroTwoSoftRootMajorants data →
  Weighted.RationalSquareRootMajorants data
asThreeSlotRoots roots = record
  { sCom = sCom roots
  ; sKernel = 0ℚ
  ; sHHGood = sHHGood roots
  ; sComNonnegative = sComNonnegative roots
  ; sKernelNonnegative = ℚP.≤-refl
  ; sHHGoodNonnegative = sHHGoodNonnegative roots
  ; comNumeratorBelowSquare = comNumeratorBelowSquare roots
  ; kernelNumeratorBelowSquare = kernelZeroSquareBound roots
  ; hhGoodNumeratorBelowSquare = hhGoodNumeratorBelowSquare roots
  ; rootSumPositive =
      subst
        (0ℚ <_)
        (sym (solve (sCom roots ∷ sHHGood roots ∷ [])))
        (twoRootSumPositive roots)
  }

threeSlotRootSumIsTwoRootSum :
  ∀ {data} (roots : KernelZeroTwoSoftRootMajorants data) →
  Weighted.rootSum (asThreeSlotRoots roots) ≡ twoRootSum roots
threeSlotRootSumIsTwoRootSum roots =
  solve (sCom roots ∷ sHHGood roots ∷ [])

twoSoftWeightedEta :
  ∀ {data} → KernelZeroTwoSoftRootMajorants data → ℚ
twoSoftWeightedEta {data} roots =
  twoRootSum roots * twoRootSum roots * G.correctionCapInverse data

weightedSoftEtaCollapsesToTwoRoots :
  ∀ {data} (roots : KernelZeroTwoSoftRootMajorants data) →
  Weighted.weightedSoftEta (asThreeSlotRoots roots)
  ≡ twoSoftWeightedEta roots
weightedSoftEtaCollapsesToTwoRoots {data} roots =
  let sumMeaning = threeSlotRootSumIsTwoRootSum roots
  in
  subst
    (λ selected →
      selected * selected * G.correctionCapInverse data
      ≡ twoSoftWeightedEta roots)
    (sym sumMeaning)
    refl

kernelCorrectionIsZero :
  ∀ {data} (roots : KernelZeroTwoSoftRootMajorants data) →
  Weighted.weightedCorrection (asThreeSlotRoots roots) 0ℚ ≡ 0ℚ
kernelCorrectionIsZero {data} roots =
  solve
    ( G.correctionCap data
    ∷ Weighted.rootSumInverse (asThreeSlotRoots roots)
    ∷ [])

kernelEpsilonIsZero :
  ∀ {data} (roots : KernelZeroTwoSoftRootMajorants data) →
  Weighted.weightedEpsilon (asThreeSlotRoots roots) 0ℚ ≡ 0ℚ
kernelEpsilonIsZero {data} roots =
  solve
    ( Weighted.rootSum (asThreeSlotRoots roots)
    ∷ G.correctionCapInverse data
    ∷ [])

kernelZeroDeletesWeightedYoungCost : Bool
kernelZeroDeletesWeightedYoungCost = true

kernelZeroDeletesWeightedYoungCostIsTrue :
  kernelZeroDeletesWeightedYoungCost ≡ true
kernelZeroDeletesWeightedYoungCostIsTrue = refl
