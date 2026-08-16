module DASHI.Physics.Closure.NSTriadKNPhysicalNineOwnerWeightedFeasibilityRound61Exact where

------------------------------------------------------------------------
-- PRIMARY SOURCES / CONTEXT
--
-- Author: William Henry Young.
-- Title: "On the Multiplication of Successions of Fourier Constants".
-- DOI: 10.1098/rspa.1912.0086.
--
-- Author: Augustin-Louis Cauchy.
-- Title/context: Cauchy's inequality / the finite Cauchy--Schwarz inequality.
-- DOI: not applicable to the original nineteenth-century source.
--
-- Authors: Tosio Kato; Gustavo Ponce.
-- Title: "Commutator Estimates and the Euler and Navier-Stokes Equations".
-- DOI: 10.1002/cpa.3160410704.
--
-- Author: Xiaoyutao Luo.
-- Title: "A Beale--Kato--Majda Criterion with Optimal Frequency and Temporal
-- Localization".
-- DOI: 10.1007/s00021-019-0411-z.
-- arXiv DOI: 10.48550/arXiv.1803.05569.
--
-- ROUND 61 HIGH-ALPHA G IMPROVEMENT
--
-- Equal thirds is a robust constructive fallback, but it is not the optimal
-- way to spend a scarce correction cap B_* when the three Young numerators are
-- very different.  The real-valued optimum allocates B_i proportional to
-- sqrt(c_i).  Exact rational Agda should not manufacture irrational roots, so
-- use rational square-root MAJORANTS instead:
--
--   c_i <= s_i^2,       s_i >= 0,
--   S = s_Com + s_kernel + s_HHg > 0.
--
-- Define
--
--   B_i       = B_* s_i / S,
--   epsilon_i = S s_i / B_*.
--
-- Then exactly over Q
--
--   epsilon_i B_i = s_i^2 >= c_i,
--   sum B_i         = B_*,
--   sum epsilon_i   = S^2 / B_*.
--
-- Thus the physical G gate can be tested by the single sharper rational scalar
-- inequality
--
--   2 C_* K_bad + S^2/B_* + 1/16 < 1.
--
-- Rational upper approximations to sqrt(c_i) can make this arbitrarily close
-- to the Cauchy-optimal real allocation while preserving exact proof terms.
-- The equal-third allocator remains useful for the degenerate S=0 case and as
-- a simple fallback, but should not be the primary feasibility test.  As in the
-- fallback module, the final strict gate is a direct proof argument, not a
-- one-field reserve receipt.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using ([]; _∷_)
open import Data.Rational.Base as ℚ using
  (ℚ; 0ℚ; 1ℚ; _+_; _*_; _≤_; _<_; 1/_; positive; nonNegative)
import Data.Rational.Properties as ℚP
open import Data.Rational.Tactic.RingSolver using (solve)
open import Relation.Binary.PropositionalEquality using
  (cong; subst; sym; module ≡-Reasoning)

import DASHI.Physics.Closure.NSTriadKNJointSoftCorrectionBudgetRound54Exact as Joint
import DASHI.Physics.Closure.NSTriadKNJointGlobalFeasibilityRound54Exact as Existing
import DASHI.Physics.Closure.NSTriadKNPhysicalNineOwnerFeasibilityRound61Exact as G

open ≡-Reasoning

record RationalSquareRootMajorants
    (data : G.PhysicalNineOwnerScalars) : Set where
  field
    sCom sKernel sHHGood : ℚ
    sComNonnegative : 0ℚ ≤ sCom
    sKernelNonnegative : 0ℚ ≤ sKernel
    sHHGoodNonnegative : 0ℚ ≤ sHHGood

    comNumeratorBelowSquare :
      G.comNumerator data ≤ sCom * sCom
    kernelNumeratorBelowSquare :
      G.kernelNumerator data ≤ sKernel * sKernel
    hhGoodNumeratorBelowSquare :
      G.hhGoodNumerator data ≤ sHHGood * sHHGood

    rootSumPositive : 0ℚ < sCom + sKernel + sHHGood

open RationalSquareRootMajorants public

rootSum :
  ∀ {data} → RationalSquareRootMajorants data → ℚ
rootSum roots = sCom roots + sKernel roots + sHHGood roots

rootSumInverse :
  ∀ {data} (roots : RationalSquareRootMajorants data) → ℚ
rootSumInverse roots =
  let
    S = rootSum roots
    instance sNonzero = ℚ.>-nonZero (rootSumPositive roots)
  in
  ℚ.1/_ S

rootSumInversePositive :
  ∀ {data} (roots : RationalSquareRootMajorants data) →
  0ℚ < rootSumInverse roots
rootSumInversePositive roots =
  let
    S = rootSum roots
    sPositive = rootSumPositive roots
    instance
      sPositiveI = positive sPositive
      sNonzero = ℚP.pos⇒nonZero S
      inversePositiveI = ℚP.1/pos⇒pos S
  in
  ℚP.positive⁻¹ (rootSumInverse roots)

rootSumTimesInverseIsOne :
  ∀ {data} (roots : RationalSquareRootMajorants data) →
  rootSum roots * rootSumInverse roots ≡ 1ℚ
rootSumTimesInverseIsOne roots =
  let
    S = rootSum roots
    instance sNonzero = ℚ.>-nonZero (rootSumPositive roots)
  in
  ℚP.*-inverseʳ S

weightedCorrection :
  ∀ {data} →
  RationalSquareRootMajorants data → ℚ → ℚ
weightedCorrection {data} roots s =
  G.correctionCap data * s * rootSumInverse roots

weightedEpsilon :
  ∀ {data} →
  RationalSquareRootMajorants data → ℚ → ℚ
weightedEpsilon {data} roots s =
  rootSum roots * s * G.correctionCapInverse data

weightedCorrectionNonnegative :
  ∀ {data} (roots : RationalSquareRootMajorants data) s →
  0ℚ ≤ s → 0ℚ ≤ weightedCorrection roots s
weightedCorrectionNonnegative {data} roots s sNN =
  let
    capNN = ℚP.<⇒≤ (G.correctionCapPositive data)
    invNN = ℚP.<⇒≤ (rootSumInversePositive roots)
    instance
      capNNI = nonNegative capNN
      sNNI = nonNegative sNN
      firstNNI = ℚP.nonNeg*nonNeg⇒nonNeg (G.correctionCap data) s
      invNNI = nonNegative invNN
      secondNNI =
        ℚP.nonNeg*nonNeg⇒nonNeg
          (G.correctionCap data * s) (rootSumInverse roots)
  in
  ℚP.nonNegative⁻¹ (weightedCorrection roots s)

weightedEpsilonNonnegative :
  ∀ {data} (roots : RationalSquareRootMajorants data) s →
  0ℚ ≤ s → 0ℚ ≤ weightedEpsilon roots s
weightedEpsilonNonnegative {data} roots s sNN =
  let
    sumNN = ℚP.<⇒≤ (rootSumPositive roots)
    capInvNN = ℚP.<⇒≤ (G.correctionCapInversePositive data)
    instance
      sumNNI = nonNegative sumNN
      sNNI = nonNegative sNN
      firstNNI = ℚP.nonNeg*nonNeg⇒nonNeg (rootSum roots) s
      capInvNNI = nonNegative capInvNN
      secondNNI =
        ℚP.nonNeg*nonNeg⇒nonNeg
          (rootSum roots * s) (G.correctionCapInverse data)
  in
  ℚP.nonNegative⁻¹ (weightedEpsilon roots s)

weightedYoungExact :
  ∀ {data} (roots : RationalSquareRootMajorants data) s →
  weightedEpsilon roots s * weightedCorrection roots s
  ≡ s * s
weightedYoungExact {data} roots s =
  let
    cap = G.correctionCap data
    capInv = G.correctionCapInverse data
    S = rootSum roots
    sInv = rootSumInverse roots
  in
  begin
    weightedEpsilon roots s * weightedCorrection roots s
  ≡⟨ solve (S ∷ s ∷ capInv ∷ cap ∷ sInv ∷ []) ⟩
    (s * s) * (cap * capInv) * (S * sInv)
  ≡⟨ cong (λ value → (s * s) * value * (S * sInv))
        (G.capTimesInverseIsOne data) ⟩
    (s * s) * 1ℚ * (S * sInv)
  ≡⟨ cong (λ value → (s * s) * 1ℚ * value)
        (rootSumTimesInverseIsOne roots) ⟩
    (s * s) * 1ℚ * 1ℚ
  ≡⟨ solve (s ∷ []) ⟩
    s * s
  ∎

weightedCorrectionTotalExact :
  ∀ {data} (roots : RationalSquareRootMajorants data) →
  weightedCorrection roots (sCom roots)
    + weightedCorrection roots (sKernel roots)
    + weightedCorrection roots (sHHGood roots)
  ≡ G.correctionCap data
weightedCorrectionTotalExact {data} roots =
  let
    cap = G.correctionCap data
    inv = rootSumInverse roots
    sC = sCom roots
    sK = sKernel roots
    sH = sHHGood roots
  in
  begin
    weightedCorrection roots sC
      + weightedCorrection roots sK
      + weightedCorrection roots sH
  ≡⟨ solve (cap ∷ sC ∷ sK ∷ sH ∷ inv ∷ []) ⟩
    cap * ((sC + sK + sH) * inv)
  ≡⟨ refl ⟩
    cap * (rootSum roots * rootSumInverse roots)
  ≡⟨ cong (cap *_) (rootSumTimesInverseIsOne roots) ⟩
    cap * 1ℚ
  ≡⟨ ℚP.*-identityʳ cap ⟩
    cap
  ∎

weightedSoftEta :
  ∀ {data} → RationalSquareRootMajorants data → ℚ
weightedSoftEta {data} roots =
  rootSum roots * rootSum roots * G.correctionCapInverse data

weightedEpsilonTotalExact :
  ∀ {data} (roots : RationalSquareRootMajorants data) →
  weightedEpsilon roots (sCom roots)
    + weightedEpsilon roots (sKernel roots)
    + weightedEpsilon roots (sHHGood roots)
  ≡ weightedSoftEta roots
weightedEpsilonTotalExact {data} roots =
  let
    S = rootSum roots
    inv = G.correctionCapInverse data
    sC = sCom roots
    sK = sKernel roots
    sH = sHHGood roots
  in
  begin
    weightedEpsilon roots sC
      + weightedEpsilon roots sK
      + weightedEpsilon roots sH
  ≡⟨ solve (S ∷ sC ∷ sK ∷ sH ∷ inv ∷ []) ⟩
    S * (sC + sK + sH) * inv
  ≡⟨ refl ⟩
    weightedSoftEta roots
  ∎

weightedThreeSoftAllocation :
  ∀ {data} →
  (roots : RationalSquareRootMajorants data) →
  Joint.ThreeSoftYoungAllocation
weightedThreeSoftAllocation {data} roots = record
  { epsilonCom = weightedEpsilon roots (sCom roots)
  ; epsilonKernel = weightedEpsilon roots (sKernel roots)
  ; epsilonHHGood = weightedEpsilon roots (sHHGood roots)
  ; bCom = weightedCorrection roots (sCom roots)
  ; bKernel = weightedCorrection roots (sKernel roots)
  ; bHHGood = weightedCorrection roots (sHHGood roots)
  ; cCom = G.comNumerator data
  ; cKernel = G.kernelNumerator data
  ; cHHGood = G.hhGoodNumerator data
  ; epsilonComNonnegative =
      weightedEpsilonNonnegative roots (sCom roots) (sComNonnegative roots)
  ; epsilonKernelNonnegative =
      weightedEpsilonNonnegative roots (sKernel roots) (sKernelNonnegative roots)
  ; epsilonHHGoodNonnegative =
      weightedEpsilonNonnegative roots (sHHGood roots) (sHHGoodNonnegative roots)
  ; bComNonnegative =
      weightedCorrectionNonnegative roots (sCom roots) (sComNonnegative roots)
  ; bKernelNonnegative =
      weightedCorrectionNonnegative roots (sKernel roots) (sKernelNonnegative roots)
  ; bHHGoodNonnegative =
      weightedCorrectionNonnegative roots (sHHGood roots) (sHHGoodNonnegative roots)
  ; comYoungCleared =
      subst
        (λ upper → G.comNumerator data ≤ upper)
        (sym (weightedYoungExact roots (sCom roots)))
        (comNumeratorBelowSquare roots)
  ; kernelYoungCleared =
      subst
        (λ upper → G.kernelNumerator data ≤ upper)
        (sym (weightedYoungExact roots (sKernel roots)))
        (kernelNumeratorBelowSquare roots)
  ; hhGoodYoungCleared =
      subst
        (λ upper → G.hhGoodNumerator data ≤ upper)
        (sym (weightedYoungExact roots (sHHGood roots)))
        (hhGoodNumeratorBelowSquare roots)
  }

weightedAggregateCorrectionCap :
  ∀ {data} (roots : RationalSquareRootMajorants data) →
  Joint.AggregateSoftCorrectionCap (weightedThreeSoftAllocation roots)
weightedAggregateCorrectionCap {data} roots = record
  { bCap = G.correctionCap data
  ; bCapNonnegative = ℚP.<⇒≤ (G.correctionCapPositive data)
  ; totalCriticalBelowCap =
      subst
        (λ lower → lower ≤ G.correctionCap data)
        (sym (weightedCorrectionTotalExact roots))
        ℚP.≤-refl
  }

weightedSoftEtaMeaning :
  ∀ {data} (roots : RationalSquareRootMajorants data) →
  Joint.softEtaTotal (weightedThreeSoftAllocation roots)
  ≡ weightedSoftEta roots
weightedSoftEtaMeaning = weightedEpsilonTotalExact

weightedCriticalBudgetIsExact :
  ∀ {data} (roots : RationalSquareRootMajorants data) →
  Joint.softCriticalTotal (weightedThreeSoftAllocation roots)
  ≡ G.correctionCap data
weightedCriticalBudgetIsExact = weightedCorrectionTotalExact

weightedNineOwnerStrictAbsorption :
  ∀ {data} (roots : RationalSquareRootMajorants data) →
  ( G.hhBadEta data
      + weightedSoftEta roots
      + Existing.hardFourClassTax
    < 1ℚ ) →
  G.hhBadEta data
    + Joint.softEtaTotal (weightedThreeSoftAllocation roots)
    + Existing.hardFourClassTax
  < 1ℚ
weightedNineOwnerStrictAbsorption roots scalarGate
  rewrite weightedSoftEtaMeaning roots =
  scalarGate

weightedRationalYoungAllocatorConstructed : Bool
weightedRationalYoungAllocatorConstructed = true

weightedRationalYoungAllocatorConstructedIsTrue :
  weightedRationalYoungAllocatorConstructed ≡ true
weightedRationalYoungAllocatorConstructedIsTrue = refl
