module DASHI.Physics.Closure.NSTriadKNPhysicalNineOwnerFeasibilityRound61Exact where

------------------------------------------------------------------------
-- PRIMARY SOURCES / CONTEXT
--
-- Author: William Henry Young.
-- Title: "On the Multiplication of Successions of Fourier Constants".
-- DOI: 10.1098/rspa.1912.0086.
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
-- ROUND 61 CONTRIBUTION
--
-- Make G constructive.  Once A/D/E have supplied the actual nonnegative Young
-- numerators and C has supplied a positive correction cap B_*, there is no need
-- to search over three arbitrary rational Young splits.
--
-- Give every soft owner exactly B_*/3 critical capacity and set
--
--   epsilon_i = 3 c_i / B_*.
--
-- Then, exactly in Q,
--
--   c_i = epsilon_i (B_*/3),
--   B_Com + B_kernel + B_HHg = B_*.
--
-- The Com numerator is not free: it is the existing Round52 lifted numerator
--
--   c_Com = (133/1024) m_Com.
--
-- Thus the final numerical theorem reduces to ONE strict scalar test
--
--   (2 C_* K_bad)
--     + epsilon_Com + epsilon_kernel + epsilon_HHg
--     + 1/16 < 1.
--
-- This equal-third construction is a robust exact fallback.  Round61's
-- weighted allocator improves it when rational square-root majorants for the
-- three physical numerators are available.  The final scalar gate is consumed
-- directly as a proof argument; it is not wrapped in a one-field receipt.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using ([]; _∷_)
import Data.Integer.Base as Int
open import Data.Rational.Base as ℚ using
  (ℚ; 0ℚ; 1ℚ; _/_; _+_; _*_; _≤_; _<_; 1/_; positive; nonNegative)
import Data.Rational.Properties as ℚP
open ℚP using (_≤?_)
open import Data.Rational.Tactic.RingSolver using (solve)
open import Relation.Binary.PropositionalEquality using (cong; subst; sym; trans)
open import Relation.Nullary.Decidable.Core using (toWitness)

import DASHI.Physics.Closure.NSTriadKNComExplicitSoftCoefficientRound50Exact as ComCoefficient
import DASHI.Physics.Closure.NSTriadKNComLiftingFeasibilityRound52Exact as Com
import DASHI.Physics.Closure.NSTriadKNJointSoftCorrectionBudgetRound54Exact as Joint
import DASHI.Physics.Closure.NSTriadKNJointGlobalFeasibilityRound54Exact as Existing
import DASHI.Physics.Closure.NSTriadKNHHBadSharpDyadicGainRound33Exact as Sharp

three oneThird : ℚ
three = Int.+ 3 / 1
oneThird = Int.+ 1 / 3

oneThirdNonnegative : 0ℚ ≤ oneThird
oneThirdNonnegative = toWitness {a? = 0ℚ ≤? oneThird} _

record PhysicalNineOwnerScalars : Set where
  field
    hhBadCeiling badChargeMultiplicity correctionCap : ℚ
    comMultiplicity kernelNumerator hhGoodNumerator : ℚ

    hhBadCeilingNonnegative : 0ℚ ≤ hhBadCeiling
    badChargeMultiplicityNonnegative : 0ℚ ≤ badChargeMultiplicity
    correctionCapPositive : 0ℚ < correctionCap
    comMultiplicityNonnegative : 0ℚ ≤ comMultiplicity
    kernelNumeratorNonnegative : 0ℚ ≤ kernelNumerator
    hhGoodNumeratorNonnegative : 0ℚ ≤ hhGoodNumerator

open PhysicalNineOwnerScalars public

comNumerator : PhysicalNineOwnerScalars → ℚ
comNumerator data = Com.liftedComYoungNumerator (comMultiplicity data)

correctionCapInverse : PhysicalNineOwnerScalars → ℚ
correctionCapInverse data =
  let
    cap = correctionCap data
    instance capNonzero = ℚ.>-nonZero (correctionCapPositive data)
  in
  ℚ.1/_ cap

thirdCorrectionCap : PhysicalNineOwnerScalars → ℚ
thirdCorrectionCap data = oneThird * correctionCap data

allocatedEpsilon : ℚ → PhysicalNineOwnerScalars → ℚ
allocatedEpsilon numerator data =
  three * numerator * correctionCapInverse data

comEpsilon kernelEpsilon hhGoodEpsilon : PhysicalNineOwnerScalars → ℚ
comEpsilon data = allocatedEpsilon (comNumerator data) data
kernelEpsilon data = allocatedEpsilon (kernelNumerator data) data
hhGoodEpsilon data = allocatedEpsilon (hhGoodNumerator data) data

hhBadEta : PhysicalNineOwnerScalars → ℚ
hhBadEta data =
  Sharp.two * hhBadCeiling data * badChargeMultiplicity data

softEta : PhysicalNineOwnerScalars → ℚ
softEta data =
  comEpsilon data + kernelEpsilon data + hhGoodEpsilon data

totalNineOwnerEta : PhysicalNineOwnerScalars → ℚ
totalNineOwnerEta data =
  hhBadEta data + softEta data + Existing.hardFourClassTax

correctionCapInversePositive :
  (data : PhysicalNineOwnerScalars) →
  0ℚ < correctionCapInverse data
correctionCapInversePositive data =
  let
    cap = correctionCap data
    capPositive = correctionCapPositive data
    instance
      capPositiveI = positive capPositive
      capNonzero = ℚP.pos⇒nonZero cap
      inversePositiveI = ℚP.1/pos⇒pos cap
  in
  ℚP.positive⁻¹ (correctionCapInverse data)

comNumeratorNonnegative :
  (data : PhysicalNineOwnerScalars) → 0ℚ ≤ comNumerator data
comNumeratorNonnegative data =
  let
    coefficientNN : 0ℚ ≤ ComCoefficient.oneThousandTwentyFourth133
    coefficientNN =
      toWitness {a? = 0ℚ ≤? ComCoefficient.oneThousandTwentyFourth133} _
    multiplicityNN = comMultiplicityNonnegative data
    instance
      coefficientNNI = nonNegative coefficientNN
      multiplicityNNI = nonNegative multiplicityNN
      productNNI =
        ℚP.nonNeg*nonNeg⇒nonNeg
          ComCoefficient.oneThousandTwentyFourth133
          (comMultiplicity data)
  in
  ℚP.nonNegative⁻¹ (comNumerator data)

allocatedEpsilonNonnegative :
  ∀ numerator data →
  0ℚ ≤ numerator →
  0ℚ ≤ allocatedEpsilon numerator data
allocatedEpsilonNonnegative numerator data numeratorNN =
  let
    threeNN : 0ℚ ≤ three
    threeNN = toWitness {a? = 0ℚ ≤? three} _
    inverseNN = ℚP.<⇒≤ (correctionCapInversePositive data)
    instance
      threeNNI = nonNegative threeNN
      numeratorNNI = nonNegative numeratorNN
      firstNNI = ℚP.nonNeg*nonNeg⇒nonNeg three numerator
      inverseNNI = nonNegative inverseNN
      secondNNI =
        ℚP.nonNeg*nonNeg⇒nonNeg
          (three * numerator) (correctionCapInverse data)
  in
  ℚP.nonNegative⁻¹ (allocatedEpsilon numerator data)

thirdCorrectionCapNonnegative :
  (data : PhysicalNineOwnerScalars) → 0ℚ ≤ thirdCorrectionCap data
thirdCorrectionCapNonnegative data =
  let
    capNN = ℚP.<⇒≤ (correctionCapPositive data)
    instance
      oneThirdNNI = nonNegative oneThirdNonnegative
      capNNI = nonNegative capNN
      productNNI =
        ℚP.nonNeg*nonNeg⇒nonNeg oneThird (correctionCap data)
  in
  ℚP.nonNegative⁻¹ (thirdCorrectionCap data)

capTimesInverseIsOne :
  (data : PhysicalNineOwnerScalars) →
  correctionCap data * correctionCapInverse data ≡ 1ℚ
capTimesInverseIsOne data =
  let
    cap = correctionCap data
    instance capNonzero = ℚ.>-nonZero (correctionCapPositive data)
  in
  ℚP.*-inverseʳ cap

allocatedYoungExact :
  ∀ numerator data →
  allocatedEpsilon numerator data * thirdCorrectionCap data
  ≡ numerator
allocatedYoungExact numerator data =
  let
    cap = correctionCap data
    inv = correctionCapInverse data
    regroup :
      allocatedEpsilon numerator data * thirdCorrectionCap data
      ≡ numerator * (cap * inv)
    regroup = solve (numerator ∷ cap ∷ inv ∷ [])
  in
  trans regroup
    (trans
      (cong (numerator *_) (capTimesInverseIsOne data))
      (ℚP.*-identityʳ numerator))

threeThirdCapsAreCap :
  (data : PhysicalNineOwnerScalars) →
  thirdCorrectionCap data
    + thirdCorrectionCap data
    + thirdCorrectionCap data
  ≡ correctionCap data
threeThirdCapsAreCap data =
  solve (correctionCap data ∷ [])

canonicalThreeSoftAllocation :
  (data : PhysicalNineOwnerScalars) → Joint.ThreeSoftYoungAllocation
canonicalThreeSoftAllocation data = record
  { epsilonCom = comEpsilon data
  ; epsilonKernel = kernelEpsilon data
  ; epsilonHHGood = hhGoodEpsilon data
  ; bCom = thirdCorrectionCap data
  ; bKernel = thirdCorrectionCap data
  ; bHHGood = thirdCorrectionCap data
  ; cCom = comNumerator data
  ; cKernel = kernelNumerator data
  ; cHHGood = hhGoodNumerator data
  ; epsilonComNonnegative =
      allocatedEpsilonNonnegative
        (comNumerator data) data (comNumeratorNonnegative data)
  ; epsilonKernelNonnegative =
      allocatedEpsilonNonnegative
        (kernelNumerator data) data (kernelNumeratorNonnegative data)
  ; epsilonHHGoodNonnegative =
      allocatedEpsilonNonnegative
        (hhGoodNumerator data) data (hhGoodNumeratorNonnegative data)
  ; bComNonnegative = thirdCorrectionCapNonnegative data
  ; bKernelNonnegative = thirdCorrectionCapNonnegative data
  ; bHHGoodNonnegative = thirdCorrectionCapNonnegative data
  ; comYoungCleared =
      subst
        (λ upper → comNumerator data ≤ upper)
        (sym (allocatedYoungExact (comNumerator data) data))
        ℚP.≤-refl
  ; kernelYoungCleared =
      subst
        (λ upper → kernelNumerator data ≤ upper)
        (sym (allocatedYoungExact (kernelNumerator data) data))
        ℚP.≤-refl
  ; hhGoodYoungCleared =
      subst
        (λ upper → hhGoodNumerator data ≤ upper)
        (sym (allocatedYoungExact (hhGoodNumerator data) data))
        ℚP.≤-refl
  }

canonicalAggregateCorrectionCap :
  (data : PhysicalNineOwnerScalars) →
  Joint.AggregateSoftCorrectionCap (canonicalThreeSoftAllocation data)
canonicalAggregateCorrectionCap data = record
  { bCap = correctionCap data
  ; bCapNonnegative = ℚP.<⇒≤ (correctionCapPositive data)
  ; totalCriticalBelowCap =
      subst
        (λ lower → lower ≤ correctionCap data)
        (sym (threeThirdCapsAreCap data))
        ℚP.≤-refl
  }

canonicalSoftEtaMeaning :
  (data : PhysicalNineOwnerScalars) →
  Joint.softEtaTotal (canonicalThreeSoftAllocation data)
  ≡ softEta data
canonicalSoftEtaMeaning data = refl

canonicalCriticalBudgetIsExact :
  (data : PhysicalNineOwnerScalars) →
  Joint.softCriticalTotal (canonicalThreeSoftAllocation data)
  ≡ correctionCap data
canonicalCriticalBudgetIsExact = threeThirdCapsAreCap

canonicalNineOwnerStrictAbsorption :
  ∀ data →
  totalNineOwnerEta data < 1ℚ →
  hhBadEta data
    + Joint.softEtaTotal (canonicalThreeSoftAllocation data)
    + Existing.hardFourClassTax
  < 1ℚ
canonicalNineOwnerStrictAbsorption data scalarGate
  rewrite canonicalSoftEtaMeaning data =
  scalarGate

physicalNineOwnerFeasibilityConstructedFromOneScalarGate : Bool
physicalNineOwnerFeasibilityConstructedFromOneScalarGate = true

physicalNineOwnerFeasibilityConstructedFromOneScalarGateIsTrue :
  physicalNineOwnerFeasibilityConstructedFromOneScalarGate ≡ true
physicalNineOwnerFeasibilityConstructedFromOneScalarGateIsTrue = refl
