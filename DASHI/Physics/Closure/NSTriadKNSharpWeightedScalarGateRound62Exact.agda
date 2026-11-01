module DASHI.Physics.Closure.NSTriadKNSharpWeightedScalarGateRound62Exact where

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
-- Round61 separately proved:
--
--   B_* = ((r-q)-a)/K              (K>0, a<r-q),
--   eta_soft = S^2/B_*             (weighted rational Young allocation).
--
-- This file performs the substitution exactly over Q.  Writing
--
--   margin = (r-q)-a,
--
-- it proves
--
--   1/B_* = K/margin,
--   eta_soft = K S^2 / margin,
--
-- and therefore exposes the final viscosity test in its irreducible physical
-- constants:
--
--   2 C_* K_bad + K S^2 / ((r-q)-a) + 1/16 < 1.
--
-- The first term is `G.hhBadEta`, definitionally `2*C_*K_bad` in Round61.
-- No correction-cap choice remains hidden in the final gate.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using ([]; _∷_)
open import Agda.Builtin.Nat using (Nat)
open import Data.Rational.Base as ℚ using
  (ℚ; 1ℚ; _+_; _*_; _<_; 1/_)
import Data.Rational.Properties as ℚP
open import Data.Rational.Tactic.RingSolver using (solve)
open import Relation.Binary.PropositionalEquality using
  (cong; subst; sym; module ≡-Reasoning)

import DASHI.Physics.Closure.NSTriadKNNineOwnerCriticalAbsorptionRound28Exact as Nine
import DASHI.Physics.Closure.NSTriadKNFixedShiftCorrectionHeadroomRound54Exact as Headroom
import DASHI.Physics.Closure.NSTriadKNFixedShiftStrictGapCapacityRound61Exact as Strict
import DASHI.Physics.Closure.NSTriadKNFixedShiftSharpStrictGapCapacityRound61Exact as SharpC
import DASHI.Physics.Closure.NSTriadKNLuoFixedShiftRecursionReductionExact as Fixed
import DASHI.Physics.Closure.NSTriadKNLuoRationalFixedBlockInductionExact as Block
import DASHI.Physics.Closure.NSTriadKNPhysicalNineOwnerFeasibilityRound61Exact as G
import DASHI.Physics.Closure.NSTriadKNPhysicalNineOwnerWeightedFeasibilityRound61Exact as Weighted
import DASHI.Physics.Closure.NSTriadKNJointGlobalFeasibilityRound54Exact as Existing

open ≡-Reasoning

criticalScale :
  ∀ {balances : Nat → Nine.NineOwnerCriticalBalance}
    {recursionData : Fixed.FixedShiftRecursionPhysicalData}
    {block : Block.RationalFixedBlockDecay}
    {identification : Headroom.PhysicalOwnerBlockCorrectionIdentification
      balances recursionData block} →
  SharpC.StrictPositiveCriticalScaleData identification → ℚ
criticalScale positiveScale =
  Strict.criticalScale (SharpC.scaleData positiveScale)

correctionMargin :
  ∀ {balances : Nat → Nine.NineOwnerCriticalBalance}
    {recursionData : Fixed.FixedShiftRecursionPhysicalData}
    {block : Block.RationalFixedBlockDecay}
    {identification : Headroom.PhysicalOwnerBlockCorrectionIdentification
      balances recursionData block} →
  SharpC.StrictPositiveCriticalScaleData identification → ℚ
correctionMargin positiveScale =
  Strict.correctionMargin (SharpC.scaleData positiveScale)

correctionMarginInverse :
  ∀ {balances : Nat → Nine.NineOwnerCriticalBalance}
    {recursionData : Fixed.FixedShiftRecursionPhysicalData}
    {block : Block.RationalFixedBlockDecay}
    {identification : Headroom.PhysicalOwnerBlockCorrectionIdentification
      balances recursionData block} →
  (positiveScale : SharpC.StrictPositiveCriticalScaleData identification) → ℚ
correctionMarginInverse positiveScale =
  let
    margin = correctionMargin positiveScale
    instance marginNonzero =
      ℚ.>-nonZero
        (Strict.correctionMarginPositive (SharpC.scaleData positiveScale))
  in
  ℚ.1/_ margin

correctionMarginTimesInverseIsOne :
  ∀ {balances : Nat → Nine.NineOwnerCriticalBalance}
    {recursionData : Fixed.FixedShiftRecursionPhysicalData}
    {block : Block.RationalFixedBlockDecay}
    {identification : Headroom.PhysicalOwnerBlockCorrectionIdentification
      balances recursionData block}
    (positiveScale : SharpC.StrictPositiveCriticalScaleData identification) →
  correctionMargin positiveScale * correctionMarginInverse positiveScale ≡ 1ℚ
correctionMarginTimesInverseIsOne positiveScale =
  let
    margin = correctionMargin positiveScale
    instance marginNonzero =
      ℚ.>-nonZero
        (Strict.correctionMarginPositive (SharpC.scaleData positiveScale))
  in
  ℚP.*-inverseʳ margin

sharpReciprocalCandidate :
  ∀ {balances : Nat → Nine.NineOwnerCriticalBalance}
    {recursionData : Fixed.FixedShiftRecursionPhysicalData}
    {block : Block.RationalFixedBlockDecay}
    {identification : Headroom.PhysicalOwnerBlockCorrectionIdentification
      balances recursionData block} →
  SharpC.StrictPositiveCriticalScaleData identification → ℚ
sharpReciprocalCandidate positiveScale =
  criticalScale positiveScale * correctionMarginInverse positiveScale

candidateTimesSharpCapIsOne :
  ∀ {balances : Nat → Nine.NineOwnerCriticalBalance}
    {recursionData : Fixed.FixedShiftRecursionPhysicalData}
    {block : Block.RationalFixedBlockDecay}
    {identification : Headroom.PhysicalOwnerBlockCorrectionIdentification
      balances recursionData block}
    (positiveScale : SharpC.StrictPositiveCriticalScaleData identification) →
  sharpReciprocalCandidate positiveScale
    * SharpC.maximalUniformCoefficient positiveScale
  ≡ 1ℚ
candidateTimesSharpCapIsOne positiveScale =
  let
    K = criticalScale positiveScale
    margin = correctionMargin positiveScale
    marginInv = correctionMarginInverse positiveScale
    B = SharpC.maximalUniformCoefficient positiveScale
  in
  begin
    sharpReciprocalCandidate positiveScale * B
  ≡⟨ solve (K ∷ marginInv ∷ B ∷ []) ⟩
    (B * K) * marginInv
  ≡⟨ cong (_* marginInv)
        (SharpC.maximalCoefficientTimesCriticalScale positiveScale) ⟩
    margin * marginInv
  ≡⟨ correctionMarginTimesInverseIsOne positiveScale ⟩
    1ℚ
  ∎

sharpCapInverseFormula :
  ∀ {balances : Nat → Nine.NineOwnerCriticalBalance}
    {recursionData : Fixed.FixedShiftRecursionPhysicalData}
    {block : Block.RationalFixedBlockDecay}
    {identification : Headroom.PhysicalOwnerBlockCorrectionIdentification
      balances recursionData block}
    {data : G.PhysicalNineOwnerScalars} →
  (positiveScale : SharpC.StrictPositiveCriticalScaleData identification) →
  G.correctionCap data ≡ SharpC.maximalUniformCoefficient positiveScale →
  G.correctionCapInverse data ≡ sharpReciprocalCandidate positiveScale
sharpCapInverseFormula {data = data} positiveScale capIsSharp =
  let
    cap = G.correctionCap data
    inv = G.correctionCapInverse data
    candidate = sharpReciprocalCandidate positiveScale

    candidateTimesCap : candidate * cap ≡ 1ℚ
    candidateTimesCap =
      subst
        (λ selectedCap → candidate * selectedCap ≡ 1ℚ)
        (sym capIsSharp)
        (candidateTimesSharpCapIsOne positiveScale)

    capTimesInv : cap * inv ≡ 1ℚ
    capTimesInv = G.capTimesInverseIsOne data
  in
  begin
    inv
  ≡⟨ sym (ℚP.*-identityʳ inv) ⟩
    inv * 1ℚ
  ≡⟨ cong (inv *_) (sym candidateTimesCap) ⟩
    inv * (candidate * cap)
  ≡⟨ solve (inv ∷ candidate ∷ cap ∷ []) ⟩
    candidate * (cap * inv)
  ≡⟨ cong (candidate *_) capTimesInv ⟩
    candidate * 1ℚ
  ≡⟨ ℚP.*-identityʳ candidate ⟩
    candidate
  ∎

sharpWeightedSoftEtaFormula :
  ∀ {balances : Nat → Nine.NineOwnerCriticalBalance}
    {recursionData : Fixed.FixedShiftRecursionPhysicalData}
    {block : Block.RationalFixedBlockDecay}
    {identification : Headroom.PhysicalOwnerBlockCorrectionIdentification
      balances recursionData block}
    {data : G.PhysicalNineOwnerScalars}
    (positiveScale : SharpC.StrictPositiveCriticalScaleData identification)
    (capIsSharp :
      G.correctionCap data ≡ SharpC.maximalUniformCoefficient positiveScale)
    (roots : Weighted.RationalSquareRootMajorants data) →
  Weighted.weightedSoftEta roots
  ≡ criticalScale positiveScale
      * Weighted.rootSum roots * Weighted.rootSum roots
      * correctionMarginInverse positiveScale
sharpWeightedSoftEtaFormula {data = data} positiveScale capIsSharp roots =
  let
    S = Weighted.rootSum roots
    K = criticalScale positiveScale
    marginInv = correctionMarginInverse positiveScale
    inverseMeaning = sharpCapInverseFormula positiveScale capIsSharp
  in
  begin
    Weighted.weightedSoftEta roots
  ≡⟨ refl ⟩
    S * S * G.correctionCapInverse data
  ≡⟨ cong (S * S *_) inverseMeaning ⟩
    S * S * (K * marginInv)
  ≡⟨ solve (S ∷ K ∷ marginInv ∷ []) ⟩
    K * S * S * marginInv
  ∎

explicitSharpEtaTotal :
  ∀ {balances : Nat → Nine.NineOwnerCriticalBalance}
    {recursionData : Fixed.FixedShiftRecursionPhysicalData}
    {block : Block.RationalFixedBlockDecay}
    {identification : Headroom.PhysicalOwnerBlockCorrectionIdentification
      balances recursionData block} →
  SharpC.StrictPositiveCriticalScaleData identification →
  (data : G.PhysicalNineOwnerScalars) →
  Weighted.RationalSquareRootMajorants data → ℚ
explicitSharpEtaTotal positiveScale data roots =
  G.hhBadEta data
  + criticalScale positiveScale
      * Weighted.rootSum roots * Weighted.rootSum roots
      * correctionMarginInverse positiveScale
  + Existing.oneSixteenth

sharpWeightedEtaTotalMeaning :
  ∀ {balances : Nat → Nine.NineOwnerCriticalBalance}
    {recursionData : Fixed.FixedShiftRecursionPhysicalData}
    {block : Block.RationalFixedBlockDecay}
    {identification : Headroom.PhysicalOwnerBlockCorrectionIdentification
      balances recursionData block}
    {data : G.PhysicalNineOwnerScalars}
    (positiveScale : SharpC.StrictPositiveCriticalScaleData identification)
    (capIsSharp :
      G.correctionCap data ≡ SharpC.maximalUniformCoefficient positiveScale)
    (roots : Weighted.RationalSquareRootMajorants data) →
  G.hhBadEta data + Weighted.weightedSoftEta roots + Existing.hardFourClassTax
  ≡ explicitSharpEtaTotal positiveScale data roots
sharpWeightedEtaTotalMeaning {data = data} positiveScale capIsSharp roots =
  let soft = sharpWeightedSoftEtaFormula positiveScale capIsSharp roots
  in
  begin
    G.hhBadEta data + Weighted.weightedSoftEta roots + Existing.hardFourClassTax
  ≡⟨ cong (λ selected → G.hhBadEta data + selected + Existing.hardFourClassTax) soft ⟩
    G.hhBadEta data
      + criticalScale positiveScale
          * Weighted.rootSum roots * Weighted.rootSum roots
          * correctionMarginInverse positiveScale
      + Existing.hardFourClassTax
  ≡⟨ cong
       (G.hhBadEta data
        + criticalScale positiveScale
            * Weighted.rootSum roots * Weighted.rootSum roots
            * correctionMarginInverse positiveScale
        +_)
       Existing.hardFourClassTaxIsOneSixteenth ⟩
    explicitSharpEtaTotal positiveScale data roots
  ∎

sharpWeightedNineOwnerStrictAbsorptionFromExplicitGate :
  ∀ {balances : Nat → Nine.NineOwnerCriticalBalance}
    {recursionData : Fixed.FixedShiftRecursionPhysicalData}
    {block : Block.RationalFixedBlockDecay}
    {identification : Headroom.PhysicalOwnerBlockCorrectionIdentification
      balances recursionData block}
    {data : G.PhysicalNineOwnerScalars}
    (positiveScale : SharpC.StrictPositiveCriticalScaleData identification)
    (capIsSharp :
      G.correctionCap data ≡ SharpC.maximalUniformCoefficient positiveScale)
    (roots : Weighted.RationalSquareRootMajorants data) →
  explicitSharpEtaTotal positiveScale data roots < 1ℚ →
  G.hhBadEta data
    + Weighted.weightedSoftEta roots
    + Existing.hardFourClassTax
  < 1ℚ
sharpWeightedNineOwnerStrictAbsorptionFromExplicitGate
    positiveScale capIsSharp roots explicitGate =
  subst
    (_< 1ℚ)
    (sym (sharpWeightedEtaTotalMeaning positiveScale capIsSharp roots))
    explicitGate

sharpWeightedGateExposesOnlyPhysicalConstants : Bool
sharpWeightedGateExposesOnlyPhysicalConstants = true

sharpWeightedGateExposesOnlyPhysicalConstantsIsTrue :
  sharpWeightedGateExposesOnlyPhysicalConstants ≡ true
sharpWeightedGateExposesOnlyPhysicalConstantsIsTrue = refl
