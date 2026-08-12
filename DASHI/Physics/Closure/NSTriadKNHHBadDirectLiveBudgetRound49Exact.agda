module DASHI.Physics.Closure.NSTriadKNHHBadDirectLiveBudgetRound49Exact where

------------------------------------------------------------------------
-- PRIMARY SOURCES / CONTEXT
--
-- Author: Gyula Farkas.
-- Title: "Theorie der einfachen Ungleichungen".
-- Journal fuer die reine und angewandte Mathematik 124 (1902), 1--27.
-- DOI: no DOI assigned to the historical article.
--
-- Author: Xiaoyutao Luo.
-- Title: "A Beale-Kato-Majda Criterion with Optimal Frequency and Temporal Localization".
-- DOI: 10.1007/s00021-019-0411-z.
--
-- DASHI CONTRIBUTION
--
-- Push the live hard gate all the way onto physical recurrence data. For
-- T = 15/32 - (tau_Com + tau_kernel)/2 it is enough to prove directly
-- C_0<T and beta<(1-alpha)T. Round 49 constructs M<T internally and
-- Round 48 then proves H2(M)<1. If Com and kernel are both soft the target
-- specializes exactly to 15/32.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (zero)
open import Data.Rational.Base using (ℚ; 0ℚ; 1ℚ; _-_; _*_; _<_) 
open import Relation.Binary.PropositionalEquality using (subst; sym)

import DASHI.Physics.Closure.NSTriadKNLuoBadCoherenceWeightedMarkovExact as Threshold
import DASHI.Physics.Closure.NSTriadKNHHBadDefectRecurrenceNormalizationRound46Exact as Defect
import DASHI.Physics.Closure.NSTriadKNHHBadLiveBudgetTargetRound48Exact as Live
import DASHI.Physics.Closure.NSTriadKNHardGateHierarchyRound47Exact as Gate
import DASHI.Physics.Closure.NSTriadKNHHBadDirectTargetToSelectedRecurrenceRound49Exact as Direct

record PhysicalDirectLiveBudgetInput
    (parameter : Threshold.PositiveThreshold) : Set where
  field
    physicalRecurrence : Defect.PhysicalDefectShellRecurrence parameter
    alphaStrict : Defect.alpha physicalRecurrence < 1ℚ
    comFloor kernelFloor : ℚ

    normalizedBaseBelowLiveTarget :
      Defect.normalizedDefectProfile physicalRecurrence zero
      < Live.allowableHHBadCeiling comFloor kernelFloor

    forcingBelowLiveTarget :
      Defect.beta physicalRecurrence
      < (1ℚ - Defect.alpha physicalRecurrence)
        * Live.allowableHHBadCeiling comFloor kernelFloor

open PhysicalDirectLiveBudgetInput public

asDirectPhysicalHHBadTarget :
  ∀ {parameter} →
  PhysicalDirectLiveBudgetInput parameter →
  Direct.DirectPhysicalHHBadTarget parameter
asDirectPhysicalHHBadTarget input = record
  { physicalRecurrence = physicalRecurrence input
  ; target = Live.allowableHHBadCeiling (comFloor input) (kernelFloor input)
  ; alphaStrict = alphaStrict input
  ; normalizedBaseStrict = normalizedBaseBelowLiveTarget input
  ; forcingStrict = forcingBelowLiveTarget input
  }

derivedLiveCeiling :
  ∀ {parameter} → PhysicalDirectLiveBudgetInput parameter → ℚ
derivedLiveCeiling input =
  Direct.derivedTargetCeiling (asDirectPhysicalHHBadTarget input)

derivedLiveCeilingBelowAllowance :
  ∀ {parameter} (input : PhysicalDirectLiveBudgetInput parameter) →
  derivedLiveCeiling input
  < Live.allowableHHBadCeiling (comFloor input) (kernelFloor input)
derivedLiveCeilingBelowAllowance input =
  Direct.derivedTargetCeilingStrict (asDirectPhysicalHHBadTarget input)

directRecurrenceDataImpliesH2Strict :
  ∀ {parameter} (input : PhysicalDirectLiveBudgetInput parameter) →
  Gate.hardGateH2
    (derivedLiveCeiling input)
    (comFloor input)
    (kernelFloor input)
  < 1ℚ
directRecurrenceDataImpliesH2Strict input =
  Live.liveCeilingTargetImpliesH2Strict
    (derivedLiveCeiling input)
    (comFloor input)
    (kernelFloor input)
    (derivedLiveCeilingBelowAllowance input)

softComKernelTargetIsFifteenThirtySeconds :
  Live.allowableHHBadCeiling 0ℚ 0ℚ ≡ Live.fifteenThirtySeconds
softComKernelTargetIsFifteenThirtySeconds = Live.allowableWithSoftComAndKernel

record SoftComKernelDirectHHBadTarget
    (parameter : Threshold.PositiveThreshold) : Set where
  field
    physicalRecurrence : Defect.PhysicalDefectShellRecurrence parameter
    alphaStrict : Defect.alpha physicalRecurrence < 1ℚ
    normalizedBaseBelowFifteenThirtySeconds :
      Defect.normalizedDefectProfile physicalRecurrence zero
      < Live.fifteenThirtySeconds
    forcingBelowFifteenThirtySeconds :
      Defect.beta physicalRecurrence
      < (1ℚ - Defect.alpha physicalRecurrence) * Live.fifteenThirtySeconds

open SoftComKernelDirectHHBadTarget public

softComKernelDirectInput :
  ∀ {parameter} →
  SoftComKernelDirectHHBadTarget parameter →
  PhysicalDirectLiveBudgetInput parameter
softComKernelDirectInput input = record
  { physicalRecurrence = SoftComKernelDirectHHBadTarget.physicalRecurrence input
  ; alphaStrict = SoftComKernelDirectHHBadTarget.alphaStrict input
  ; comFloor = 0ℚ
  ; kernelFloor = 0ℚ
  ; normalizedBaseBelowLiveTarget =
      subst
        (λ upper →
          Defect.normalizedDefectProfile
            (SoftComKernelDirectHHBadTarget.physicalRecurrence input) zero
          < upper)
        (sym softComKernelTargetIsFifteenThirtySeconds)
        (normalizedBaseBelowFifteenThirtySeconds input)
  ; forcingBelowLiveTarget =
      subst
        (λ upper →
          Defect.beta (SoftComKernelDirectHHBadTarget.physicalRecurrence input)
          < (1ℚ - Defect.alpha
              (SoftComKernelDirectHHBadTarget.physicalRecurrence input)) * upper)
        (sym softComKernelTargetIsFifteenThirtySeconds)
        (forcingBelowFifteenThirtySeconds input)
  }

softComKernelDirectTargetsImplyH0Strict :
  ∀ {parameter}
    (input : SoftComKernelDirectHHBadTarget parameter) →
  Gate.hardGateH2
    (derivedLiveCeiling (softComKernelDirectInput input)) 0ℚ 0ℚ
  < 1ℚ
softComKernelDirectTargetsImplyH0Strict input =
  directRecurrenceDataImpliesH2Strict (softComKernelDirectInput input)

hhBadHardGateNowConsumesDirectRecurrenceTargets : Bool
hhBadHardGateNowConsumesDirectRecurrenceTargets = true

hhBadHardGateNowConsumesDirectRecurrenceTargetsIsTrue :
  hhBadHardGateNowConsumesDirectRecurrenceTargets ≡ true
hhBadHardGateNowConsumesDirectRecurrenceTargetsIsTrue = refl
