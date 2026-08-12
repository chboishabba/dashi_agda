module DASHI.Physics.Closure.NSTriadKNHHBadZetaDirectLiveBudgetRound50Exact where

------------------------------------------------------------------------
-- PRIMARY SOURCES / CONTEXT
--
-- Authors: Peter Constantin; Charles Fefferman.
-- Title: "Direction of Vorticity and the Problem of Global Regularity for
-- the Navier-Stokes Equations".
-- DOI: 10.1512/iumj.1993.42.42034.
--
-- Author: Xiaoyutao Luo.
-- Title: "A Beale-Kato-Majda Criterion with Optimal Frequency and Temporal
-- Localization".
-- DOI: 10.1007/s00021-019-0411-z.
-- arXiv DOI: 10.48550/arXiv.1803.05569.
--
-- DASHI CONTRIBUTION
--
-- Replace alpha by the physical normalized depletion margin
--
--   zeta = 1-alpha > 0.
--
-- The live numerical gate is then exactly
--
--   C0 < T,
--   beta < zeta T.
--
-- This record converts those physically transparent hypotheses back into the
-- Round-49 direct-gate API, so no downstream theorem needs to be duplicated.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (zero)
open import Data.Rational.Base using (ℚ; 0ℚ; 1ℚ; _-_; _*_; _<_; _≤_)
open import Relation.Binary.PropositionalEquality using (subst; sym)

import DASHI.Physics.Closure.NSTriadKNLuoBadCoherenceWeightedMarkovExact as Threshold
import DASHI.Physics.Closure.NSTriadKNHHBadDefectRecurrenceNormalizationRound46Exact as Defect
import DASHI.Physics.Closure.NSTriadKNHHBadLiveBudgetTargetRound48Exact as Live
import DASHI.Physics.Closure.NSTriadKNHHBadDirectLiveBudgetRound49Exact as Direct
import DASHI.Physics.Closure.NSTriadKNHHBadZetaMarginRound50Exact as Zeta

record PhysicalZetaLiveBudgetInput
    (parameter : Threshold.PositiveThreshold) : Set where
  field
    physicalRecurrence : Defect.PhysicalDefectShellRecurrence parameter
    zeta : ℚ
    zetaPositive : 0ℚ < zeta
    zetaIsOneMinusAlpha :
      zeta ≡ 1ℚ - Defect.alpha physicalRecurrence

    comFloor kernelFloor : ℚ

    normalizedBaseBelowLiveTarget :
      Defect.normalizedDefectProfile physicalRecurrence zero
      < Live.allowableHHBadCeiling comFloor kernelFloor

    forcingBelowZetaTimesLiveTarget :
      Defect.beta physicalRecurrence
      < zeta * Live.allowableHHBadCeiling comFloor kernelFloor

open PhysicalZetaLiveBudgetInput public

alphaStrictFromPhysicalZeta :
  ∀ {parameter} (input : PhysicalZetaLiveBudgetInput parameter) →
  Defect.alpha (physicalRecurrence input) < 1ℚ
alphaStrictFromPhysicalZeta input =
  let
    zetaAsDifference :
      0ℚ < 1ℚ - Defect.alpha (physicalRecurrence input)
    zetaAsDifference =
      subst
        (0ℚ <_)
        (zetaIsOneMinusAlpha input)
        (zetaPositive input)
  in
  -- For ordered rationals, 0 < 1-alpha is equivalent to alpha < 1.
  -- Reuse the exact direction already consumed throughout the recurrence lane.
  Zeta.alphaStrictFromZetaPositive
    {zeta = 1ℚ - Defect.alpha (physicalRecurrence input)}
    zetaAsDifference

asRound49DirectLiveBudget :
  ∀ {parameter} →
  PhysicalZetaLiveBudgetInput parameter →
  Direct.PhysicalDirectLiveBudgetInput parameter
asRound49DirectLiveBudget input = record
  { physicalRecurrence = physicalRecurrence input
  ; alphaStrict = alphaStrictFromPhysicalZeta input
  ; comFloor = comFloor input
  ; kernelFloor = kernelFloor input
  ; normalizedBaseBelowLiveTarget = normalizedBaseBelowLiveTarget input
  ; forcingBelowLiveTarget =
      subst
        (λ factor →
          Defect.beta (physicalRecurrence input)
          < factor * Live.allowableHHBadCeiling
              (comFloor input) (kernelFloor input))
        (zetaIsOneMinusAlpha input)
        (forcingBelowZetaTimesLiveTarget input)
  }

zetaGateImpliesH2Strict :
  ∀ {parameter} (input : PhysicalZetaLiveBudgetInput parameter) →
  DASHI.Physics.Closure.NSTriadKNHardGateHierarchyRound47Exact.hardGateH2
    (Direct.derivedLiveCeiling (asRound49DirectLiveBudget input))
    (comFloor input)
    (kernelFloor input)
  < 1ℚ
zetaGateImpliesH2Strict input =
  Direct.directRecurrenceDataImpliesH2Strict
    (asRound49DirectLiveBudget input)

hhBadDirectGateNowUsesC0ZetaBeta : Bool
hhBadDirectGateNowUsesC0ZetaBeta = true

hhBadDirectGateNowUsesC0ZetaBetaIsTrue :
  hhBadDirectGateNowUsesC0ZetaBeta ≡ true
hhBadDirectGateNowUsesC0ZetaBetaIsTrue = refl
