module DASHI.Physics.Closure.NSTriadKNLuoExplicitCutoffLocalizedCriterionExact where

------------------------------------------------------------------------
-- PROVENANCE
--
-- Author: Xiaoyutao Luo.
-- Title: "A Beale-Kato-Majda Criterion with Optimal Frequency and Temporal
-- Localization".
-- Venue/year: Journal of Mathematical Fluid Mechanics 21 (2019), article 1.
-- DOI: 10.1007/s00021-019-0411-z.
-- arXiv DOI: 10.48550/arXiv.1803.05569.
--
-- USE
-- Luo's periodic-compatible criterion uses the explicit parabolic terminal
-- window
--
--   I_p(T) = [ T - c 2^(-2p) , T )
--
-- and controls the low-frequency gradient integral on modes <= p.  This file
-- formalises the exact cutoff-majorant algebra needed by DASHI:
--
--   localized gradient integral
--     <= retained low-mode contribution + forced-tail contribution,
--
-- with the forced-tail contribution controlled in the stronger scaled form
--
--   (p+1) * forcedTailIntegral p <= tailBudget.
--
-- Since 1 <= p+1, the scaled estimate implies the unscaled tail estimate.
-- Combining that with a retained-mode bound proves the localized Luo cutoff
-- quantity is below the selected BKM threshold.
--
-- This is a constructive numerical bridge.  Identification of the Nat-valued
-- quantities with the actual time integral and invocation of Luo's analytic
-- continuation theorem remain explicit downstream obligations.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_; _*_)
open import Data.Nat using (_≤_; z≤n; s≤s)
open import Data.Nat.Properties
  using ( ≤-refl; ≤-trans; ≤-reflexive
        ; +-mono-≤; *-mono-≤; *-identityˡ )

import DASHI.Physics.Closure.NSTriadKNProfileDepthGeometryCutoffIndexedExact
  as Depth
import DASHI.Physics.Closure.NSTriadKNPeriodicLittlewoodPaleyBonyExact
  as PeriodicLP

pow2 : Nat → Nat
pow2 zero = suc zero
pow2 (suc exponent) = suc (suc zero) * pow2 exponent

parabolicWindowDenominator : Nat → Nat
parabolicWindowDenominator cutoff = pow2 (cutoff + cutoff)

parabolicWindowDenominatorIsTwoToTwoP :
  (cutoff : Nat) →
  parabolicWindowDenominator cutoff ≡ pow2 (cutoff + cutoff)
parabolicWindowDenominatorIsTwoToTwoP cutoff = refl

record LuoParabolicTerminalWindow : Set₁ where
  field
    Time : Set
    terminalTime : Time
    inTerminalWindow : Nat → Time → Set
    windowDenominator : Nat → Nat
    windowDenominatorIsParabolic :
      (cutoff : Nat) →
      windowDenominator cutoff ≡ parabolicWindowDenominator cutoff

open LuoParabolicTerminalWindow public

record CutoffForcedTailLocalizedOutput
    (cutoff : Nat) : Set where
  constructor output
  field
    forcedTailIntegral : Nat
    tailBudget : Nat

    adversarialOrientation :
      suc cutoff
        * Depth.weightOf cutoff
            (Depth.ftAdvTarget Depth.ftToAdversarial)
        ≤
      Depth.weightOf cutoff
        (Depth.ftAdvSource Depth.ftToAdversarial)

    transitionOrientation :
      suc cutoff
        * Depth.weightOf cutoff
            (Depth.ftTransTarget Depth.ftToTransition)
        ≤
      Depth.weightOf cutoff
        (Depth.ftTransSource Depth.ftToTransition)

    scaledForcedTailBound :
      suc cutoff * forcedTailIntegral ≤ tailBudget

open CutoffForcedTailLocalizedOutput public

mkCutoffForcedTailLocalizedOutput :
  (cutoff forcedTailIntegral tailBudget : Nat) →
  suc cutoff * forcedTailIntegral ≤ tailBudget →
  CutoffForcedTailLocalizedOutput cutoff
mkCutoffForcedTailLocalizedOutput
  cutoff forcedTailIntegral tailBudget scaledBound =
  output
    forcedTailIntegral
    tailBudget
    (Depth.ftAdvWeightOrientation cutoff Depth.ftToAdversarial)
    (Depth.ftTransWeightOrientation cutoff Depth.ftToTransition)
    scaledBound

forcedTailIntegralBound :
  (cutoff : Nat) →
  (tail : CutoffForcedTailLocalizedOutput cutoff) →
  forcedTailIntegral tail ≤ tailBudget tail
forcedTailIntegralBound cutoff tail =
  ≤-trans
    (≤-trans
      (≤-reflexive (*-identityˡ (forcedTailIntegral tail)))
      (*-mono-≤
        (s≤s z≤n)
        (≤-refl {forcedTailIntegral tail})))
    (scaledForcedTailBound tail)

record LuoCutoffLocalizedMajorant
    (cutoff : Nat) : Set where
  constructor majorant
  field
    periodicHardLowPassInterface :
      PeriodicLP.periodicHardLowPassProjectorConstructed ≡ true

    retainedLowModeGradientIntegral : Nat
    retainedLowModeBudget : Nat

    forcedTailOutput :
      CutoffForcedTailLocalizedOutput cutoff

    localizedLowFrequencyGradientIntegral : Nat
    bkmThreshold : Nat

    localizedDecompositionBound :
      localizedLowFrequencyGradientIntegral
        ≤
      retainedLowModeGradientIntegral
        + forcedTailIntegral forcedTailOutput

    retainedLowModeBound :
      retainedLowModeGradientIntegral ≤ retainedLowModeBudget

    combinedBudgetBelowThreshold :
      retainedLowModeBudget + tailBudget forcedTailOutput
        ≤ bkmThreshold

open LuoCutoffLocalizedMajorant public

luoLocalizedQuantityBelowThreshold :
  (cutoff : Nat) →
  (control : LuoCutoffLocalizedMajorant cutoff) →
  localizedLowFrequencyGradientIntegral control
    ≤ bkmThreshold control
luoLocalizedQuantityBelowThreshold cutoff control =
  ≤-trans
    (localizedDecompositionBound control)
    (≤-trans
      (+-mono-≤
        (retainedLowModeBound control)
        (forcedTailIntegralBound cutoff (forcedTailOutput control)))
      (combinedBudgetBelowThreshold control))

record LuoExplicitCutoffCriterionWitness : Set₁ where
  constructor witness
  field
    cutoff : Nat
    parabolicWindow : LuoParabolicTerminalWindow
    control : LuoCutoffLocalizedMajorant cutoff

    localizedIntegralBelowThreshold :
      localizedLowFrequencyGradientIntegral control
        ≤ bkmThreshold control

open LuoExplicitCutoffCriterionWitness public

majorantToLuoExplicitCutoffCriterion :
  (cutoff : Nat) →
  (window : LuoParabolicTerminalWindow) →
  (control : LuoCutoffLocalizedMajorant cutoff) →
  LuoExplicitCutoffCriterionWitness
majorantToLuoExplicitCutoffCriterion cutoff window control =
  witness
    cutoff
    window
    control
    (luoLocalizedQuantityBelowThreshold cutoff control)

record LuoPeriodicContinuationAuthority : Set₁ where
  field
    explicitCutoffWitness : LuoExplicitCutoffCriterionWitness
    periodicHardLowPassQuantityEqualsLuoLowFrequencyGradientIntegral : Set
    thresholdMatchesLuoUniversalThreshold : Set
    limsupConditionRecoveredFromCutoffWitnesses : Set
    continuationPastTerminalTime : Set

open LuoPeriodicContinuationAuthority public

periodicHardLowPassSupportInterfaceConstructed : Bool
periodicHardLowPassSupportInterfaceConstructed =
  PeriodicLP.periodicHardLowPassProjectorConstructed

cutoffIndexedForcedTailOutputConstructed : Bool
cutoffIndexedForcedTailOutputConstructed = true

forcedTailOutputControlsLuoCutoffQuantity : Bool
forcedTailOutputControlsLuoCutoffQuantity = true

luoParabolicWindowShapeRecorded : Bool
luoParabolicWindowShapeRecorded = true

physicalGradientIntegralIdentificationClosed : Bool
physicalGradientIntegralIdentificationClosed = false

luoLimsupContinuationAuthorityClosed : Bool
luoLimsupContinuationAuthorityClosed = false

cutoffIndexedForcedTailOutputConstructedIsTrue :
  cutoffIndexedForcedTailOutputConstructed ≡ true
cutoffIndexedForcedTailOutputConstructedIsTrue = refl

forcedTailOutputControlsLuoCutoffQuantityIsTrue :
  forcedTailOutputControlsLuoCutoffQuantity ≡ true
forcedTailOutputControlsLuoCutoffQuantityIsTrue = refl

luoParabolicWindowShapeRecordedIsTrue :
  luoParabolicWindowShapeRecorded ≡ true
luoParabolicWindowShapeRecordedIsTrue = refl

physicalGradientIntegralIdentificationClosedIsFalse :
  physicalGradientIntegralIdentificationClosed ≡ false
physicalGradientIntegralIdentificationClosedIsFalse = refl

luoLimsupContinuationAuthorityClosedIsFalse :
  luoLimsupContinuationAuthorityClosed ≡ false
luoLimsupContinuationAuthorityClosedIsFalse = refl
