module DASHI.Physics.Closure.NSTriadKNHHBadDirectSlackGateRound49Exact where

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
-- Eliminate the HH-bad ceiling M as a free numerical parameter. Carry one
-- positive rational live-gate slack s and define M := T-s. The physical
-- obligations become C_0 <= T-s and beta <= (1-alpha)(T-s), together with
-- the selected-threshold recurrence. The mature Round-47 recurrence witness
-- is then constructed definitionally and M<T is proved exactly.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Data.Rational.Base using
  (ℚ; 0ℚ; 1ℚ; _+_; _-_; _*_; _≤_; _<_; positive)
import Data.Rational.Properties as ℚP
open import Data.Rational.Tactic.RingSolver using (solve)
open import Relation.Binary.PropositionalEquality using (subst₂)

import DASHI.Physics.Closure.NSTriadKNLuoBadCoherenceWeightedMarkovExact as Threshold
import DASHI.Physics.Closure.NSTriadKNHHBadSharpDyadicGainRound33Exact as Sharp
import DASHI.Physics.Closure.NSTriadKNHHBadSelectedThresholdRecurrenceRound47Exact as Selected
import DASHI.Physics.Closure.NSTriadKNHHBadDefectRecurrenceNormalizationRound46Exact as Defect

record DirectLiveHHBadSlackGate : Set where
  field
    parameter : Threshold.PositiveThreshold
    defectRate : Nat → ℚ
    defectRateNonnegative : ∀ q → 0ℚ ≤ defectRate q

    target margin alpha beta : ℚ
    marginPositive : 0ℚ < margin
    liveCeilingNonnegative : 0ℚ ≤ target - margin
    alphaNonnegative : 0ℚ ≤ alpha
    betaNonnegative : 0ℚ ≤ beta
    alphaStrict : alpha < 1ℚ
    gapPositive : 0ℚ < 1ℚ - alpha

    baseBelowLiveSlack :
      defectRate zero
      ≤ Threshold.threshold parameter * (target - margin)

    oneShellTransfer : ∀ q →
      defectRate (suc q)
      ≤ alpha * Sharp.half * defectRate q
        + Threshold.threshold parameter
          * Sharp.inverseDyadicScale (suc q) * beta

    forcingBelowLiveSlack :
      beta ≤ (1ℚ - alpha) * (target - margin)

open DirectLiveHHBadSlackGate public

liveCeiling : DirectLiveHHBadSlackGate → ℚ
liveCeiling gate = target gate - margin gate

liveCeilingStrictlyBelowTarget :
  (gate : DirectLiveHHBadSlackGate) →
  liveCeiling gate < target gate
liveCeilingStrictlyBelowTarget gate =
  let
    shifted :
      0ℚ + liveCeiling gate < margin gate + liveCeiling gate
    shifted = ℚP.+-monoʳ-< (liveCeiling gate) (marginPositive gate)

    leftMeaning : 0ℚ + liveCeiling gate ≡ liveCeiling gate
    leftMeaning = solve (target gate ∷ margin gate ∷ [])

    rightMeaning : margin gate + liveCeiling gate ≡ target gate
    rightMeaning = solve (target gate ∷ margin gate ∷ [])
  in
  subst₂ _<_ leftMeaning rightMeaning shifted

asSelectedThresholdRecurrence :
  DirectLiveHHBadSlackGate → Selected.SelectedThresholdDefectRecurrence
asSelectedThresholdRecurrence gate = record
  { parameter = parameter gate
  ; defectRate = defectRate gate
  ; defectRateNonnegative = defectRateNonnegative gate
  ; ceiling = liveCeiling gate
  ; alpha = alpha gate
  ; beta = beta gate
  ; ceilingNonnegative = liveCeilingNonnegative gate
  ; alphaNonnegative = alphaNonnegative gate
  ; betaNonnegative = betaNonnegative gate
  ; alphaStrict = alphaStrict gate
  ; baseLinearInSelectedThreshold = baseBelowLiveSlack gate
  ; oneShellTransfer = oneShellTransfer gate
  ; forcingFitsCeiling = forcingBelowLiveSlack gate
  }

baseStrictTarget :
  (gate : DirectLiveHHBadSlackGate) →
  defectRate gate zero
  < Threshold.threshold (parameter gate) * target gate
baseStrictTarget gate =
  let
    delta = Threshold.threshold (parameter gate)
    ceilingToTarget : delta * liveCeiling gate < delta * target gate
    ceilingToTarget =
      let instance deltaPos = positive (Threshold.thresholdPositive (parameter gate))
      in ℚP.*-monoʳ-<-pos delta (liveCeilingStrictlyBelowTarget gate)
  in
  ℚP.≤-<-trans (baseBelowLiveSlack gate) ceilingToTarget

forcingStrictTarget :
  (gate : DirectLiveHHBadSlackGate) →
  beta gate < (1ℚ - alpha gate) * target gate
forcingStrictTarget gate =
  let
    gap = 1ℚ - alpha gate
    scaled : gap * liveCeiling gate < gap * target gate
    scaled =
      let instance gapPos = positive (gapPositive gate)
      in ℚP.*-monoʳ-<-pos gap (liveCeilingStrictlyBelowTarget gate)
  in
  ℚP.≤-<-trans (forcingBelowLiveSlack gate) scaled

selectedProfileBelowDerivedLiveCeiling :
  (gate : DirectLiveHHBadSlackGate) →
  ∀ q →
  Defect.normalizedDefectProfile
    (Selected.asPhysicalDefectRecurrence
      (asSelectedThresholdRecurrence gate)) q
  ≤ liveCeiling gate
selectedProfileBelowDerivedLiveCeiling gate q =
  Selected.selectedThresholdUniformShellCeiling
    (asSelectedThresholdRecurrence gate) q

hhBadFreeCeilingEliminatedByLiveSlack : Bool
hhBadFreeCeilingEliminatedByLiveSlack = true

hhBadFreeCeilingEliminatedByLiveSlackIsTrue :
  hhBadFreeCeilingEliminatedByLiveSlack ≡ true
hhBadFreeCeilingEliminatedByLiveSlackIsTrue = refl
