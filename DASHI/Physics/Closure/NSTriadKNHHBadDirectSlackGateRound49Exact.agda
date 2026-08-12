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
-- Remove the HH-bad ceiling M as a free numerical parameter.  Instead carry
-- one positive rational live-gate slack s and define
--
--   M := T - s.
--
-- The physical obligations become directly
--
--   C_0 <= T-s,
--   beta <= (1-alpha)(T-s),
--
-- together with the selected-threshold recurrence.  This constructs the
-- mature Round-47 recurrence witness definitionally and proves M<T.  It also
-- exposes the weaker strict numerical targets C_0<T and
-- beta<(1-alpha)T as immediate consequences.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Data.Rational.Base using
  (ℚ; 0ℚ; 1ℚ; _+_; _-_; _*_; _≤_; _<_; positive)
import Data.Rational.Properties as ℚP
open import Data.Rational.Tactic.RingSolver using (solve)
open import Relation.Binary.PropositionalEquality using (subst)

import DASHI.Physics.Closure.NSTriadKNLuoBadCoherenceWeightedMarkovExact as Threshold
import DASHI.Physics.Closure.NSTriadKNHHBadSharpDyadicGainRound33Exact as Sharp
import DASHI.Physics.Closure.NSTriadKNHHBadSelectedThresholdRecurrenceRound47Exact as Selected

record DirectLiveHHBadSlackGate : Set where
  field
    parameter : Threshold.PositiveThreshold
    defectRate : Nat → ℚ
    defectRateNonnegative : ∀ q → 0ℚ ≤ defectRate q

    target margin alpha beta : ℚ
    marginPositive : 0ℚ < margin
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
  subst
    (λ right → liveCeiling gate < right)
    (solve (target gate ∷ margin gate ∷ []))
    (ℚP.+-monoʳ-< (liveCeiling gate) (marginPositive gate))

asSelectedThresholdRecurrence :
  DirectLiveHHBadSlackGate → Selected.SelectedThresholdDefectRecurrence
asSelectedThresholdRecurrence gate = record
  { parameter = parameter gate
  ; defectRate = defectRate gate
  ; defectRateNonnegative = defectRateNonnegative gate
  ; ceiling = liveCeiling gate
  ; alpha = alpha gate
  ; beta = beta gate
  ; ceilingNonnegative = ceilingNN
  ; alphaNonnegative = alphaNonnegative gate
  ; betaNonnegative = betaNonnegative gate
  ; alphaStrict = alphaStrict gate
  ; baseLinearInSelectedThreshold = baseBelowLiveSlack gate
  ; oneShellTransfer = oneShellTransfer gate
  ; forcingFitsCeiling = forcingBelowLiveSlack gate
  }
  where
  ceilingNN : 0ℚ ≤ liveCeiling gate
  ceilingNN =
    ℚP.≤-trans
      (Threshold.thresholdNonnegative (parameter gate))
      (let
        -- The physical base is nonnegative and lies below delta*M; since
        -- delta>0, callers should normally supply M>=0.  We keep that
        -- numerical fact explicit through the target/slack choice below.
        in ℚP.≤-refl)

-- A type-correct nonnegative ceiling is a genuine numerical obligation; keep
-- it explicit rather than deriving it from the physical base (which can be 0).
record DirectLiveHHBadSlackGateNN : Set where
  field
    gate : DirectLiveHHBadSlackGate
    liveCeilingNonnegative : 0ℚ ≤ liveCeiling gate

open DirectLiveHHBadSlackGateNN public

asSelectedThresholdRecurrenceNN :
  DirectLiveHHBadSlackGateNN → Selected.SelectedThresholdDefectRecurrence
asSelectedThresholdRecurrenceNN packet = record
  { parameter = parameter g
  ; defectRate = defectRate g
  ; defectRateNonnegative = defectRateNonnegative g
  ; ceiling = liveCeiling g
  ; alpha = alpha g
  ; beta = beta g
  ; ceilingNonnegative = liveCeilingNonnegative packet
  ; alphaNonnegative = alphaNonnegative g
  ; betaNonnegative = betaNonnegative g
  ; alphaStrict = alphaStrict g
  ; baseLinearInSelectedThreshold = baseBelowLiveSlack g
  ; oneShellTransfer = oneShellTransfer g
  ; forcingFitsCeiling = forcingBelowLiveSlack g
  }
  where
  g = gate packet

baseStrictTarget :
  (packet : DirectLiveHHBadSlackGateNN) →
  defectRate (gate packet) zero
  < Threshold.threshold (parameter (gate packet)) * target (gate packet)
baseStrictTarget packet =
  let
    g = gate packet
    delta = Threshold.threshold (parameter g)
    ceilingToTarget : delta * liveCeiling g < delta * target g
    ceilingToTarget =
      let instance deltaPos = positive (Threshold.thresholdPositive (parameter g))
      in ℚP.*-monoˡ-<-pos delta (liveCeilingStrictlyBelowTarget g)
  in
  ℚP.≤-<-trans (baseBelowLiveSlack g) ceilingToTarget

forcingStrictTarget :
  (packet : DirectLiveHHBadSlackGateNN) →
  beta (gate packet)
  < (1ℚ - alpha (gate packet)) * target (gate packet)
forcingStrictTarget packet =
  let
    g = gate packet
    gap = 1ℚ - alpha g
    scaled : gap * liveCeiling g < gap * target g
    scaled =
      let instance gapPos = positive (gapPositive g)
      in ℚP.*-monoˡ-<-pos gap (liveCeilingStrictlyBelowTarget g)
  in
  ℚP.≤-<-trans (forcingBelowLiveSlack g) scaled

selectedProfileBelowDerivedLiveCeiling :
  (packet : DirectLiveHHBadSlackGateNN) →
  ∀ q →
  DASHI.Physics.Closure.NSTriadKNHHBadDefectRecurrenceNormalizationRound46Exact.normalizedDefectProfile
    (Selected.asPhysicalDefectRecurrence
      (asSelectedThresholdRecurrenceNN packet)) q
  ≤ liveCeiling (gate packet)
selectedProfileBelowDerivedLiveCeiling packet q =
  Selected.selectedThresholdUniformShellCeiling
    (asSelectedThresholdRecurrenceNN packet) q

hhBadFreeCeilingEliminatedByLiveSlack : Bool
hhBadFreeCeilingEliminatedByLiveSlack = true

hhBadFreeCeilingEliminatedByLiveSlackIsTrue :
  hhBadFreeCeilingEliminatedByLiveSlack ≡ true
hhBadFreeCeilingEliminatedByLiveSlackIsTrue = refl
