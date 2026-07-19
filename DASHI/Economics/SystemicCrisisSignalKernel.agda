module DASHI.Economics.SystemicCrisisSignalKernel where

open import DASHI.Core.Prelude
open import DASHI.Algebra.Trit using (Trit; neg; zer; pos)

------------------------------------------------------------------------
-- Mechanism-first systemic-risk state machine.
--
-- Every observable is triadic:
--   neg = normalising / absent
--   zer = unresolved / insufficient evidence
--   pos = stressed / present
--
-- A price narrative is deliberately not an input to the mechanism classifier.
-- Promotion requires jointly observed funding, liquidity, contagion, safe-haven,
-- and forced-selling evidence.
------------------------------------------------------------------------

infixr 6 _∧_
infixr 5 _∨_

_∧_ : Bool → Bool → Bool
true  ∧ b = b
false ∧ _ = false

_∨_ : Bool → Bool → Bool
true  ∨ _ = true
false ∨ b = b

isPositive : Trit → Bool
isPositive neg = false
isPositive zer = false
isPositive pos = true

isNotPositive : Trit → Bool
isNotPositive neg = true
isNotPositive zer = true
isNotPositive pos = false

atLeastTwo : Trit → Trit → Trit → Bool
atLeastTwo a b c =
  (isPositive a ∧ isPositive b)
  ∨ (isPositive a ∧ isPositive c)
  ∨ (isPositive b ∧ isPositive c)

record CrisisObservation : Set where
  constructor observation
  field
    fundingStress         : Trit
    liquidityImpairment   : Trit
    crossAssetContagion   : Trit
    safeHavenFailure      : Trit
    forcedSelling         : Trit
    policyBackstop        : Trit
    mechanicalExhaustion  : Trit

open CrisisObservation public

data CrisisPhase : Set where
  normalPhase     : CrisisPhase
  fragilityPhase  : CrisisPhase
  proximityPhase  : CrisisPhase
  activePhase     : CrisisPhase
  abatingPhase    : CrisisPhase

------------------------------------------------------------------------
-- Evidence gates.
------------------------------------------------------------------------

latentFragility : CrisisObservation → Bool
latentFragility o =
  atLeastTwo
    (fundingStress o)
    (liquidityImpairment o)
    (crossAssetContagion o)

triggerProximity : CrisisObservation → Bool
triggerProximity o =
  isPositive (fundingStress o)
  ∧ isPositive (crossAssetContagion o)
  ∧ isPositive (safeHavenFailure o)

marketFunctionBreak : CrisisObservation → Bool
marketFunctionBreak o =
  isPositive (fundingStress o)
  ∧ isPositive (liquidityImpairment o)
  ∧ isPositive (forcedSelling o)

mechanicalRecovery : CrisisObservation → Bool
mechanicalRecovery o =
  isPositive (policyBackstop o)
  ∧ isPositive (mechanicalExhaustion o)
  ∧ isNotPositive (fundingStress o)
  ∧ isNotPositive (liquidityImpairment o)

------------------------------------------------------------------------
-- Instantaneous classification and hysteretic transition.
------------------------------------------------------------------------

instantPhase : CrisisObservation → CrisisPhase
instantPhase o with marketFunctionBreak o
... | true  = activePhase
... | false with triggerProximity o
...   | true  = proximityPhase
...   | false with latentFragility o
...     | true  = fragilityPhase
...     | false = normalPhase

stepPhase : CrisisPhase → CrisisObservation → CrisisPhase
stepPhase normalPhase o = instantPhase o
stepPhase fragilityPhase o = instantPhase o
stepPhase proximityPhase o = instantPhase o
stepPhase activePhase o with marketFunctionBreak o
... | true  = activePhase
... | false with mechanicalRecovery o
...   | true  = abatingPhase
...   | false = activePhase
stepPhase abatingPhase o with marketFunctionBreak o
... | true  = activePhase
... | false with latentFragility o
...   | true  = fragilityPhase
...   | false = normalPhase

------------------------------------------------------------------------
-- Operational posture. This is a diagnostic control surface, not a price
-- forecast and not a claim that a sovereign crisis must follow.
------------------------------------------------------------------------

data CrisisPosture : Set where
  monitorPosture   : CrisisPosture
  reduceRiskPosture : CrisisPosture
  preserveLiquidityPosture : CrisisPosture
  reengageCautiouslyPosture : CrisisPosture

posture : CrisisPhase → CrisisPosture
posture normalPhase    = monitorPosture
posture fragilityPhase = monitorPosture
posture proximityPhase = reduceRiskPosture
posture activePhase    = preserveLiquidityPosture
posture abatingPhase   = reengageCautiouslyPosture

------------------------------------------------------------------------
-- Narrative non-promotion boundary.
------------------------------------------------------------------------

record PublicNarrative : Set where
  constructor narrative
  field
    singleAssetDrawdownClaim : Trit
    deterministicTimelineClaim : Bool
    sovereignCrisisClaim : Bool

classifyWithNarrative : CrisisObservation → PublicNarrative → CrisisPhase
classifyWithNarrative o _ = instantPhase o

narrativeIrrelevance :
  (o : CrisisObservation) (n₁ n₂ : PublicNarrative) →
  classifyWithNarrative o n₁ ≡ classifyWithNarrative o n₂
narrativeIrrelevance o n₁ n₂ = refl

noPlumbingNoCrisis :
  (safe forced policy exhausted : Trit) →
  instantPhase
    (observation neg neg neg safe forced policy exhausted)
  ≡ normalPhase
noPlumbingNoCrisis safe forced policy exhausted = refl
