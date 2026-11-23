module DASHI.Biology.BH4StimulantResponseCountermodelExact where

-- Synthetic finite observation obstruction; no clinical or kinetic claim.
-- Reuses existing catalytic capacity, not irreversible cofactor consumption.
open import DASHI.Core.Prelude
import DASHI.Biology.BH4CatalyticTurnoverFutureCountermodelExact as C

record Window : Set where
  constructor window
  field
    capacity : C.CatalyticCapacityScenario
    synthesis unusedCapacity initialReserve basalRelease extraRelease finalReserve : Nat
    capacityBound : synthesis + unusedCapacity ≡ C.selectedTurnoverCapacity capacity
    reserveBalance : initialReserve + synthesis ≡ basalRelease + extraRelease + finalReserve

open Window public

record Observation : Set where
  constructor observation
  field
    baselineScaled methylphenidateScaled amphetamineScaled : Nat

-- Fixed common toy clearance 2, 1, 1; all rational observations scaled by 2.
-- The balance accounts for the maximum-release window, not a drug sequence.
observe : Window → Observation
observe x = observation (basalRelease x) (2 * basalRelease x)
  (2 * (basalRelease x + extraRelease x))

pool : Window → Nat
pool x = C.availableCofactorMolecules (capacity x)

lowPool highPool unusedTurnover : Window
lowPool = window C.slowCycle 1 0 3 1 1 2 refl refl
highPool = window (C.catalytic-capacity-scenario 2 1 2 refl) 2 0 2 1 1 2 refl refl
unusedTurnover = window (C.catalytic-capacity-scenario 2 2 4 refl) 1 3 3 1 1 2 refl refl

sameObservation : observe lowPool ≡ observe highPool
sameObservation = refl

sameUnusedObservation : observe lowPool ≡ observe unusedTurnover
sameUnusedObservation = refl

differentPool : pool lowPool ≡ pool highPool → ⊥
differentPool ()

differentSynthesis : synthesis lowPool ≡ synthesis highPool → ⊥
differentSynthesis ()

observationDoesNotIdentify : (target : Window → Nat)
  (a b : Window) → observe a ≡ observe b →
  (target a ≡ target b → ⊥) →
  (predict : Observation → Nat) →
  ((x : Window) → target x ≡ predict (observe x)) → ⊥
observationDoesNotIdentify target a b same different predict factors =
  different (trans (factors a) (trans (cong predict same) (sym (factors b))))

stimulantObservationDoesNotIdentifyPool :
  (predict : Observation → Nat) →
  ((x : Window) → pool x ≡ predict (observe x)) → ⊥
stimulantObservationDoesNotIdentifyPool =
  observationDoesNotIdentify pool lowPool highPool sameObservation differentPool

stimulantObservationDoesNotIdentifySynthesis :
  (predict : Observation → Nat) →
  ((x : Window) → synthesis x ≡ predict (observe x)) → ⊥
stimulantObservationDoesNotIdentifySynthesis =
  observationDoesNotIdentify synthesis lowPool highPool sameObservation differentSynthesis

-- Identical synthesis and response are also compatible with different pool sizes.
sameSynthesisDifferentPool : pool lowPool ≡ pool unusedTurnover → ⊥
sameSynthesisDifferentPool ()

sameSynthesisAcrossPools : synthesis lowPool ≡ synthesis unusedTurnover
sameSynthesisAcrossPools = refl

-- S3 finite observation refinement: explicit transfer ledgers, not kinetics.
-- Synthesis is an external catecholamine source, not BH4 consumption.
record Stock : Set where
  constructor stock
  field
    cytosolic vesicular extracellular : Nat

open Stock public

record TransferStep (before : Stock) (newSynthesis : Nat) : Set where
  constructor transfer-step
  field
    after : Stock
    packing exocytosis efflux reuptake cytLoss extLoss : Nat
    cytBalance :
      cytosolic before + newSynthesis + reuptake
        ≡ cytosolic after + packing + efflux + cytLoss
    vesBalance : vesicular before + packing ≡ vesicular after + exocytosis
    extBalance :
      extracellular before + exocytosis + efflux
        ≡ extracellular after + reuptake + extLoss

open TransferStep public

-- Matched one-step alternatives, NOT sequential administration.
record MatchedChallenges : Set where
  constructor matched-challenges
  field
    challengeCapacity : C.CatalyticCapacityScenario
    challengeSynthesis challengeUnused : Nat
    challengeBound :
      challengeSynthesis + challengeUnused ≡
        C.selectedTurnoverCapacity challengeCapacity
    challengeInitial : Stock
    baselineStep methylStep ampStep :
      TransferStep challengeInitial challengeSynthesis

open MatchedChallenges public

record EndpointObservation : Set where
  constructor endpoints
  field
    initialExt baselineExt methylExt ampExt : Nat

observeEndpoints : MatchedChallenges → EndpointObservation
observeEndpoints x = endpoints (extracellular (challengeInitial x))
  (extracellular (after (baselineStep x)))
  (extracellular (after (methylStep x)))
  (extracellular (after (ampStep x)))

resolvedPool : MatchedChallenges → Nat
resolvedPool x = C.availableCofactorMolecules (challengeCapacity x)

commonInitial : Stock
commonInitial = stock 2 2 1

resolvedLow resolvedHigh resolvedGross : MatchedChallenges
resolvedLow = matched-challenges C.slowCycle 1 0 refl commonInitial
  (transfer-step (stock 4 1 1) 0 1 0 1 0 0 refl refl refl)
  (transfer-step (stock 3 1 2) 0 1 0 0 0 0 refl refl refl)
  (transfer-step (stock 2 1 3) 0 1 1 0 0 0 refl refl refl)
resolvedHigh = matched-challenges
  (C.catalytic-capacity-scenario 2 1 2 refl) 2 0 refl commonInitial
  (transfer-step (stock 5 1 1) 0 1 0 1 0 0 refl refl refl)
  (transfer-step (stock 4 1 2) 0 1 0 0 0 0 refl refl refl)
  (transfer-step (stock 3 1 3) 0 1 1 0 0 0 refl refl refl)
resolvedGross = matched-challenges C.slowCycle 1 0 refl commonInitial
  (transfer-step (stock 5 0 1) 0 2 0 2 0 0 refl refl refl)
  (transfer-step (stock 4 0 2) 0 2 0 1 0 0 refl refl refl)
  (transfer-step (stock 3 0 3) 0 2 1 1 0 0 refl refl refl)

resolvedSameEndpoints : observeEndpoints resolvedLow ≡ observeEndpoints resolvedHigh
resolvedSameEndpoints = refl

grossSameEndpoints : observeEndpoints resolvedLow ≡ observeEndpoints resolvedGross
grossSameEndpoints = refl

resolvedSameInitial : challengeInitial resolvedLow ≡ challengeInitial resolvedHigh
resolvedSameInitial = refl

resolvedDifferentPool : resolvedPool resolvedLow ≡ resolvedPool resolvedHigh → ⊥
resolvedDifferentPool ()

resolvedDifferentSynthesis :
  challengeSynthesis resolvedLow ≡ challengeSynthesis resolvedHigh → ⊥
resolvedDifferentSynthesis ()

basalGrossRelease : MatchedChallenges → Nat
basalGrossRelease x = exocytosis (baselineStep x)

grossDifferentRelease : basalGrossRelease resolvedLow ≡ basalGrossRelease resolvedGross → ⊥
grossDifferentRelease ()

endpointNonIdentification : (target : MatchedChallenges → Nat)
  (a b : MatchedChallenges) → observeEndpoints a ≡ observeEndpoints b →
  (target a ≡ target b → ⊥) →
  (predict : EndpointObservation → Nat) →
  ((x : MatchedChallenges) → target x ≡ predict (observeEndpoints x)) → ⊥
endpointNonIdentification target a b same different predict factors =
  different (trans (factors a) (trans (cong predict same) (sym (factors b))))

endpointsDoNotIdentifyPool :
  (predict : EndpointObservation → Nat) →
  ((x : MatchedChallenges) → resolvedPool x ≡ predict (observeEndpoints x)) → ⊥
endpointsDoNotIdentifyPool = endpointNonIdentification resolvedPool resolvedLow
  resolvedHigh resolvedSameEndpoints resolvedDifferentPool

endpointsDoNotIdentifySynthesis :
  (predict : EndpointObservation → Nat) →
  ((x : MatchedChallenges) → challengeSynthesis x ≡ predict (observeEndpoints x)) → ⊥
endpointsDoNotIdentifySynthesis = endpointNonIdentification challengeSynthesis
  resolvedLow resolvedHigh resolvedSameEndpoints resolvedDifferentSynthesis

endpointsDoNotIdentifyGrossRelease :
  (predict : EndpointObservation → Nat) →
  ((x : MatchedChallenges) → basalGrossRelease x ≡ predict (observeEndpoints x)) → ⊥
endpointsDoNotIdentifyGrossRelease = endpointNonIdentification basalGrossRelease
  resolvedLow resolvedGross grossSameEndpoints grossDifferentRelease

-- These two extra observations split the respective displayed collisions only.
terminalCytSplitsSynthesisWitness :
  cytosolic (after (baselineStep resolvedLow)) ≡
    cytosolic (after (baselineStep resolvedHigh)) → ⊥
terminalCytSplitsSynthesisWitness ()

terminalVesSplitsGrossWitness :
  vesicular (after (baselineStep resolvedLow)) ≡
    vesicular (after (baselineStep resolvedGross)) → ⊥
terminalVesSplitsGrossWitness ()

-- S4c.6 situated finite release witness: same integrated count, distinct
-- chronological consumer. These are event counts, not physical kinetics.
-- Reuse the original generic residual and descent owners.
import DASHI.Core.ConsumerIndexedResidualRefinementExact as SituatedResidual
import DASHI.Core.ConsumerDescentMinimalObserverExact as SituatedDescent

record OrderedReleaseWindows : Set where
  constructor ordered-release-windows
  field
    earlyRelease lateRelease : Nat

open OrderedReleaseWindows public

integratedRelease : OrderedReleaseWindows → Nat
integratedRelease x = earlyRelease x + lateRelease x

earlyHistory lateHistory : OrderedReleaseWindows
earlyHistory = ordered-release-windows 1 0
lateHistory = ordered-release-windows 0 1

sameIntegratedRelease : integratedRelease earlyHistory ≡ integratedRelease lateHistory
sameIntegratedRelease = refl

differentEarlyRelease : earlyRelease earlyHistory ≡ earlyRelease lateHistory → ⊥
differentEarlyRelease ()

earlyReleaseCollision :
  SituatedResidual.ConsumerRelevantCollision integratedRelease earlyRelease
earlyReleaseCollision = SituatedResidual.consumer-relevant-collision
  earlyHistory lateHistory sameIntegratedRelease differentEarlyRelease

integratedReleaseAdequateForTotal :
  SituatedDescent.ConsumerSufficient integratedRelease integratedRelease
integratedReleaseAdequateForTotal =
  SituatedDescent.consumerObserverIsSufficient integratedRelease

integratedReleaseNotAdequateForEarly :
  SituatedResidual.ConsumerSufficient integratedRelease earlyRelease → ⊥
integratedReleaseNotAdequateForEarly =
  SituatedResidual.coarseCollisionBlocksSufficiency earlyReleaseCollision
