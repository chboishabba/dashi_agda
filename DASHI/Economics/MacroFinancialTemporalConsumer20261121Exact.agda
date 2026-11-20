module DASHI.Economics.MacroFinancialTemporalConsumer20261121Exact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)
import DASHI.Economics.JPYJGBTreasuryFundingTransmission2026Exact as Yen
import DASHI.Economics.AIGlobalFundingRegulatorySynthesisExact as Global
import DASHI.Economics.AICapitalObservedStateTimeSeries2026Exact as Capital
import DASHI.Economics.AICapitalOutcomeCompatibility20261016Exact as Outcome
import DASHI.Economics.ChinaRetailGoldMarketTopology2026Exact as Gold
import DASHI.Economics.AICapitalBurdenRelocation20261012Exact as Burden
import DASHI.Core.ConsumerDescentMinimalObserverExact as Descent

-- Relative clock ticks on a common declared timeline, not calendar parsing.
-- A historical event can be disclosed later; a plan is not settlement.
data AtMost : Nat → Nat → Set where
  zeroAtMost : ∀ {n} → AtMost zero n
  stepAtMost : ∀ {m n} → AtMost m n → AtMost (suc m) (suc n)

data SettlementClock : Set where
  settlementUnknown : SettlementClock
  settlementAt : Nat → SettlementClock

record TemporalAttachment (asOf : Nat) : Set where
  constructor temporalAttachment
  field
    scope : String
    actor : String
    sourceId : String
    eventTick : Nat
    disclosureTick : Nat
    actorKnowledgeTick : Nat
    eventBeforeCut : AtMost eventTick asOf
    disclosureBeforeCut : AtMost disclosureTick asOf
    knowledgeBeforeCut : AtMost actorKnowledgeTick asOf
    settlement : SettlementClock

open TemporalAttachment public

-- Settlement admission is a separate typed witness, never inferred from disclosure.
record SettledBy {asOf : Nat} (a : TemporalAttachment asOf) : Set where
  field
    tick : Nat
    settlementMatches : settlement a ≡ settlementAt tick
    settlementBeforeCut : AtMost tick asOf

record ExistingStateAttachment (asOf : Nat) : Set where
  field
    timeline : TemporalAttachment asOf
    coupledState : Global.CoupledState
    capitalPoint : Capital.ObservedCapitalStatePoint
    goldBoundary : Gold.ChinaRetailGoldTopologyBoundary
    burdenState : Burden.CapitalBurdenState

-- The intent coordinate is deliberately a synthetic rival-world discriminator.
-- Identical observed economics can coexist with distinct intended objectives.
data CorrectionObjective : Set where
  endogenousCorrection deliberateTolerance deliberateInduction : CorrectionObjective

record RivalWorld (asOf : Nat) : Set where
  constructor rivalWorld
  field
    observed : ExistingStateAttachment asOf
    objective : CorrectionObjective

open RivalWorld public

sameObservationDifferentObjective :
  ∀ {t} (s : ExistingStateAttachment t) →
  Descent.ConsumerNonDescentWitness
    (observed {asOf = t}) (objective {asOf = t})
sameObservationDifferentObjective s =
  Descent.consumerNonDescentWitness
    (rivalWorld s endogenousCorrection)
    (rivalWorld s deliberateInduction)
    refl (λ ())

observationDoesNotDetermineIntent :
  ∀ {t} (s : ExistingStateAttachment t) →
  Descent.FactorsThrough
    (observed {asOf = t}) (objective {asOf = t}) → ⊥
observationDoesNotDetermineIntent s =
  Descent.nonDescentWitnessBlocksFactorization
    (sameObservationDifferentObjective s)

-- Existing alternative-regime fits are retained, not assigned to new actors.
existingRefinancingFit : Outcome.OutcomeFit
existingRefinancingFit = Outcome.refinancingStressFit

existingYenBridge : Yen.CrossMarketFundingBridge
existingYenBridge = Yen.candidateCrossMarketBridge
