module DASHI.Governance.CybersynDatedPublicRiskJoinExact where

-- DASHI-original typed dated loss-incidence join, 2026-11-12.
-- Identity/time/source permission and real authority are distinct witnesses.
-- No live world-store admission or observed finance amounts is asserted.
-- See Docs/SourceAttributionPolicy.md.
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Agda.Builtin.String using (String)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Empty using (⊥)

import DASHI.Governance.CybersynGlobalViabilityMaxCutExact as Cyber
import DASHI.Governance.CybersynPublicBackstopLossWaterfallExact as Loss
import DASHI.Governance.CybersynHistoricalMandateWorldBridgeExact as History
import DASHI.Governance.CybersynAuthorityFeedbackExact as Authority
import DASHI.Economics.HistoryIndexedMarketMechanismOODALoopExact as Market
import DASHI.Core.IntersectionalNonFactorability as NonFactor

-- Event IDs are explicit tokens, not a join on abbreviated labels or
-- unverified claims of source identity.
data EventID : Set where
  hypotheticalAIInvestment : EventID
  hypotheticalEnergyShock : EventID

record DatedEvent : Set where
  constructor datedEvent
  field
    eventID : EventID
    observedAt : Nat
    eventDescription : String

open DatedEvent public

-- Exact same-event relation is a proof obligation: two similar prose labels
-- are not sufficient.  Same timestamp additionally requires a witness.
record SameDatedEvent (left right : DatedEvent) : Set where
  constructor sameDatedEvent
  field
    idExact : eventID left ≡ eventID right
    timeExact : observedAt left ≡ observedAt right

open SameDatedEvent public

-- Distinguish source stages from formal proof status and from actual empirical
-- acceptance.  The latter cannot be synthesised from an unvalidated source.
data EmpiricallyAdmitted : Cyber.Admission → Set where
  admittedWithReceipt :
    EmpiricallyAdmitted Cyber.empiricallyValidated

candidateCannotPromoteEmpirical :
  EmpiricallyAdmitted Cyber.candidateOnly → ⊥
candidateCannotPromoteEmpirical ()

sourceCheckedCannotPromoteEmpirical :
  EmpiricallyAdmitted Cyber.sourceChecked → ⊥
sourceCheckedCannotPromoteEmpirical ()

record RiskObservation (event : DatedEvent) : Set where
  constructor riskObservation
  field
    source : Cyber.AttributedSignal
    sourceEventTimeIsExact :
      Cyber.observationTime source ≡ observedAt event
    posting : Loss.LossWaterfall
    programme : EventID
    programmeMatchesEvent : programme ≡ eventID event

open RiskObservation public

-- A risky investment may have two possible loss allocations at the same
-- event identity and time.  The equal headline and total loss are insufficient
-- statistics for public downside.
exampleEvent : DatedEvent
exampleEvent =
  datedEvent hypotheticalAIInvestment zero
    "synthetic infrastructure shock; not a company transaction"

exampleSource : Cyber.AttributedSignal
exampleSource =
  Cyber.signal
    "DASHI synthetic scenario"
    "illustrative, unmeasured, no promoted causal inference"
    Cyber.dashiTheorem Cyber.candidateOnly
    Cyber.government Cyber.investor zero

privateRiskObservation : RiskObservation exampleEvent
privateRiskObservation =
  riskObservation exampleSource refl
    Loss.privateAbsorption hypotheticalAIInvestment refl

publicRiskObservation : RiskObservation exampleEvent
publicRiskObservation =
  riskObservation exampleSource refl
    Loss.publicBackstop hypotheticalAIInvestment refl

sameExactEvent :
  SameDatedEvent exampleEvent exampleEvent
sameExactEvent = sameDatedEvent refl refl

sameTotalRisk :
  Loss.totalLoss (posting privateRiskObservation) ≡
  Loss.totalLoss (posting publicRiskObservation)
sameTotalRisk = refl

differentPublicCost :
  Loss.publicLoss (posting privateRiskObservation) ≡
  Loss.publicLoss (posting publicRiskObservation) → ⊥
differentPublicCost ()

-- For untrusted or mere candidate sources, no checked empirical promotion is
-- available even when the formal arithmetic itself is exact.
noEmpiricalPromotionFromExample :
  EmpiricallyAdmitted (Cyber.admission exampleSource) → ⊥
noEmpiricalPromotionFromExample ()

-- An actual builder must supply exact event identity and source/time evidence;
-- construction of the pairing below cannot silently produce that evidence.
record AdmittedSameEventJoin
    (leftEvent rightEvent : DatedEvent)
    (leftRisk : RiskObservation leftEvent)
    (rightRisk : RiskObservation rightEvent) : Set where
  constructor admittedSameEventJoin
  field
    equalityWitness : SameDatedEvent leftEvent rightEvent
    leftEmpirical : EmpiricallyAdmitted
      (Cyber.admission (source leftRisk))
    rightEmpirical : EmpiricallyAdmitted
      (Cyber.admission (source rightRisk))

open AdmittedSameEventJoin public

-- Pure syntactic join is possible without empirical validation but is strictly
-- weaker.  This must never be used as a real-world authorisation gate.
record CandidateSameEventJoin
    (leftEvent rightEvent : DatedEvent) : Set where
  constructor candidateSameEventJoin
  field
    sameEvent : SameDatedEvent leftEvent rightEvent

open CandidateSameEventJoin public

syntheticJoin : CandidateSameEventJoin exampleEvent exampleEvent
syntheticJoin = candidateSameEventJoin sameExactEvent

-- The same instrument/event identifier does not identify how losses were
-- distributed.  This is an exact non-factorability theorem over two typed
-- candidate scenarios, not a claim about an actual publicly guaranteed loan.
data LossPolicyScenario : Set where
  equityFirst : LossPolicyScenario
  publicGuarantee : LossPolicyScenario

eventProjection : LossPolicyScenario → EventID
eventProjection _ = hypotheticalAIInvestment

publicDownside : LossPolicyScenario → Nat
publicDownside equityFirst = Loss.publicLoss Loss.privateAbsorption
publicDownside publicGuarantee = Loss.publicLoss Loss.publicBackstop

sameRiskEventProjection :
  eventProjection equityFirst ≡ eventProjection publicGuarantee
sameRiskEventProjection = refl

differentScenarioBurden :
  publicDownside equityFirst ≡ publicDownside publicGuarantee → ⊥
differentScenarioBurden ()

eventIdentityCannotRecoverPublicRisk :
  NonFactor.FactorsThrough eventProjection publicDownside → ⊥
eventIdentityCannotRecoverPublicRisk =
  NonFactor.witnessRulesOutEveryFlatFactorisation
    (NonFactor.nonFactorabilityWitness
      equityFirst publicGuarantee
      sameRiskEventProjection differentScenarioBurden)

-- Reused owners preserve mandate and history without manufacturing them.
historyAuthorityOwner :
  History.SameWorldObject EventID
    hypotheticalAIInvestment hypotheticalAIInvestment
historyAuthorityOwner = History.sameWorldObject refl

marketControlBoundary : Market.HistoryIndexedMarketMechanismBoundary
marketControlBoundary = Market.canonicalHistoryIndexedMarketMechanismBoundary

consultationBoundary : Authority.GovernanceAdmission
consultationBoundary = Authority.mereConsultation
