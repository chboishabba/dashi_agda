module DASHI.Governance.CybersynGlobalViabilityMaxCutExact where

-- DASHI-original formal bridge, 2026-11-12.
-- This module reuses existing typed owners.  It does not attribute its finite
-- Agda constructions to Beer, Allende, Kimmerer, Zizek, Marx or Indigenous
-- communities; see Docs/SourceAttributionPolicy.md.
--
-- Source/context owners:
--   DASHI.Core.GeneralizedRoleUnifiedDomains (cybernetic role family)
--   DASHI.Governance.CyberneticClinicalInstitutionalRepairBridge
--   DASHI.Core.PluralEpistemicOperationalClosureExact
--   DASHI.Culture.KimmererTwoEyedSeeingInterpretationBoundaryExact
--   DASHI.Core.IntergenerationalPlanningHorizonExact
--   DASHI.Reasoning.PNFZizekOperator
--   DASHI.Economics.AIGlobalFundingRegulatorySynthesisExact
--   DASHI.Economics.JPYJGBTreasuryFundingTransmission2026Exact
--   DASHI.Economics.AISafetyRegulatoryMoatGameExact
--
-- Attribution boundary: original conceptual lenses remain owned by their
-- source authors/communities; formal counterexamples and interface types are
-- DASHI constructions.  No empirical claims are promoted by this module.

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Core.GeneralizedRoleUnifiedDomains as Roles
import DASHI.Governance.CyberneticClinicalInstitutionalRepairBridge as Governance
import DASHI.Core.PluralEpistemicOperationalClosureExact as Plural
import DASHI.Culture.KimmererTwoEyedSeeingInterpretationBoundaryExact as TwoEyed
import DASHI.Core.IntergenerationalPlanningHorizonExact as Horizons
import DASHI.Core.IntersectionalNonFactorability as NonFactor
import DASHI.Reasoning.PNFZizekOperator as Zizek
import DASHI.Economics.AIGlobalFundingRegulatorySynthesisExact as Finance
import DASHI.Economics.JPYJGBTreasuryFundingTransmission2026Exact as Yen
import DASHI.Economics.AISafetyRegulatoryMoatGameExact as Regulation

infixr 6 _and_
_and_ : Bool → Bool → Bool
true and b = b
false and _ = false

-- Authority, evidence, and effects must not be inferred from shared signals.
data ActorRole : Set where
  affectedCommunity government investor insurer lender worker
    ecologicalSteward coordinatingFederation : ActorRole

data SourceLayer : Set where
  externalClaim dashiReconstruction dashiInference dashiTheorem
    empiricalAdmission : SourceLayer

data Admission : Set where
  candidateOnly sourceChecked independentlyCorroborated
    empiricallyValidated : Admission

record AttributedSignal : Set where
  constructor signal
  field
    sourceIdentifier : String
    claimBoundary : String
    claimLayer : SourceLayer
    admission : Admission
    sourceAuthority : ActorRole
    observer : ActorRole
    observationTime : Nat

open AttributedSignal public

-- The temporal hyperfabric has typed roles, states, events, source receipts
-- and actor-dependent observation and response operators.  Its carrier is
-- independent of any single economic ontology.
record TimeIndexedCybersyn
  (State Action Observation Effect Authority : Set) : Set₁ where
  field
    step : Nat → State → Action → State
    observe : ActorRole → Nat → State → Observation
    realisedEffect : Nat → State → Effect
    hasAuthority : ActorRole → Nat → State → Authority
    intervention : ActorRole → Nat → Observation → Action
    outcomeAfter : ActorRole → Nat → State → State
    outcomeAfterLaw : (a : ActorRole) (t : Nat) (s : State) →
      outcomeAfter a t s ≡
      step t s (intervention a t (observe a t s))

open TimeIndexedCybersyn public

-- A coordination model is not complete merely because sensing and control
-- operators are defined: it must carry material and democratic closures.
record ViabilityGates : Set where
  constructor viabilityGates
  field
    householdProvisioning : Bool
    ecologicalIntegrity : Bool
    intergenerationalContinuity : Bool
    infrastructureContinuity : Bool
    financialSettlement : Bool
    affectedPeopleAuthority : Bool
    correctionOperational : Bool
    evidenceSourceAdmitted : Bool

open ViabilityGates public

viable : ViabilityGates → Bool
viable g =
  householdProvisioning g and
  ecologicalIntegrity g and
  intergenerationalContinuity g and
  infrastructureContinuity g and
  financialSettlement g and
  affectedPeopleAuthority g and
  correctionOperational g and
  evidenceSourceAdmitted g

-- Counterexample: a financed, physically operating project is not thereby
-- socially/ecologically viable.  This is a finite DASHI witness, not a
-- claim about NEXTDC or any particular development.
financedButUnaccountable : ViabilityGates
financedButUnaccountable =
  viabilityGates true false false true true false false false

financedButUnaccountableNotViable :
  viable financedButUnaccountable ≡ false
financedButUnaccountableNotViable = refl

allGatesPaid : ViabilityGates
allGatesPaid = viabilityGates true true true true true true true true

allGatesPaidIsViable : viable allGatesPaid ≡ true
allGatesPaidIsViable = refl

-- Local headline/announced investment can be identical while observed
-- community outcomes and authority differ.  Hence no flattening of the
-- latter into an investment headline can be valid for all states.
data ToyPolicyState : Set where
  announcedOnly accountableDelivery : ToyPolicyState

data InvestmentHeadline : Set where
  promisedCapital : InvestmentHeadline

data CommunityResult : Set where
  unresolvedHarm repairedWithAuthority : CommunityResult

headline : ToyPolicyState → InvestmentHeadline
headline _ = promisedCapital

communityResult : ToyPolicyState → CommunityResult
communityResult announcedOnly = unresolvedHarm
communityResult accountableDelivery = repairedWithAuthority

sameHeadline :
  headline announcedOnly ≡ headline accountableDelivery
sameHeadline = refl

differentCommunityResult :
  communityResult announcedOnly ≡
  communityResult accountableDelivery → ⊥
differentCommunityResult ()

headlineCannotRecoverCommunityResult :
  NonFactor.FactorsThrough headline communityResult → ⊥
headlineCannotRecoverCommunityResult =
  NonFactor.witnessRulesOutEveryFlatFactorisation
    (NonFactor.nonFactorabilityWitness
      announcedOnly accountableDelivery
      sameHeadline differentCommunityResult)

-- Time-indexed critical cut: an action can change the feasible
-- infrastructure state despite unchanged financial ownership.  The toy
-- illustrates a dependency cut, not a causal estimate for a listed company.
data AccessState : Set where
  constructionAccessBlocked constructionAccessOpen : AccessState

data AccessAction : Set where
  noChange negotiatedAccess : AccessAction

accessStep : Nat → AccessState → AccessAction → AccessState
accessStep _ s noChange = s
accessStep _ _ negotiatedAccess = constructionAccessOpen

noChangePreservesBlock : (t : Nat) →
  accessStep t constructionAccessBlocked noChange ≡ constructionAccessBlocked
noChangePreservesBlock t = refl

negotiationChangesFeasibility : (t : Nat) →
  accessStep t constructionAccessBlocked negotiatedAccess ≡ constructionAccessOpen
negotiationChangesFeasibility t = refl

-- Explicitly keep selected philosophy / knowledge lenses source-bounded.
cybersynOwner : Roles.RoleFamily
cybersynOwner = Roles.cyberneticDomain

systemFiveOwner : Governance.GovernanceGateRow
systemFiveOwner = Governance.cybersynSystemFiveRow

pluralOperationalOwner : Plural.PluralEvidenceAssessment
pluralOperationalOwner = Plural.canonicalPluralEvidenceAssessment

twoEyedOwner : TwoEyed.KimmererTwoEyedSeeingBoundary
twoEyedOwner = TwoEyed.canonicalKimmererTwoEyedSeeingBoundary

intergenerationalOwner : Horizons.IntergenerationalPlanningBoundary
intergenerationalOwner = Horizons.canonicalIntergenerationalPlanningBoundary

zizekOwner : Zizek.PNFZizekAuthorityBoundary
zizekOwner = Zizek.canonicalPNFZizekAuthorityBoundary

-- No fusion of source histories; a shared observation is not the authority
-- to use a source or speak for the community that produced it.
sameEcologicalObservationDoesNotFuseHistories :
  NonFactor.FactorsThrough
    TwoEyed.observeKnowledgeHistory TwoEyed.provenance → ⊥
sameEcologicalObservationDoesNotFuseHistories =
  TwoEyed.sharedObservationDoesNotRecoverProvenance

-- No unlicensed promotion from financial/policy signals to economic success.
policySupportCannotProveViability :
  Finance.CoupledSignalsImplyCertainCrashPermission → ⊥
policySupportCannotProveViability = Finance.couplingDoesNotAutoProveCertainCrash

yenAppreciationCannotProveGlobalCollapse :
  Yen.YenAppreciationImpliesGlobalCrisisPermission → ⊥
yenAppreciationCannotProveGlobalCollapse =
  Yen.yenAppreciationDoesNotAutoCauseGlobalCrisis

regulatoryMoatCannotProveConspiracy :
  Regulation.RegulatoryMoatImpliesConspiracyPermission → ⊥
regulatoryMoatCannotProveConspiracy =
  Regulation.moatDoesNotAutoProveConspiracy

-- Cross-disciplinary import registry: explicit interpretations, not a claim
-- that a philosophy or Indigenous knowledge source entails DASHI mathematics.
data Lens : Set where
  cyberneticViabilityLens marxCapitalLens zizekIdeologyLens
    irigarayRelationalLens kimmererReciprocityLens
    twoEyedPluralKnowledgeLens sevenGenerationPlanningLens
    communitySelfDeterminationLens : Lens

record InterpretiveReceipt : Set where
  constructor interpretiveReceipt
  field
    lens : Lens
    formalOwner : String
    sourceLocator : String
    boundary : String
    upgradesEmpiricalAdmission : Bool
    upgradesEmpiricalAdmissionIsFalse :
      upgradesEmpiricalAdmission ≡ false

open InterpretiveReceipt public

kimmererInterpretiveReceipt : InterpretiveReceipt
kimmererInterpretiveReceipt =
  interpretiveReceipt kimmererReciprocityLens
    "DASHI.Culture.KimmererTwoEyedSeeingInterpretationBoundaryExact"
    "Robin Wall Kimmerer, Braiding Sweetgrass (2013); source registry owner"
    "Interpretive motivation only; community authority and empirical outcomes require separate receipts."
    false refl

zizekInterpretiveReceipt : InterpretiveReceipt
zizekInterpretiveReceipt =
  interpretiveReceipt zizekIdeologyLens
    "DASHI.Reasoning.PNFZizekOperator"
    "DASHI.Reasoning.ZizekPNFSourceAtlas"
    "Parallax, contradiction and ideology remain typed interpretive readings, not empirical outcomes."
    false refl

intergenerationalInterpretiveReceipt : InterpretiveReceipt
intergenerationalInterpretiveReceipt =
  interpretiveReceipt sevenGenerationPlanningLens
    "DASHI.Core.IntergenerationalPlanningHorizonExact"
    "DASHI source-specific Indigenous knowledge and seven-generation owners"
    "Seven generations is a selected planning horizon, not universal Indigenous law or permission."
    false refl

-- Exact remaining computational/empirical cuts:
-- G1: typed stock-flow/physical conservation and cross-sector joins;
-- G2: measured time-series transitions and action-response calibration;
-- G3: genuine affected-community authority and consent receipts;
-- G4: multi-generation viability across regional/scenario traces;
-- G5: adversarial historical backtests and independent promotion evidence.
