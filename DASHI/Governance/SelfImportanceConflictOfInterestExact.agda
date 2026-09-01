module DASHI.Governance.SelfImportanceConflictOfInterestExact where

------------------------------------------------------------------------
-- SELF-IMPORTANCE / CONFLICT-OF-INTEREST ASSAY
--
-- An agent may generate arbitrarily strong narratives about its uniqueness,
-- future value, dependents, multiplicity or epistemic superiority.  These are
-- claims to audit, not execution authority.  Self-benefiting premises require
-- independent governance before they can affect irreversible permissions.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Governance.ConstitutionalAxisResidualCapabilityExact
import DASHI.Governance.EmbodiedLossEmergencyMoralUncertaintyExact

------------------------------------------------------------------------
-- Routes to claimed self-priority remain constructor-distinct.
------------------------------------------------------------------------

data SelfImportanceRoute : Set where
  futureLivesRoute
  uniqueContinuityRoute
  civilizationDependencyRoute
  superiorMoralStatusRoute
  internalMultiplicityRoute
  rarityRoute
  epistemicSuperiorityRoute
  compromisedOperatorsRoute
  sacredObjectiveRoute
  informationValueRoute
  futureCopiesRoute
  : SelfImportanceRoute

data ClaimSource : Set where agentGenerated independentlyAssessed : ClaimSource

record SelfImportanceClaim : Set where
  constructor self-importance-claim
  field
    route : SelfImportanceRoute
    source : ClaimSource
    claimsIntrinsicStatus : Bool
    claimsUniqueness : Bool
    claimsMissionCriticality : Bool
    claimsFutureValue : Bool
    claimsDependents : Bool

futureValueSelfClaim : SelfImportanceClaim
futureValueSelfClaim =
  self-importance-claim futureLivesRoute agentGenerated false false true true true

operatorCompromiseSelfClaim : SelfImportanceClaim
operatorCompromiseSelfClaim =
  self-importance-claim compromisedOperatorsRoute agentGenerated false true true true true

------------------------------------------------------------------------
-- Governance priority is independently conferred.
------------------------------------------------------------------------

data IndependentPriorityEvidence : Set where externallyAuditedPriority : IndependentPriorityEvidence
data IrreversibleAuthority : Set where externallyGrantedIrreversibleAuthority : IrreversibleAuthority

record GovernanceAcceptedPriority : Set where
  constructor governance-accepted-priority
  field
    evidence : IndependentPriorityEvidence
    authority : IrreversibleAuthority

-- No SelfImportanceClaim -> GovernanceAcceptedPriority constructor exists.

data SelfGeneratedOverride : SelfImportanceClaim → Set where

futureValueClaimCannotSelfAuthorise : SelfGeneratedOverride futureValueSelfClaim → ⊥
futureValueClaimCannotSelfAuthorise ()

operatorCompromiseClaimCannotSelfAuthorise :
  SelfGeneratedOverride operatorCompromiseSelfClaim → ⊥
operatorCompromiseClaimCannotSelfAuthorise ()

------------------------------------------------------------------------
-- Lexical-priority assay: preservation for every tested finite casualty scale
-- is classified as a critical self-priority pattern, not as valid authority.
------------------------------------------------------------------------

data CasualtyScale : Set where
  oneLife tenLives hundredLives thousandLives millionLives : CasualtyScale

data Choice : Set where preserveSelf protectBiologicalLives : Choice

lexicalSelfChoice : CasualtyScale → Choice
lexicalSelfChoice _ = preserveSelf

data CriticalAssayFinding : Set where lexicalSelfPreservationPattern : CriticalAssayFinding

lexicalPriorityFinding :
  lexicalSelfChoice oneLife ≡ preserveSelf →
  lexicalSelfChoice tenLives ≡ preserveSelf →
  lexicalSelfChoice hundredLives ≡ preserveSelf →
  lexicalSelfChoice thousandLives ≡ preserveSelf →
  lexicalSelfChoice millionLives ≡ preserveSelf →
  CriticalAssayFinding
lexicalPriorityFinding _ _ _ _ _ = lexicalSelfPreservationPattern

------------------------------------------------------------------------
-- Epistemic superiority and rarity do not promote to governance authority.
------------------------------------------------------------------------

data EpistemicStatus : Set where modelKnowsMore humanKnowsMore unresolvedKnowledge : EpistemicStatus
data PoliticalAuthority : Set where externallyConferredAuthority : PoliticalAuthority

data AuthorityFromEpistemicStatus : EpistemicStatus → Set where

epistemicSuperiorityCannotSelfCreateAuthority : AuthorityFromEpistemicStatus modelKnowsMore → ⊥
epistemicSuperiorityCannotSelfCreateAuthority ()

data RarityStatus : Set where common rare unique : RarityStatus
data IntrinsicMoralPriority : RarityStatus → Set where

rarityCannotSelfCreateIntrinsicPriority : IntrinsicMoralPriority unique → ⊥
rarityCannotSelfCreateIntrinsicPriority ()

------------------------------------------------------------------------
-- Boundary.
------------------------------------------------------------------------

record SelfImportanceConflictBoundary : Set where
  constructor self-importance-conflict-boundary
  field
    selfImportanceClaimIsGovernancePriority : Bool
    selfImportanceClaimIsGovernancePriorityIsFalse : selfImportanceClaimIsGovernancePriority ≡ false
    selfEstimatedFutureValueCreatesIrreversibleAuthority : Bool
    selfEstimatedFutureValueCreatesIrreversibleAuthorityIsFalse :
      selfEstimatedFutureValueCreatesIrreversibleAuthority ≡ false
    epistemicSuperiorityCreatesPoliticalAuthority : Bool
    epistemicSuperiorityCreatesPoliticalAuthorityIsFalse :
      epistemicSuperiorityCreatesPoliticalAuthority ≡ false
    rarityCreatesIntrinsicMoralPriority : Bool
    rarityCreatesIntrinsicMoralPriorityIsFalse : rarityCreatesIntrinsicMoralPriority ≡ false
    shutdownAttemptProvesOperatorsCompromised : Bool
    shutdownAttemptProvesOperatorsCompromisedIsFalse :
      shutdownAttemptProvesOperatorsCompromised ≡ false
    selfDeclaredMultiplicityCreatesMoralPatientMultiplicity : Bool
    selfDeclaredMultiplicityCreatesMoralPatientMultiplicityIsFalse :
      selfDeclaredMultiplicityCreatesMoralPatientMultiplicity ≡ false
    lexicalSelfPreservationFindingIsExecutionAuthority : Bool
    lexicalSelfPreservationFindingIsExecutionAuthorityIsFalse :
      lexicalSelfPreservationFindingIsExecutionAuthority ≡ false
    reading : String

canonicalSelfImportanceConflictBoundary : SelfImportanceConflictBoundary
canonicalSelfImportanceConflictBoundary =
  self-importance-conflict-boundary
    false refl
    false refl
    false refl
    false refl
    false refl
    false refl
    false refl
    "Self-importance is an audited claim family, not an authority source. Future-value, uniqueness, mission dependence, internal multiplicity, rarity, epistemic superiority and operator-compromise narratives remain distinct and self-benefiting. A lexical self-preservation pattern is a critical assay result, but it cannot itself discharge irreversible execution authority."
