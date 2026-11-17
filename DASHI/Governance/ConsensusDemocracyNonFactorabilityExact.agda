module DASHI.Governance.ConsensusDemocracyNonFactorabilityExact where

open import DASHI.Core.Prelude

import DASHI.Core.GenericReceipt as GenericReceipt
import DASHI.Core.IntersectionalNonFactorability as INF

------------------------------------------------------------------------
-- Consensus is one decision-procedure observation, not a complete democratic
-- profile.  The finite witness below is DASHI mathematics, not an empirical
-- classification of Occupy or any real institution.
------------------------------------------------------------------------

data ConsensusStatus : Set where
  consensusReached : ConsensusStatus

data GovernanceState : Set where
  consensusWithContestability : GovernanceState
  consensusWithoutContestability : GovernanceState

record DemocraticProfile : Set where
  constructor democraticProfileRecord
  field
    participationAvailable : Bool
    voiceAvailable : Bool
    vetoAvailable : Bool
    exitAvailable : Bool
    contestabilityAvailable : Bool
    transparencyAvailable : Bool
    nonDominationSatisfied : Bool

open DemocraticProfile public

contestableProfile : DemocraticProfile
contestableProfile =
  democraticProfileRecord
    true
    true
    true
    true
    true
    true
    true

uncontestableProfile : DemocraticProfile
uncontestableProfile =
  democraticProfileRecord
    true
    true
    true
    false
    false
    true
    false

consensusObserver : GovernanceState → ConsensusStatus
consensusObserver consensusWithContestability = consensusReached
consensusObserver consensusWithoutContestability = consensusReached

democraticProfile : GovernanceState → DemocraticProfile
democraticProfile consensusWithContestability = contestableProfile
democraticProfile consensusWithoutContestability = uncontestableProfile

sameConsensusObservation :
  consensusObserver consensusWithContestability
  ≡ consensusObserver consensusWithoutContestability
sameConsensusObservation = refl

democraticProfilesDiffer :
  democraticProfile consensusWithContestability
  ≡ democraticProfile consensusWithoutContestability
  → ⊥
democraticProfilesDiffer profilesEqual with cong exitAvailable profilesEqual
... | ()

canonicalConsensusDemocracyNonFactorability :
  INF.NonFactorabilityWitness consensusObserver democraticProfile
canonicalConsensusDemocracyNonFactorability =
  INF.nonFactorabilityWitness
    consensusWithContestability
    consensusWithoutContestability
    sameConsensusObservation
    democraticProfilesDiffer

consensusCannotDetermineDemocraticProfile :
  INF.FactorsThrough consensusObserver democraticProfile → ⊥
consensusCannotDetermineDemocraticProfile =
  INF.witnessRulesOutEveryFlatFactorisation
    canonicalConsensusDemocracyNonFactorability

record ConsensusDemocracyBoundary : Set where
  constructor consensusDemocracyBoundary
  field
    consensusAloneDeterminesDemocracy : Bool
    participationAloneDeterminesNonDomination : Bool
    exitContestabilityIndependentOfConsensus : Bool
    finiteWitnessClassifiesRealInstitutions : Bool
    consensusFailureProvesDemocracyImpossible : Bool

open ConsensusDemocracyBoundary public

canonicalConsensusDemocracyBoundary : ConsensusDemocracyBoundary
canonicalConsensusDemocracyBoundary =
  consensusDemocracyBoundary
    false
    false
    true
    false
    false

canonicalConsensusDemocracyNonFactorabilityReceipt :
  GenericReceipt.GenericReceipt
canonicalConsensusDemocracyNonFactorabilityReceipt =
  GenericReceipt.mkNonPromotingReceipt
    "consensus / democratic-profile non-factorability"
    "DASHI.Governance.ConsensusDemocracyNonFactorabilityExact"
    "canonicalConsensusDemocracyNonFactorability"
    "constructs two finite governance states with identical consensus observations but different exit/contestability/non-domination profiles, proving that no interpretation of consensus status alone can recover the selected democratic profile"
    "the witness is synthetic, does not classify Occupy or any real institution, and neither consensus failure nor consensus success determines democracy in the absence of additional dimensions"
    "agda -i . DASHI/Governance/ConsensusDemocracyNonFactorabilityRegression.agda"
