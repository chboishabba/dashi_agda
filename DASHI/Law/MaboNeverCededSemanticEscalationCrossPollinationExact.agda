module DASHI.Law.MaboNeverCededSemanticEscalationCrossPollinationExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

import DASHI.Law.AustralianColonialSemanticConstitutionSourceReceiptsExact as Colonial
import DASHI.Law.SecuritySemanticEscalationDistanceExact as Escalation
import DASHI.Law.MaboCountrySecurityClassificationCrossPollinationExact as MaboCross

------------------------------------------------------------------------
-- Dynamic colonial semantic audit.
-- The key distinction is between (a) semantic downgrading as an operational
-- mechanism of colonial administration and (b) a claim about subjective intent.
------------------------------------------------------------------------

data AuthorityVisibility : Set where
  authorityExplicit
  authorityPartiallyVisible
  authorityAdministrativelySubordinated
  authorityErasedFromObserver : AuthorityVisibility

data ColonialAdministrativeLevel : Set where
  antecedentPoliticalOrder
  unrecognisedPoliticalOrder
  settledColonySubject
  protectedPopulation
  assimilablePopulation
  administrativeResidual : ColonialAdministrativeLevel

record ColonialSemanticState : Set where
  constructor colonialSemanticState
  field
    administrativeLevel : ColonialAdministrativeLevel
    authorityVisibility : AuthorityVisibility
    sovereigntyClaimVisible : Bool
    countryRelationVisible : Bool
    governingLawVisible : Bool
    stateReference : String

open ColonialSemanticState public

preColonialAuthorityState : ColonialSemanticState
preColonialAuthorityState = colonialSemanticState
  antecedentPoliticalOrder authorityExplicit true true true
  "analytical antecedent state: Country, law and political authority are represented rather than collapsed into the colonial observer"

settledColonyProjectionState : ColonialSemanticState
settledColonyProjectionState = colonialSemanticState
  settledColonySubject authorityErasedFromObserver false false false
  "colonial legal projection: settled-colony doctrine treated prior sovereignty/law as unrecognised for reception/occupation purposes"

protectionProjectionState : ColonialSemanticState
protectionProjectionState = colonialSemanticState
  protectedPopulation authorityAdministrativelySubordinated false true false
  "protection regime: identity and life were administratively classified/controlled under colonial statutes"

assimilationProjectionState : ColonialSemanticState
assimilationProjectionState = colonialSemanticState
  assimilablePopulation authorityAdministrativelySubordinated false false false
  "assimilation regime: colonial administrative categories governed absorption into the dominant society"

------------------------------------------------------------------------
-- Constitutive semantic mechanism versus subjective intent.
------------------------------------------------------------------------

data ColonialSemanticClaim : Set where
  semanticDowngradingOperationallyEnabledColonialAdministration
  semanticDowngradingWasConstitutiveOfSettledColonyLogic
  semanticDowngradingProvesEveryColonialActorSubjectivelyIntendedErasure
  sovereigntyNeverCededAsFirstNationsPoliticalPosition
  sovereigntyNeverCededAsHighCourtHolding
  modernSecurityClassificationRepeatsColonialMechanism : ColonialSemanticClaim

data ColonialSemanticProducer : Set where
  doctrineAndAdministrationCorpusProducer
  settledColonyLegalLogicProducer
  actorSpecificIntentProducer
  uluruPoliticalStatementProducer
  highCourtHoldingProducer
  modernSameMechanismLineageProducer : ColonialSemanticProducer

reverseColonialSemantic : ColonialSemanticClaim → ColonialSemanticProducer
reverseColonialSemantic semanticDowngradingOperationallyEnabledColonialAdministration = doctrineAndAdministrationCorpusProducer
reverseColonialSemantic semanticDowngradingWasConstitutiveOfSettledColonyLogic = settledColonyLegalLogicProducer
reverseColonialSemantic semanticDowngradingProvesEveryColonialActorSubjectivelyIntendedErasure = actorSpecificIntentProducer
reverseColonialSemantic sovereigntyNeverCededAsFirstNationsPoliticalPosition = uluruPoliticalStatementProducer
reverseColonialSemantic sovereigntyNeverCededAsHighCourtHolding = highCourtHoldingProducer
reverseColonialSemantic modernSecurityClassificationRepeatsColonialMechanism = modernSameMechanismLineageProducer

------------------------------------------------------------------------
-- Escalation/visibility joint trajectory.
------------------------------------------------------------------------

data JointTrajectoryPoint : Set where
  authorityVisibleLowThreat
  authorityPartialGroupThreat
  authorityErasedCollectiveThreat
  authorityErasedTerminalThreat : JointTrajectoryPoint

threatLevel : JointTrajectoryPoint → Escalation.EscalationLevel
threatLevel authorityVisibleLowThreat = Escalation.preservedLevel
threatLevel authorityPartialGroupThreat = Escalation.scopeBroadenedLevel
threatLevel authorityErasedCollectiveThreat = Escalation.collectiveEnemyLevel
threatLevel authorityErasedTerminalThreat = Escalation.terminalEnemyLevel

authorityAt : JointTrajectoryPoint → AuthorityVisibility
authorityAt authorityVisibleLowThreat = authorityExplicit
authorityAt authorityPartialGroupThreat = authorityPartiallyVisible
authorityAt authorityErasedCollectiveThreat = authorityErasedFromObserver
authorityAt authorityErasedTerminalThreat = authorityErasedFromObserver

record ColonialEscalationBoundary : Set where
  constructor colonialEscalationBoundary
  field
    semanticDowngradingWasIncidentalToSettledColonyAdministration : Bool
    semanticDowngradingWasIncidentalToSettledColonyAdministrationIsFalse : semanticDowngradingWasIncidentalToSettledColonyAdministration ≡ false
    constitutiveMechanismProvesUniversalSubjectiveIntent : Bool
    constitutiveMechanismProvesUniversalSubjectiveIntentIsFalse : constitutiveMechanismProvesUniversalSubjectiveIntent ≡ false
    neverCededPositionErasedByMunicipalNonJusticiability : Bool
    neverCededPositionErasedByMunicipalNonJusticiabilityIsFalse : neverCededPositionErasedByMunicipalNonJusticiability ≡ false
    modernSemanticEscalationAutomaticallyEqualsColonialism : Bool
    modernSemanticEscalationAutomaticallyEqualsColonialismIsFalse : modernSemanticEscalationAutomaticallyEqualsColonialism ≡ false
    maboRecognitionExhaustsAntecedentAuthority : Bool
    maboRecognitionExhaustsAntecedentAuthorityIsFalse : maboRecognitionExhaustsAntecedentAuthority ≡ false

canonicalColonialEscalationBoundary : ColonialEscalationBoundary
canonicalColonialEscalationBoundary =
  colonialEscalationBoundary false refl false refl false refl false refl false refl

------------------------------------------------------------------------
-- Pins to sourced donor propositions.
------------------------------------------------------------------------

neverCededSourceRole : Colonial.ColonialSourceRole
neverCededSourceRole = Colonial.firstNationsPoliticalStatement

semanticConstitutionSourceRole : Colonial.ColonialSourceRole
semanticConstitutionSourceRole = Colonial.dashiAnalyticalSynthesis

maboAuthorityResidualProducer : MaboCross.SecurityCountryProducer
maboAuthorityResidualProducer = MaboCross.countryAuthorityResidualProducer
