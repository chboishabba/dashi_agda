module DASHI.Cognition.PNF.SensibLawIndigenousAsymmetricJuridicalLegibilityExact where

------------------------------------------------------------------------
-- INDIGENOUS ASYMMETRIC JURIDICAL LEGIBILITY
--
-- Cross-period structural comparison, not historical identity:
--   * Mabo/Brennan source strand: foundational land-sovereignty machinery could
--     deny Indigenous law, sovereignty, occupancy and proprietorship constitutive
--     standing in Crown acquisition/title.
--   * Bringing Them Home source strand: later State/non-State infrastructure
--     operationally exercised/implemented coercive governance over Indigenous
--     children and families.
--
-- The combined asymmetry is a SensibLaw/DASHI structural synthesis. It is not
-- attributed as a phrase or theory to Brennan J, HREOC, churches or any one
-- historical actor.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

import DASHI.Cognition.PNF.SensibLawTerraNulliusFoundationalJuridicalPersonhoodExact as Terra
import DASHI.Governance.IndigenousRemovalDelegatedInfrastructureExact as Removal
import DASHI.Core.OperationalSystemBehaviourSemanticsExact as POSIWID
import DASHI.Core.IntersectionalNonFactorability as INF

------------------------------------------------------------------------
-- Relation-specific juridical legibility.
------------------------------------------------------------------------

data JuridicalRelation : Set where
  foundationalLandSovereigntyRelation
  coerciveGovernanceRelation
  familyRemovalAdministrationRelation
  welfareInstitutionRelation
  : JuridicalRelation

data JuridicalLegibility : Set where
  constitutiveAuthorityLegible
  governableSubjectLegible
  serviceRecipientLegible
  juridicallyErased
  : JuridicalLegibility

record AsymmetricJuridicalLegibility : Set where
  constructor asymmetric-juridical-legibility
  field
    landSovereigntyRelation : JuridicalRelation
    coerciveRelation : JuridicalRelation
    landConstitutiveLegibility : JuridicalLegibility
    landConstitutiveLegibilityExact : landConstitutiveLegibility ≡ juridicallyErased
    coerciveGovernabilityLegibility : JuridicalLegibility
    coerciveGovernabilityLegibilityExact :
      coerciveGovernabilityLegibility ≡ governableSubjectLegible
    sameHumanPopulationCanBeDifferentlyLegibleByRelation : Bool
    sameHumanPopulationCanBeDifferentlyLegibleByRelationIsTrue :
      sameHumanPopulationCanBeDifferentlyLegibleByRelation ≡ true
    structuralComparisonIsSameStatuteOrEvent : Bool
    structuralComparisonIsSameStatuteOrEventIsFalse :
      structuralComparisonIsSameStatuteOrEvent ≡ false
    synthesisReference : String

open AsymmetricJuridicalLegibility public

canonicalAsymmetricColonialLegibility : AsymmetricJuridicalLegibility
canonicalAsymmetricColonialLegibility = asymmetric-juridical-legibility
  foundationalLandSovereigntyRelation
  coerciveGovernanceRelation
  juridicallyErased refl
  governableSubjectLegible refl
  true refl
  false refl
  "SensibLaw cross-period structural synthesis: Indigenous peoples may be denied constitutive legal standing as law-bearing/sovereign/occupying/proprietary communities where such standing would block Crown acquisition, while remaining intensely legible to State systems as governable, removable, administrable or service-dependent subjects."

------------------------------------------------------------------------
-- Same-object source anchors remain separate.
------------------------------------------------------------------------

terraNulliusLandRelationErasesConstitutiveActor :
  Terra.personhoodState Terra.terraNulliusFoundationalJuridicalPersonhood
  ≡ Terra.juridicallyErasedActor
terraNulliusLandRelationErasesConstitutiveActor = refl

removalStateAuthorityPresent :
  Removal.stateRemovalAuthorityPresent Removal.bringingThemHomeInfrastructure ≡ true
removalStateAuthorityPresent = refl

removalNonStateParticipationPresent :
  Removal.nonStateServiceParticipationPresent Removal.bringingThemHomeInfrastructure ≡ true
removalNonStateParticipationPresent = refl

removalInfrastructureOperationallyEnabledSeparation :
  Removal.familySeparationOperationallyEnabled Removal.bringingThemHomeInfrastructure ≡ true
removalInfrastructureOperationallyEnabledSeparation = refl

nonStateProviderDidNotPossessWholeSovereignAuthority :
  Removal.nonStateProviderPossessesWholeStateAuthority Removal.bringingThemHomeInfrastructure ≡ false
nonStateProviderDidNotPossessWholeSovereignAuthority = refl

------------------------------------------------------------------------
-- Selective legibility is not a contradiction: the observer is relation-indexed.
------------------------------------------------------------------------

data RelationIndexedState : Set where
  samePeopleLandRelation samePeopleCoerciveRelation : RelationIndexedState

data CoarseHumanPresence : Set where
  humanPopulationPresent : CoarseHumanPresence

data RelationSpecificStanding : Set where
  sovereigntyConstitutiveStandingDenied coerciveGovernabilityImposed : RelationSpecificStanding

humanPresenceObserver : RelationIndexedState → CoarseHumanPresence
humanPresenceObserver _ = humanPopulationPresent

relationSpecificStanding : RelationIndexedState → RelationSpecificStanding
relationSpecificStanding samePeopleLandRelation = sovereigntyConstitutiveStandingDenied
relationSpecificStanding samePeopleCoerciveRelation = coerciveGovernabilityImposed

relationSpecificStandingDiffers :
  relationSpecificStanding samePeopleLandRelation
  ≡ relationSpecificStanding samePeopleCoerciveRelation → ⊥
relationSpecificStandingDiffers ()

humanPresenceAloneCannotRecoverJuridicalStanding :
  INF.FactorsThrough humanPresenceObserver relationSpecificStanding → ⊥
humanPresenceAloneCannotRecoverJuridicalStanding =
  INF.witnessRulesOutEveryFlatFactorisation
    (INF.nonFactorabilityWitness
      samePeopleLandRelation samePeopleCoerciveRelation refl relationSpecificStandingDiffers)

------------------------------------------------------------------------
-- POSIWID: realised allocation of powers/constraints is part of what the system
-- does, even when mission statements use benevolent vocabulary.
------------------------------------------------------------------------

posiwidBoundary : POSIWID.OperationalDescriptionBoundary
posiwidBoundary = POSIWID.canonicalOperationalDescriptionBoundary

realisedOperationMayBeClassified :
  POSIWID.observedOperationMayClassifyWhatSystemDoes posiwidBoundary ≡ true
realisedOperationMayBeClassified = refl

missionStatementDoesNotOverrideRealisedEffect :
  POSIWID.declaredPurposeOverridesRepeatedRealizedEffect posiwidBoundary ≡ false
missionStatementDoesNotOverrideRealisedEffect = refl

------------------------------------------------------------------------
-- Critical reading: asymmetric personhood/legibility.
------------------------------------------------------------------------

record AsymmetricPersonhoodCriticalBoundary : Set where
  constructor asymmetric-personhood-critical-boundary
  field
    coerciveLegibilityImpliesEqualSovereignStanding : Bool
    coerciveLegibilityImpliesEqualSovereignStandingIsFalse :
      coerciveLegibilityImpliesEqualSovereignStanding ≡ false
    legalGovernabilityImpliesLandConstitutiveStanding : Bool
    legalGovernabilityImpliesLandConstitutiveStandingIsFalse :
      legalGovernabilityImpliesLandConstitutiveStanding ≡ false
    landErasureImpliesNoLegalRegulationOfIndigenousPeopleAnywhere : Bool
    landErasureImpliesNoLegalRegulationOfIndigenousPeopleAnywhereIsFalse :
      landErasureImpliesNoLegalRegulationOfIndigenousPeopleAnywhere ≡ false
    relationSpecificAsymmetryCanBeClassifiedAsJuridicalDehumanisation : Bool
    relationSpecificAsymmetryCanBeClassifiedAsJuridicalDehumanisationIsTrue :
      relationSpecificAsymmetryCanBeClassifiedAsJuridicalDehumanisation ≡ true
    sourceAuthorsUsedOurAsymmetricPersonhoodPhrase : Bool
    sourceAuthorsUsedOurAsymmetricPersonhoodPhraseIsFalse :
      sourceAuthorsUsedOurAsymmetricPersonhoodPhrase ≡ false

open AsymmetricPersonhoodCriticalBoundary public

canonicalAsymmetricPersonhoodCriticalBoundary : AsymmetricPersonhoodCriticalBoundary
canonicalAsymmetricPersonhoodCriticalBoundary = asymmetric-personhood-critical-boundary
  false refl
  false refl
  false refl
  true refl
  false refl

------------------------------------------------------------------------
-- No-collapse laws.
------------------------------------------------------------------------

data CoerciveGovernabilityProvesEqualHumanStanding : Set where
data FoundationalErasureMeansNoColonialGovernanceOccurred : Set where
data CrossPeriodStructuralComparisonMeansSameHistoricalMechanism : Set where
data AsymmetricLegibilityWasExplicitPhraseOfPrimarySources : Set where

coerciveGovernabilityDoesNotProveEqualStanding :
  CoerciveGovernabilityProvesEqualHumanStanding → ⊥
coerciveGovernabilityDoesNotProveEqualStanding ()

foundationalErasureDoesNotMeanNoGovernance :
  FoundationalErasureMeansNoColonialGovernanceOccurred → ⊥
foundationalErasureDoesNotMeanNoGovernance ()

structuralComparisonDoesNotMakeEventsIdentical :
  CrossPeriodStructuralComparisonMeansSameHistoricalMechanism → ⊥
structuralComparisonDoesNotMakeEventsIdentical ()

ourPhraseDoesNotBackTransferToSources :
  AsymmetricLegibilityWasExplicitPhraseOfPrimarySources → ⊥
ourPhraseDoesNotBackTransferToSources ()
