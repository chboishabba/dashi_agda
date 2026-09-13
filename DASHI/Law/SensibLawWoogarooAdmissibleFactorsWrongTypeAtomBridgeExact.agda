module DASHI.Law.SensibLawWoogarooAdmissibleFactorsWrongTypeAtomBridgeExact where

open import DASHI.Core.Prelude

import DASHI.Core.IntersectionalNonFactorability as INF
import DASHI.Core.QueryIndexedProjectionAdequacyExact as Query
import DASHI.Core.AdmissibleConsumerMDLHyperfabricExact as MDL
import DASHI.Cognition.PNF.SensibLawWrongTypeLegalElementAlgebraExact as Wrong
import DASHI.Law.SensibLawWoogarooBartyRepresentativeFirstOutreachExact as Representative
import DASHI.Law.SensibLawWoogarooBartyPreservationCrossPollinationExact as Barty
import DASHI.Law.SensibLawWoogarooPreservationRoadmapExact as Roadmap

------------------------------------------------------------------------
-- WOOGAROO: ADMISSIBLE / FACTORSTHROUGH / WRONGTYPE / ATOM BRIDGE
--
-- This owner does not create a parallel admissibility or factorisation calculus.
-- It reuses the canonical DASHI surfaces and applies them to four distinct
-- Woogaroo consumers:
--
--   * representative triage / private Barty outreach;
--   * public attribution / endorsement;
--   * EPBC 2019/8575 statutory decision;
--   * Queensland NCA critical-habitat application.
--
-- A source-paid atom may be admissible context for one consumer while being
-- inadequate, non-factorising, or simply the WrongType for another consumer.
------------------------------------------------------------------------

data WoogarooConsumer : Set where
  managementTriageConsumer : WoogarooConsumer
  publicAttributionConsumer : WoogarooConsumer
  epbc8575DecisionConsumer : WoogarooConsumer
  qldNCA13CriticalHabitatConsumer : WoogarooConsumer
  custodialAuthorityConsumer : WoogarooConsumer

data WoogarooAtom : Set where
  localPlaceNexusAtom : WoogarooAtom
  activeFederalDecisionWindowAtom : WoogarooAtom
  threatenedSpeciesPresenceAtom : WoogarooAtom
  exactParcelHabitatFunctionAtom : WoogarooAtom
  authorisedRepresentativeTriageAtom : WoogarooAtom
  explicitPublicAttributionConsentAtom : WoogarooAtom
  authorisedEPBCDelegateAtom : WoogarooAtom
  localCustodialAuthorityAtom : WoogarooAtom

------------------------------------------------------------------------
-- Application-declared atom admission.  These constructors do not mean the
-- atom is sufficient for the consumer; they only record that it is admissible
-- input of the declared kind.
------------------------------------------------------------------------

data AtomAdmissibleFor : WoogarooAtom → WoogarooConsumer → Set where
  localNexusAdmissibleForTriage :
    AtomAdmissibleFor localPlaceNexusAtom managementTriageConsumer
  activeWindowAdmissibleForTriage :
    AtomAdmissibleFor activeFederalDecisionWindowAtom managementTriageConsumer
  representativeTriageAdmissibleForTriage :
    AtomAdmissibleFor authorisedRepresentativeTriageAtom managementTriageConsumer
  explicitConsentAdmissibleForAttribution :
    AtomAdmissibleFor explicitPublicAttributionConsentAtom publicAttributionConsumer
  threatenedSpeciesAdmissibleForEPBC :
    AtomAdmissibleFor threatenedSpeciesPresenceAtom epbc8575DecisionConsumer
  exactParcelFunctionAdmissibleForEPBC :
    AtomAdmissibleFor exactParcelHabitatFunctionAtom epbc8575DecisionConsumer
  exactParcelFunctionAdmissibleForNCA13 :
    AtomAdmissibleFor exactParcelHabitatFunctionAtom qldNCA13CriticalHabitatConsumer
  delegateAdmissibleForEPBC :
    AtomAdmissibleFor authorisedEPBCDelegateAtom epbc8575DecisionConsumer
  custodialAuthorityAdmissibleForCustodialConsumer :
    AtomAdmissibleFor localCustodialAuthorityAtom custodialAuthorityConsumer

------------------------------------------------------------------------
-- Canonical MDL reuse: admissibility and consumer adequacy remain separate.
-- The full internal legal dossier can be source-admissible but still be an
-- inadequate first-contact object because the representative-first consumer
-- requires a short, triageable, non-pressuring brief.
------------------------------------------------------------------------

data TriageModel : Set where
  localNexusOnly : TriageModel
  representativeFirstBrief : TriageModel
  fullInternalLegalDossier : TriageModel

data TriageAdmissible : TriageModel → Set where
  nexusAdmissible : TriageAdmissible localNexusOnly
  representativeBriefAdmissible : TriageAdmissible representativeFirstBrief
  internalDossierAdmissible : TriageAdmissible fullInternalLegalDossier

data TriageAdequate : TriageModel → Set where
  representativeBriefAdequate : TriageAdequate representativeFirstBrief

data TriageRefines : TriageModel → TriageModel → Set where
  nexusToBrief : TriageRefines localNexusOnly representativeFirstBrief
  briefToDossier : TriageRefines representativeFirstBrief fullInternalLegalDossier
  sameNexus : TriageRefines localNexusOnly localNexusOnly
  sameBrief : TriageRefines representativeFirstBrief representativeFirstBrief
  sameDossier : TriageRefines fullInternalLegalDossier fullInternalLegalDossier

triageDescriptionLength : TriageModel → Nat
triageDescriptionLength localNexusOnly = 1
triageDescriptionLength representativeFirstBrief = 2
triageDescriptionLength fullInternalLegalDossier = 10

triageModelReference : TriageModel → String
triageModelReference localNexusOnly = "local nexus only"
triageModelReference representativeFirstBrief = "representative-first factual brief"
triageModelReference fullInternalLegalDossier = "full internal Woogaroo legal/political/proof dossier"

bartyTriageProblem : MDL.ConsumerMDLProblem
bartyTriageProblem = MDL.consumerMDLProblem
  TriageModel
  TriageAdmissible
  TriageAdequate
  triageDescriptionLength
  TriageRefines
  triageModelReference
  "small ordinal length used only as a fixture; no truth/authority claim"
  "NC Management representative-first triage consumer"

representativeFirstBriefIsEligible : MDL.Eligible bartyTriageProblem representativeFirstBrief
representativeFirstBriefIsEligible = representativeBriefAdmissible , representativeBriefAdequate

fullInternalDossierIsAdmissibleButNotTriageAdequate :
  TriageAdequate fullInternalLegalDossier → ⊥
fullInternalDossierIsAdmissibleButNotTriageAdequate ()

localNexusAloneIsNotTriageAdequate : TriageAdequate localNexusOnly → ⊥
localNexusAloneIsNotTriageAdequate ()

------------------------------------------------------------------------
-- FactorsThrough witness 1: the same local nexus cannot determine public
-- attribution permission.  Consent is a finer coordinate than local connection.
------------------------------------------------------------------------

data BartySituatedState : Set where
  sameLocalNexusWithoutAttributionConsent : BartySituatedState
  sameLocalNexusWithAttributionConsent : BartySituatedState

data LocalNexusProjection : Set where
  sameLocalNexusProjection : LocalNexusProjection

data AttributionAnswer : Set where
  attributionNotPermitted : AttributionAnswer
  attributionPermitted : AttributionAnswer

projectLocalNexus : BartySituatedState → LocalNexusProjection
projectLocalNexus sameLocalNexusWithoutAttributionConsent = sameLocalNexusProjection
projectLocalNexus sameLocalNexusWithAttributionConsent = sameLocalNexusProjection

publicAttributionAnswer : BartySituatedState → AttributionAnswer
publicAttributionAnswer sameLocalNexusWithoutAttributionConsent = attributionNotPermitted
publicAttributionAnswer sameLocalNexusWithAttributionConsent = attributionPermitted

localNexusAttributionDefect :
  INF.NonFactorabilityWitness projectLocalNexus publicAttributionAnswer
localNexusAttributionDefect = INF.nonFactorabilityWitness
  sameLocalNexusWithoutAttributionConsent
  sameLocalNexusWithAttributionConsent
  refl
  (λ ())

localNexusCannotFactorToPublicAttribution :
  INF.FactorsThrough projectLocalNexus publicAttributionAnswer → ⊥
localNexusCannotFactorToPublicAttribution =
  INF.witnessRulesOutEveryFlatFactorisation localNexusAttributionDefect

------------------------------------------------------------------------
-- FactorsThrough witness 2: threatened-species presence alone cannot determine
-- the Queensland s 13 critical-habitat answer.  The missing coordinate is the
-- habitat function/essentiality relation to viable-population conservation.
------------------------------------------------------------------------

data HabitatSituatedState : Set where
  threatenedSpeciesPresentNonEssentialHabitat : HabitatSituatedState
  threatenedSpeciesPresentEssentialHabitat : HabitatSituatedState

data SpeciesPresenceProjection : Set where
  threatenedSpeciesPresent : SpeciesPresenceProjection

data NCA13Answer : Set where
  nca13NotPaidByThisState : NCA13Answer
  nca13EssentialityCoordinatePaid : NCA13Answer

projectThreatenedSpeciesPresence : HabitatSituatedState → SpeciesPresenceProjection
projectThreatenedSpeciesPresence threatenedSpeciesPresentNonEssentialHabitat = threatenedSpeciesPresent
projectThreatenedSpeciesPresence threatenedSpeciesPresentEssentialHabitat = threatenedSpeciesPresent

nca13Answer : HabitatSituatedState → NCA13Answer
nca13Answer threatenedSpeciesPresentNonEssentialHabitat = nca13NotPaidByThisState
nca13Answer threatenedSpeciesPresentEssentialHabitat = nca13EssentialityCoordinatePaid

speciesPresenceNCA13Defect :
  INF.NonFactorabilityWitness projectThreatenedSpeciesPresence nca13Answer
speciesPresenceNCA13Defect = INF.nonFactorabilityWitness
  threatenedSpeciesPresentNonEssentialHabitat
  threatenedSpeciesPresentEssentialHabitat
  refl
  (λ ())

speciesPresenceCannotFactorToNCA13 :
  INF.FactorsThrough projectThreatenedSpeciesPresence nca13Answer → ⊥
speciesPresenceCannotFactorToNCA13 =
  INF.witnessRulesOutEveryFlatFactorisation speciesPresenceNCA13Defect

------------------------------------------------------------------------
-- Query-indexed adequacy: a projection can be adequate for a bounded outreach
-- question while inadequate for endorsement or a statutory decision.  This is
-- exactly the repository's query-indexed projection discipline.
------------------------------------------------------------------------

data OutreachQuery : Set where
  whyContactIsLocallyRelevant : OutreachQuery
  mayCampaignPubliclyAttributeSupport : OutreachQuery

data OutreachQueryAnswer : Set where
  locallyRelevant : OutreachQueryAnswer
  noPublicAttribution : OutreachQueryAnswer
  yesPublicAttribution : OutreachQueryAnswer

outreachQueryAnswer : OutreachQuery → BartySituatedState → OutreachQueryAnswer
outreachQueryAnswer whyContactIsLocallyRelevant state = locallyRelevant
outreachQueryAnswer mayCampaignPubliclyAttributeSupport sameLocalNexusWithoutAttributionConsent = noPublicAttribution
outreachQueryAnswer mayCampaignPubliclyAttributeSupport sameLocalNexusWithAttributionConsent = yesPublicAttribution

outreachQuerySemantics : Query.QuerySemantics BartySituatedState OutreachQuery OutreachQueryAnswer
outreachQuerySemantics = Query.querySemantics outreachQueryAnswer

localNexusAdequateForLocalRelevance :
  Query.AdequateFor projectLocalNexus outreachQuerySemantics whyContactIsLocallyRelevant
localNexusAdequateForLocalRelevance =
  Query.factorsForQuery (λ _ → locallyRelevant) (λ _ → refl)

localNexusDefectiveForPublicAttribution :
  Query.QueryAdequacyDefect projectLocalNexus outreachQuerySemantics mayCampaignPubliclyAttributeSupport
localNexusDefectiveForPublicAttribution = Query.queryAdequacyDefect
  sameLocalNexusWithoutAttributionConsent
  sameLocalNexusWithAttributionConsent
  refl
  (λ ())

------------------------------------------------------------------------
-- WrongType / Atom firewalls.
--
-- A source-paid atomic proposition is not promoted into a legal-element proof,
-- public consent, custodial authority, or statutory classification merely by
-- being relevant or admissible somewhere else.
------------------------------------------------------------------------

data LocalNexusAtomEqualsConsentAtom : Set where
data ThreatenedSpeciesAtomEqualsCriticalHabitatAtom : Set where
data DelegateIdentityAtomEqualsApprovalOutcomeAtom : Set where
data IndigenousIdentityAtomEqualsCustodialAuthorityAtom : Set where
data AdmissibleAtomEqualsConsumerAdequateBundle : Set where

localNexusAtomDoesNotBecomeConsentAtom : LocalNexusAtomEqualsConsentAtom → ⊥
localNexusAtomDoesNotBecomeConsentAtom ()

threatenedSpeciesAtomDoesNotBecomeCriticalHabitatAtom :
  ThreatenedSpeciesAtomEqualsCriticalHabitatAtom → ⊥
threatenedSpeciesAtomDoesNotBecomeCriticalHabitatAtom ()

delegateIdentityAtomDoesNotBecomeApprovalOutcome :
  DelegateIdentityAtomEqualsApprovalOutcomeAtom → ⊥
delegateIdentityAtomDoesNotBecomeApprovalOutcome ()

indigenousIdentityAtomDoesNotBecomeCustodialAuthority :
  IndigenousIdentityAtomEqualsCustodialAuthorityAtom → ⊥
indigenousIdentityAtomDoesNotBecomeCustodialAuthority ()

admissibleAtomDoesNotBecomeAdequateBundle :
  AdmissibleAtomEqualsConsumerAdequateBundle → ⊥
admissibleAtomDoesNotBecomeAdequateBundle ()

legalElementStringStillDoesNotProveElement :
  Wrong.ElementStringReferenceIsElementProof → ⊥
legalElementStringStillDoesNotProveElement = Wrong.stringReferenceDoesNotProveElement

wrongTypeIdStillDoesNotGenerateElements :
  Wrong.WrongTypeIdAloneDeterminesAllElements → ⊥
wrongTypeIdStillDoesNotGenerateElements = Wrong.wrongTypeIdDoesNotGenerateElements

------------------------------------------------------------------------
-- Current consumer routing.
------------------------------------------------------------------------

record WoogarooConsumerRoutingBoundary : Set where
  constructor woogaroo-consumer-routing-boundary
  field
    representativeFirstRequest : Representative.RepresentativeFirstRequest
    preservationAwareBrief : Barty.PreservationAwareOutreachBrief
    federalRoadmap : Roadmap.RoadmapCoordinate
    localNexusAdequateForTriageContext : Bool
    localNexusAdequateForPublicAttribution : Bool
    speciesPresenceAdequateForNCA13ByItself : Bool
    admissibilitySeparatedFromAdequacy : Bool
    factorisationIndexedByConsumer : Bool
    wrongTypeAtomsKeptDistinct : Bool

canonicalWoogarooConsumerRoutingBoundary : WoogarooConsumerRoutingBoundary
canonicalWoogarooConsumerRoutingBoundary = woogaroo-consumer-routing-boundary
  Representative.currentRepresentativeFirstRequest
  Barty.currentPreservationAwareBartyBrief
  Roadmap.federal8575
  true
  false
  false
  true
  true
  true
