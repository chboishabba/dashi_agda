module DASHI.Wikimedia.IbrahimSnowballStateAnthropologyArchaeologyExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Core.AttributedSourceCore as Attribution
import DASHI.Core.IntersectionalNonFactorability as INF
import DASHI.Wikimedia.SnowballExternalIdentityAvailabilityExact as Identity
import DASHI.Wikimedia.IbrahimEnglishAnthropologyHumanityBridgeExact as Anthropology
import DASHI.Wikimedia.IbrahimEnglishArchaeologyGeologyPetrochemGapExact as ArchaeologyGap
import DASHI.Wikimedia.IbrahimEnglishCommunityStateScienceParentBridgeExact as Parent

------------------------------------------------------------------------
-- IBRAHIM SNOWBALL WALK: STATE / ANTHROPOLOGY / ARCHAEOLOGY
--
-- Navigation prior:
-- Mark Ibrahim; Christopher M. Danforth; Peter Sheridan Dodds,
-- "Connecting every bit of knowledge: The structure of Wikipedia's First Link
-- Network", Journal of Computational Science 19 (2017), 21-30.
-- DOI 10.1016/j.jocs.2016.12.001.
--
-- Current EN observations inspected 2026-09-10 are revision-sensitive:
--   State       -> political entity (raw lead-link/navigation candidate)
--   Anthropology describes itself as scientific study of humanity
--   Archaeology -> human activity via recovery/analysis of material culture
--
-- QIDs are supplemental identity coordinates. They do not pay parentage,
-- authority, theorem truth, historical interpretation, or community standing.
------------------------------------------------------------------------

ibrahimSource : Attribution.AttributedSource
ibrahimSource = Attribution.mkDOISource
  "Mark Ibrahim; Christopher M. Danforth; Peter Sheridan Dodds"
  "Connecting every bit of knowledge: The structure of Wikipedia's First Link Network"
  "Journal of Computational Science 19, 21-30"
  "2017"
  "10.1016/j.jocs.2016.12.001"
  "https://doi.org/10.1016/j.jocs.2016.12.001"
  Attribution.academicArticleSource
  "navigation prior over revision-indexed Wikipedia first-link flow; not DASHI semantic authority"
  Attribution.publicAttribution

------------------------------------------------------------------------
-- External identity demands: requested when applicable, non-promoting.
------------------------------------------------------------------------

stateQidDemand : Identity.ExternalIdentityDemand
stateQidDemand = Identity.mkOptionalIdentityDemand
  "Ibrahim snowball graph walk" "state identity" "State"
  Identity.wikidataQid
  (Identity.verified "Q7275" "Wikidata identity checked 2026-09-10")

stateRawParentQidDemand : Identity.ExternalIdentityDemand
stateRawParentQidDemand = Identity.mkOptionalIdentityDemand
  "Ibrahim snowball graph walk" "raw first-link target identity" "political entity"
  Identity.wikidataQid
  (Identity.unresolved "do not silently substitute political territorial entity Q1048835")

anthropologyQidDemand : Identity.ExternalIdentityDemand
anthropologyQidDemand = Identity.mkOptionalIdentityDemand
  "Ibrahim snowball graph walk" "anthropology identity" "Anthropology"
  Identity.wikidataQid
  (Identity.verified "Q23404" "Wikidata identity checked 2026-09-10")

humanityQidDemand : Identity.ExternalIdentityDemand
humanityQidDemand = Identity.mkOptionalIdentityDemand
  "Ibrahim snowball graph walk" "selected conceptual parent identity" "humanity"
  Identity.wikidataQid
  (Identity.verified "Q1156970" "existing canonical Wikimedia coordinate")

archaeologyQidDemand : Identity.ExternalIdentityDemand
archaeologyQidDemand = Identity.mkOptionalIdentityDemand
  "Ibrahim snowball graph walk" "archaeology identity" "Archaeology"
  Identity.wikidataQid
  (Identity.verified "Q23498" "Wikidata identity checked 2026-09-10")

humanActivityQidDemand : Identity.ExternalIdentityDemand
humanActivityQidDemand = Identity.mkOptionalIdentityDemand
  "Ibrahim snowball graph walk" "raw archaeology lead concept" "human activity"
  Identity.wikidataQid
  (Identity.verified "Q24902509" "existing canonical Wikimedia coordinate")

------------------------------------------------------------------------
-- State regression: recognition/administrative surface cannot determine the
-- source of Country/community authority.
------------------------------------------------------------------------

data StateSituatedCase : Set where
  sameStateSurfacePreExistingCountryAuthority : StateSituatedCase
  sameStateSurfaceStateConferredAuthority : StateSituatedCase

data StateSurface : Set where
  sameRecognisedStateSurface : StateSurface

data CountryAuthorityReading : Set where
  authorityPreExistsStateRecognition : CountryAuthorityReading
  authorityConstitutedByState : CountryAuthorityReading

projectStateSurface : StateSituatedCase → StateSurface
projectStateSurface _ = sameRecognisedStateSurface

countryAuthorityReading : StateSituatedCase → CountryAuthorityReading
countryAuthorityReading sameStateSurfacePreExistingCountryAuthority = authorityPreExistsStateRecognition
countryAuthorityReading sameStateSurfaceStateConferredAuthority = authorityConstitutedByState

stateSurfaceCountryAuthorityDefect :
  INF.NonFactorabilityWitness projectStateSurface countryAuthorityReading
stateSurfaceCountryAuthorityDefect = INF.nonFactorabilityWitness
  sameStateSurfacePreExistingCountryAuthority
  sameStateSurfaceStateConferredAuthority
  refl
  (λ ())

stateSurfaceCannotFactorCountryAuthority :
  INF.FactorsThrough projectStateSurface countryAuthorityReading → ⊥
stateSurfaceCannotFactorCountryAuthority =
  INF.witnessRulesOutEveryFlatFactorisation stateSurfaceCountryAuthorityDefect

------------------------------------------------------------------------
-- Anthropology regression: the same broad "study of humanity" surface does
-- not determine whose knowledge, method, consent, authority or provenance is
-- being carried.  Two-Eyed/situated inspection must preserve that residual.
------------------------------------------------------------------------

data AnthropologySituatedCase : Set where
  humanityStudyExternalObserverOnly : AnthropologySituatedCase
  humanityStudyCommunityAuthorised : AnthropologySituatedCase

data HumanityStudySurface : Set where
  sameHumanityStudySurface : HumanityStudySurface

data AnthropologyAuthorityReading : Set where
  externalObservationWithoutCommunityAuthority : AnthropologyAuthorityReading
  communityAuthorisedKnowledgeRelation : AnthropologyAuthorityReading

projectHumanityStudy : AnthropologySituatedCase → HumanityStudySurface
projectHumanityStudy _ = sameHumanityStudySurface

anthropologyAuthorityReading : AnthropologySituatedCase → AnthropologyAuthorityReading
anthropologyAuthorityReading humanityStudyExternalObserverOnly =
  externalObservationWithoutCommunityAuthority
anthropologyAuthorityReading humanityStudyCommunityAuthorised =
  communityAuthorisedKnowledgeRelation

humanityParentAuthorityDefect :
  INF.NonFactorabilityWitness projectHumanityStudy anthropologyAuthorityReading
humanityParentAuthorityDefect = INF.nonFactorabilityWitness
  humanityStudyExternalObserverOnly humanityStudyCommunityAuthorised refl (λ ())

humanityParentCannotFactorAnthropologyAuthority :
  INF.FactorsThrough projectHumanityStudy anthropologyAuthorityReading → ⊥
humanityParentCannotFactorAnthropologyAuthority =
  INF.witnessRulesOutEveryFlatFactorisation humanityParentAuthorityDefect

------------------------------------------------------------------------
-- Archaeology regression: object/material label cannot recover archaeological
-- context.  Context, locus, recovery history, dating method, custody and
-- community/legal authority may snowball only when the consumer needs them.
------------------------------------------------------------------------

data ArchaeologicalSituatedCase : Set where
  sameObjectInDocumentedContext : ArchaeologicalSituatedCase
  sameObjectDisplacedFromContext : ArchaeologicalSituatedCase

data MaterialObjectSurface : Set where
  sameMaterialObjectClass : MaterialObjectSurface

data ArchaeologicalContextReading : Set where
  contextProvenanceRetained : ArchaeologicalContextReading
  contextProvenanceLost : ArchaeologicalContextReading

projectMaterialObject : ArchaeologicalSituatedCase → MaterialObjectSurface
projectMaterialObject _ = sameMaterialObjectClass

archaeologicalContextReading : ArchaeologicalSituatedCase → ArchaeologicalContextReading
archaeologicalContextReading sameObjectInDocumentedContext = contextProvenanceRetained
archaeologicalContextReading sameObjectDisplacedFromContext = contextProvenanceLost

materialObjectContextDefect :
  INF.NonFactorabilityWitness projectMaterialObject archaeologicalContextReading
materialObjectContextDefect = INF.nonFactorabilityWitness
  sameObjectInDocumentedContext sameObjectDisplacedFromContext refl (λ ())

materialObjectCannotFactorArchaeologicalContext :
  INF.FactorsThrough projectMaterialObject archaeologicalContextReading → ⊥
materialObjectCannotFactorArchaeologicalContext =
  INF.witnessRulesOutEveryFlatFactorisation materialObjectContextDefect

------------------------------------------------------------------------
-- Snowball frontier.  Named axes are current discoveries, not the invariant.
------------------------------------------------------------------------

record StateAnthropologyArchaeologySnowballBoundary : Set where
  constructor state-anthropology-archaeology-snowball-boundary
  field
    ibrahimSourceAttributed : Bool
    wikidataRequestedWhenApplicable : Bool
    unresolvedQidsAllowed : Bool
    rawFirstLinkSeparatedFromConceptualParent : Bool
    stateSurfaceFactorsCountryAuthority : Bool
    humanitySurfaceFactorsAnthropologyAuthority : Bool
    materialObjectFactorsArchaeologicalContext : Bool
    twoEyedSourceAuthorityResidualRetained : Bool
    archaeologyGapStillReal : Bool
    currentAxisVocabularyClaimedComplete : Bool
    wikipediaCreatesDomainAuthority : Bool
open StateAnthropologyArchaeologySnowballBoundary public

canonicalStateAnthropologyArchaeologySnowballBoundary :
  StateAnthropologyArchaeologySnowballBoundary
canonicalStateAnthropologyArchaeologySnowballBoundary =
  state-anthropology-archaeology-snowball-boundary
    true true true true false false false true
    (ArchaeologyGap.CrossDomainGapReading.archaeologyIsRealGap
      ArchaeologyGap.currentCrossDomainGapReading)
    false false

anthropologyPriorBoundary : Anthropology.AnthropologyHumanityBoundary
anthropologyPriorBoundary = Anthropology.canonicalAnthropologyHumanityBoundary

statePriorBoundary : Parent.StateBridgeRequirements
statePriorBoundary = Parent.stateRequirements
