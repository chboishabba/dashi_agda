module DASHI.Wikimedia.IbrahimEnglishSocialScienceFunnelBridgeExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)
open import Agda.Builtin.Bool using (Bool; true; false)
open import Data.Empty using (⊥)

import DASHI.Wikimedia.IbrahimEnglishParentCoverageGapAtlasExact as Gap

------------------------------------------------------------------------
-- IBRAHIM ENGLISH SOCIAL-SCIENCE FUNNEL BRIDGE
--
-- Navigation prior:
-- Mark Ibrahim; Christopher M. Danforth; Peter Sheridan Dodds,
-- "Connecting every bit of knowledge: The structure of Wikipedia's First
-- Link Network", Journal of Computational Science 19 (2017), 21-30.
-- DOI: 10.1016/j.jocs.2016.12.001
--
-- Current external identity coordinate inspected 2026-09-10:
--   social science = Wikidata Q34749.
--
-- The current English Social science page enumerates economics, psychology,
-- sociology, anthropology and political science among its constituent
-- disciplines.  We use that fact only as an external navigation/coverage
-- prior.  It does not identify those disciplines, create theorem dependency,
-- or make Wikipedia the DASHI semantic owner.
--
-- This file pays the shared-parent seam isolated by
-- IbrahimEnglishParentCoverageGapAtlasExact.  It does not add another
-- ontology and it does not duplicate the existing QID layer.
------------------------------------------------------------------------

data SocialScienceChild : Set where
  psychology : SocialScienceChild
  sociology : SocialScienceChild
  economics : SocialScienceChild
  anthropology : SocialScienceChild
  politicalScience : SocialScienceChild

record SocialScienceFunnelCoordinate : Set where
  constructor social-science-funnel-coordinate
  field
    title : String
    qid : String
    observationDate : String
    externalRole : String
open SocialScienceFunnelCoordinate public

socialScienceQ34749 : SocialScienceFunnelCoordinate
socialScienceQ34749 =
  social-science-funnel-coordinate
    "social science"
    "Q34749"
    "2026-09-10"
    "current EN/Wikidata shared navigation coordinate; not DASHI proof authority"

record SocialScienceChildBridge : Set where
  constructor social-science-child-bridge
  field
    child : SocialScienceChild
    childTitle : String
    childQid : String
    externalParent : SocialScienceFunnelCoordinate
    existingDashiSurface : String
    priorCoverageStatus : Gap.DashiParentCoverageStatus
    needsNewLeafTheory : Bool
    needsSharedParentBridge : Bool
    bridgeMeaning : String
open SocialScienceChildBridge public

psychologyBridge : SocialScienceChildBridge
psychologyBridge =
  social-science-child-bridge
    psychology
    "Psychology"
    "Q9418"
    socialScienceQ34749
    "DASHI/Culture/LopezRiosMarxistPsychologySourceAtlasExact.agda; DASHI/Culture/LopezRiosExistingPsychologyCrossPollinationExact.agda; DASHI/Cognition/PNF/*"
    Gap.strongLeafCoverageMissingParent
    false
    true
    "reuse existing psychology/cognition content; add only the shared social-science explanatory bridge"

sociologyBridge : SocialScienceChildBridge
sociologyBridge =
  social-science-child-bridge
    sociology
    "Sociology"
    "Q21201"
    socialScienceQ34749
    "DASHI/Cognition/PNF/CulturalMembershipBoundaryExact.agda; culture/governance/social-ecology and DOI-backed sociology surfaces"
    Gap.fragmentedIndirectCoverage
    false
    true
    "sociology is represented indirectly; the bridge exposes the missing canonical parent seam without erasing existing sociology content"

economicsBridge : SocialScienceChildBridge
economicsBridge =
  social-science-child-bridge
    economics
    "Economics"
    "Q8134"
    socialScienceQ34749
    "DASHI/Economics/Everything.agda; DASHI/Economics/*"
    Gap.strongLeafCoverageMissingParent
    false
    true
    "economics already has a formal domain; only its explicit shared social-science parent bridge is debt"

anthropologyBridge : SocialScienceChildBridge
anthropologyBridge =
  social-science-child-bridge
    anthropology
    "Anthropology"
    "Q23404"
    socialScienceQ34749
    "existing Mabo, culture, human, biology and social-ecology formulations provide candidate child-side material"
    Gap.parentBridgeMissing
    true
    true
    "do not mint a broad anthropology theory from Wikipedia; first quotient existing human/culture/Mabo material, then add only the surviving leaf and parent coordinates"

politicalScienceBridge : SocialScienceChildBridge
politicalScienceBridge =
  social-science-child-bridge
    politicalScience
    "Political science"
    "Q36442"
    socialScienceQ34749
    "existing Governance, SensibLaw, Mabo and political-economy formulations provide candidate child-side material"
    Gap.parentBridgeMissing
    true
    true
    "political-science coverage remains a real canonical-owner gap; the shared funnel identifies where it should connect but does not manufacture that owner"

------------------------------------------------------------------------
-- Introspective payoff.
--
-- One shared parent coordinate pays multiple navigation debts, but only two
-- child lanes still plausibly need genuinely new leaf consolidation after the
-- quotient against existing content: anthropology and political science.
------------------------------------------------------------------------

record SocialScienceFunnelPayoff : Set where
  constructor social-science-funnel-payoff
  field
    sharedParentQid : String
    psychologyLeafAlreadyPresent : Bool
    sociologyMaterialAlreadyPresent : Bool
    economicsLeafAlreadyPresent : Bool
    anthropologyNeedsLeafConsolidation : Bool
    politicalScienceNeedsLeafConsolidation : Bool
    sharedParentBridgePaysMultipleChildren : Bool
    wikipediaParentCreatesSemanticEquivalence : Bool
open SocialScienceFunnelPayoff public

firstSocialScienceFunnelPayoff : SocialScienceFunnelPayoff
firstSocialScienceFunnelPayoff =
  social-science-funnel-payoff
    "Q34749"
    true
    true
    true
    true
    true
    true
    false

------------------------------------------------------------------------
-- Bridge admission: an external funnel is useful only when it is welded back
-- to a DASHI-side formulation surface.  QID/title alone cannot close debt.
------------------------------------------------------------------------

record AdmittedSocialScienceBridge : Set where
  constructor admitted-social-science-bridge
  field
    candidate : SocialScienceChildBridge
    dashiFormulationSurfaceExists : Bool
    qidReusesCanonicalIdentityLayer : Bool
    sourceBoundaryRetained : Bool
    wikipediaObservationRevisionSensitive : Bool
open AdmittedSocialScienceBridge public

psychologyBridgeAdmission : AdmittedSocialScienceBridge
psychologyBridgeAdmission =
  admitted-social-science-bridge psychologyBridge true true true true

sociologyBridgeAdmission : AdmittedSocialScienceBridge
sociologyBridgeAdmission =
  admitted-social-science-bridge sociologyBridge true true true true

economicsBridgeAdmission : AdmittedSocialScienceBridge
economicsBridgeAdmission =
  admitted-social-science-bridge economicsBridge true true true true

-- These stay deliberately unadmitted as canonical child owners in this
-- tranche. Existing material is a candidate substrate, not yet a proof that
-- the Anthropology / Political science leaf owner itself has been paid.
anthropologyBridgeAdmission : AdmittedSocialScienceBridge
anthropologyBridgeAdmission =
  admitted-social-science-bridge anthropologyBridge false true true true

politicalScienceBridgeAdmission : AdmittedSocialScienceBridge
politicalScienceBridgeAdmission =
  admitted-social-science-bridge politicalScienceBridge false true true true

------------------------------------------------------------------------
-- Firewalls.
------------------------------------------------------------------------

data SharedExternalParentMakesChildrenEquivalent : Set where
data QidPaysMissingDashiOwner : Set where
data WikipediaEnumerationCreatesFormalCoverage : Set where
data SocialScienceBridgeErasesDisciplineSpecificSources : Set where

sharedParentDoesNotMakeChildrenEquivalent :
  SharedExternalParentMakesChildrenEquivalent → ⊥
sharedParentDoesNotMakeChildrenEquivalent ()

qidDoesNotPayMissingDashiOwner : QidPaysMissingDashiOwner → ⊥
qidDoesNotPayMissingDashiOwner ()

wikipediaEnumerationDoesNotCreateFormalCoverage :
  WikipediaEnumerationCreatesFormalCoverage → ⊥
wikipediaEnumerationDoesNotCreateFormalCoverage ()

sharedBridgeRetainsDisciplineSources :
  SocialScienceBridgeErasesDisciplineSpecificSources → ⊥
sharedBridgeRetainsDisciplineSpecificSources ()

record SocialScienceFunnelBoundary : Set where
  constructor social-science-funnel-boundary
  field
    externalIdentityReused : Bool
    currentEnglishObservationRevisionSensitive : Bool
    leafAndParentDebtSeparated : Bool
    existingDashiLeavesReused : Bool
    missingOwnersRemainExplicit : Bool
    sharedParentImpliesSemanticEquivalence : Bool
    wikipediaCreatesProofAuthority : Bool
open SocialScienceFunnelBoundary public

canonicalSocialScienceFunnelBoundary : SocialScienceFunnelBoundary
canonicalSocialScienceFunnelBoundary =
  social-science-funnel-boundary
    true true true true true false false
