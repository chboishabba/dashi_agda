module DASHI.Wikimedia.IbrahimEnglishAnthropologyHumanityBridgeExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)
open import Agda.Builtin.Bool using (Bool; true; false)
open import Data.Empty using (⊥)

import DASHI.Wikimedia.IbrahimEnglishParentCoverageGapAtlasExact as Gap

------------------------------------------------------------------------
-- IBRAHIM ENGLISH ANTHROPOLOGY / HUMANITY BRIDGE
--
-- Navigation prior:
-- Mark Ibrahim; Christopher M. Danforth; Peter Sheridan Dodds,
-- "Connecting every bit of knowledge: The structure of Wikipedia's First
-- Link Network", Journal of Computational Science 19 (2017), 21-30.
-- DOI: 10.1016/j.jocs.2016.12.001
--
-- Current external coordinates inspected 2026-09-10:
--   anthropology = Wikidata Q23404
--   humanity     = Wikidata Q1156970
--
-- Current EN describes anthropology as the scientific study of humanity,
-- spanning human behaviour, human biology, cultures, societies and
-- linguistics, in present and past contexts. Wikidata Q23404 likewise records
-- anthropology as an academic discipline, subclass/part of social science,
-- and "is the study of" humanity.
--
-- These observations are revision-sensitive navigation/identity evidence.
-- They do NOT define DASHI anthropology and do not turn adjacent Mabo,
-- biology, culture, cognition, Indigenous-knowledge or law material into an
-- anthropology theorem by proximity.
------------------------------------------------------------------------

record AnthropologyHumanityCoordinate : Set where
  constructor anthropology-humanity-coordinate
  field
    anthropologyTitle : String
    anthropologyQid : String
    parentTitle : String
    parentQid : String
    observationDate : String
    externalReading : String
open AnthropologyHumanityCoordinate public

anthropologyToHumanityCoordinate : AnthropologyHumanityCoordinate
anthropologyToHumanityCoordinate =
  anthropology-humanity-coordinate
    "Anthropology"
    "Q23404"
    "humanity"
    "Q1156970"
    "2026-09-10"
    "current EN/Wikidata navigation coordinate; not formal authority"

------------------------------------------------------------------------
-- Quotient existing DASHI substrate before declaring new theory debt.
------------------------------------------------------------------------

data AnthropologySurface : Set where
  biologicalHuman : AnthropologySurface
  culturalSocial : AnthropologySurface
  indigenousRelational : AnthropologySurface
  juridicalColonial : AnthropologySurface
  linguistic : AnthropologySurface
  archaeologicalHistorical : AnthropologySurface
  ethnographicMethod : AnthropologySurface

record AnthropologySurfaceAudit : Set where
  constructor anthropology-surface-audit
  field
    surface : AnthropologySurface
    repositoryEvidence : String
    reusableSubstrateObserved : Bool
    canonicalAnthropologyOwnerPaid : Bool
    sourceLanePaid : Bool
    residual : String
open AnthropologySurfaceAudit public

biologicalHumanAudit : AnthropologySurfaceAudit
biologicalHumanAudit =
  anthropology-surface-audit
    biologicalHuman
    "DASHI/Biology/* plus human/person/agent carriers; specialised Mabo dehumanisation owner also contains an explicit biological-anthropology coordinate"
    true false false
    "biology/humanity substrate exists, but biological anthropology as a discipline/source lane is not thereby paid"

culturalSocialAudit : AnthropologySurfaceAudit
culturalSocialAudit =
  anthropology-surface-audit
    culturalSocial
    "DASHI/Culture/*; DASHI/Cognition/PNF/CulturalMembershipBoundaryExact.agda; sociology/social-ecology and culture cross-pollinations"
    true false false
    "substantial culture/social substrate exists; anthropology-specific synthesis and attribution remain open"

indigenousRelationalAudit : AnthropologySurfaceAudit
indigenousRelationalAudit =
  anthropology-surface-audit
    indigenousRelational
    "DASHI/Culture/IndigenousKnowledgeStoryTwoEyedSeeingBidiExact.agda; DASHI/Culture/KimmererTwoEyedSeeingInterpretationBoundaryExact.agda; Country/Two-Eyed/Mabo owners"
    true false true
    "source-bounded Indigenous-knowledge material is reusable only with its own provenance and cannot be relabelled as generic anthropology"

juridicalColonialAudit : AnthropologySurfaceAudit
juridicalColonialAudit =
  anthropology-surface-audit
    juridicalColonial
    "Mabo/terra-nullius/juridical-humanity owners across DASHI/Cognition/PNF and SensibLaw"
    true false true
    "colonial/juridical human classification is well represented but is one anthropology-adjacent problem, not a canonical discipline owner"

linguisticAudit : AnthropologySurfaceAudit
linguisticAudit =
  anthropology-surface-audit
    linguistic
    "focused canonical search found no linguistic-anthropology owner"
    false false false
    "genuine leaf gap: linguistic anthropology plus its empirical/source boundary"

archaeologicalHistoricalAudit : AnthropologySurfaceAudit
archaeologicalHistoricalAudit =
  anthropology-surface-audit
    archaeologicalHistorical
    "repository uses 'archaeology' heavily as proof-search terminology, but focused search did not establish archaeology-the-discipline as an anthropology owner"
    false false false
    "genuine leaf gap unless a discipline-specific archaeology/human-past owner is found outside the focused search"

ethnographicMethodAudit : AnthropologySurfaceAudit
ethnographicMethodAudit =
  anthropology-surface-audit
    ethnographicMethod
    "no canonical ethnography/participant-observation anthropology method owner established by the focused audit"
    false false false
    "genuine methodological gap: observation/fieldwork provenance cannot be inferred from general observer machinery"

------------------------------------------------------------------------
-- Introspective reduction.
--
-- The apparent top-level Anthropology hole does collapse substantially: human
-- biology, culture, Indigenous relational material, colonial/juridical
-- classification and social cognition already provide reusable fibres.
--
-- But three anthropology-specific seams survive the quotient:
--   1. canonical discipline synthesis/owner,
--   2. ethnographic/fieldwork methodology and provenance,
--   3. underrepresented linguistic and archaeological/historical leaves.
------------------------------------------------------------------------

record AnthropologyQuotientResult : Set where
  constructor anthropology-quotient-result
  field
    humanityParentCoordinatePaid : Bool
    humanBiologySubstratePresent : Bool
    cultureSocietySubstratePresent : Bool
    indigenousRelationalSubstratePresent : Bool
    colonialJuridicalSubstratePresent : Bool
    canonicalAnthropologyOwnerPaid : Bool
    ethnographicMethodPaid : Bool
    linguisticAnthropologyPaid : Bool
    archaeologicalAnthropologyPaid : Bool
    anthropologyNeedsEntirelyNewTheory : Bool
open AnthropologyQuotientResult public

currentAnthropologyQuotient : AnthropologyQuotientResult
currentAnthropologyQuotient =
  anthropology-quotient-result
    true true true true true false false false false false

record AnthropologyResidualFrontier : Set where
  constructor anthropology-residual-frontier
  field
    canonicalOwnerResidual : String
    methodResidual : String
    linguisticResidual : String
    archaeologyResidual : String
    existingSubstrateMustRetainSourceIdentity : Bool
    wikipediaCanCloseResiduals : Bool
open AnthropologyResidualFrontier public

currentAnthropologyResidualFrontier : AnthropologyResidualFrontier
currentAnthropologyResidualFrontier =
  anthropology-residual-frontier
    "canonical Anthropology owner that relates biological, sociocultural, linguistic and human-past fibres without collapsing them"
    "ethnographic/participant-observation/fieldwork receipt with observer, community, time, method, consent/authority and source provenance kept explicit"
    "linguistic anthropology owner/source lane"
    "archaeological/historical anthropology owner or explicit external handoff"
    true
    false

------------------------------------------------------------------------
-- Firewalls.
------------------------------------------------------------------------

data HumanityIdentityCreatesAnthropologyTheory : Set where
data MaboCreatesGeneralAnthropology : Set where
data IndigenousKnowledgeBecomesAnthropologyWithoutSourceBoundary : Set where
data ObserverMachineryCreatesEthnographicReceipt : Set where
data BiologyCreatesBiologicalAnthropology : Set where

humanityIdentityDoesNotCreateAnthropologyTheory :
  HumanityIdentityCreatesAnthropologyTheory → ⊥
humanityIdentityDoesNotCreateAnthropologyTheory ()

maboDoesNotCreateGeneralAnthropology : MaboCreatesGeneralAnthropology → ⊥
maboDoesNotCreateGeneralAnthropology ()

indigenousKnowledgeRetainsSourceBoundary :
  IndigenousKnowledgeBecomesAnthropologyWithoutSourceBoundary → ⊥
indigenousKnowledgeRetainsSourceBoundary ()

observerMachineryIsNotEthnographicReceipt :
  ObserverMachineryCreatesEthnographicReceipt → ⊥
observerMachineryIsNotEthnographicReceipt ()

biologyDoesNotCreateBiologicalAnthropology :
  BiologyCreatesBiologicalAnthropology → ⊥
biologyDoesNotCreateBiologicalAnthropology ()

record AnthropologyHumanityBoundary : Set where
  constructor anthropology-humanity-boundary
  field
    qidIdentityReused : Bool
    currentEnglishObservationRevisionSensitive : Bool
    adjacentDashiSubstrateReused : Bool
    disciplineSpecificResidualsRemainExplicit : Bool
    indigenousKnowledgeSourceBoundaryRetained : Bool
    wikipediaCreatesAnthropologyAuthority : Bool
open AnthropologyHumanityBoundary public

canonicalAnthropologyHumanityBoundary : AnthropologyHumanityBoundary
canonicalAnthropologyHumanityBoundary =
  anthropology-humanity-boundary true true true true true false
