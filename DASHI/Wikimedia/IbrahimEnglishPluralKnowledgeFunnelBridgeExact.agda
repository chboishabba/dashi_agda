module DASHI.Wikimedia.IbrahimEnglishPluralKnowledgeFunnelBridgeExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)
open import Agda.Builtin.Bool using (Bool; true; false)
open import Data.Empty using (⊥)

import DASHI.Wikimedia.ScientificReferenceEntityAtlasExact as Entity

------------------------------------------------------------------------
-- IBRAHIM ENGLISH PLURAL-KNOWLEDGE / CRITICAL-THEORY FUNNEL BRIDGE
--
-- Navigation prior:
-- Mark Ibrahim; Christopher M. Danforth; Peter Sheridan Dodds,
-- "Connecting every bit of knowledge: The structure of Wikipedia's First
-- Link Network", Journal of Computational Science 19 (2017), 21-30.
-- DOI: 10.1016/j.jocs.2016.12.001
--
-- This tranche corrects an important introspective defect: the literal first
-- qualifying English-Wikipedia link is navigation evidence, not necessarily
-- an ontology parent. Current examples inspected 2026-09-10 include:
--   Feminism            -> political movements
--   Intersectionality   -> analytical framework
--   Traditional knowledge -> regional
-- These edges are useful for traversal, but DASHI parent selection must retain
-- source, community, place, authority and conceptual-role information.
------------------------------------------------------------------------

record RawFirstLinkObservation : Set where
  constructor raw-first-link-observation
  field
    pageTitle : String
    pageQid : String
    rawFirstLinkTitle : String
    observationDate : String
    interpretation : String
open RawFirstLinkObservation public

feminismRaw : RawFirstLinkObservation
feminismRaw = raw-first-link-observation
  "Feminism" "Q7252" "political movements" "2026-09-10"
  "raw Ibrahim-style EN traversal edge; not a claim that feminism is exhausted by political movements"

intersectionalityRaw : RawFirstLinkObservation
intersectionalityRaw = raw-first-link-observation
  "Intersectionality" "Q1516555" "analytical framework" "2026-09-10"
  "raw EN traversal edge; framework identity does not replace Crenshaw/source or non-factorability content"

traditionalKnowledgeRaw : RawFirstLinkObservation
traditionalKnowledgeRaw = raw-first-link-observation
  "Traditional knowledge / indigenous knowledge" "Q1428168" "regional" "2026-09-10"
  "literal first-link traversal is intentionally not promoted to conceptual parent; community/place/custodianship are retained downstream"

------------------------------------------------------------------------
-- Existing DASHI substrate: quotient first, add no parallel ontology.
------------------------------------------------------------------------

data PluralKnowledgeLane : Set where
  indigenousKnowledge : PluralKnowledgeLane
  twoEyedSeeing : PluralKnowledgeLane
  braidingSweetgrass : PluralKnowledgeLane
  intersectionality : PluralKnowledgeLane
  feminism : PluralKnowledgeLane
  hegelDialectic : PluralKnowledgeLane
  zizekDialectic : PluralKnowledgeLane
  lacanianPsychoanalysis : PluralKnowledgeLane
  antiLacanianFeministGrammar : PluralKnowledgeLane

record ExistingLaneAudit : Set where
  constructor existing-lane-audit
  field
    lane : PluralKnowledgeLane
    repositorySurface : String
    substantiveCoverageObserved : Bool
    parentBridgeStillUseful : Bool
    bridgeTarget : String
open ExistingLaneAudit public

indigenousAudit : ExistingLaneAudit
indigenousAudit = existing-lane-audit indigenousKnowledge
  "DASHI/Culture/IndigenousKnowledgeStoryTwoEyedSeeingBidiExact.agda; DASHI/IndigenousKnowledgeTwoEyedValidation.agda; Country/Mabo/Environment integrations"
  true true
  "Knowledge + Community + Place/Country; do not collapse Indigenous knowledge into generic science"

twoEyedAudit : ExistingLaneAudit
twoEyedAudit = existing-lane-audit twoEyedSeeing
  "DASHI/Culture/KimmererTwoEyedSeeingInterpretationBoundaryExact.agda plus SensibLaw/Environment/Country consumers"
  true true
  "plural epistemic comparison/coordination bridge with authority and provenance retained"

sweetgrassAudit : ExistingLaneAudit
sweetgrassAudit = existing-lane-audit braidingSweetgrass
  "DASHI/Culture/KimmererBraidingAcknowledgement.agda; CulturalProvenanceBoundaryCore; braided governance/biology consumers"
  true true
  "Community + ecology + reciprocal obligation + knowledge provenance; acknowledgement is not generic theory ownership"

intersectionalAudit : ExistingLaneAudit
intersectionalAudit = existing-lane-audit intersectionality
  "DASHI/Core/IntersectionalNonFactorability.agda and widespread law/planning/education/Indigenous consumers"
  true true
  "Social Science + Society + Law; retain non-factorability rather than reducing to a list of identities"

feminismAudit : ExistingLaneAudit
feminismAudit = existing-lane-audit feminism
  "Haraway SituatedFormalisationBoundaryExact; PlumwoodMasterModelOperationFamilyExact; ButlerPerformativeGenesisNonDescentExact; TrinhSubjectInMakingNoncollapseExact; Scott DifferenceWithoutHierarchyExact; Irigaray critical-relational sources"
  true true
  "Philosophy + political/social movement + gender/power; no single feminist school promoted as canonical feminism"

hegelAudit : ExistingLaneAudit
hegelAudit = existing-lane-audit hegelDialectic
  "DASHI/Culture/HegelDialecticPrimarySourceBoundaryExact.agda; DialecticPluralismRepresentationSourceAtlasExact; DASHI/Core/DialecticalMaterialRevisionExact.agda"
  true true
  "Philosophy + dialectic; primary-source Hegel remains separate from DASHI generic revision machinery"

zizekAudit : ExistingLaneAudit
zizekAudit = existing-lane-audit zizekDialectic
  "DASHI/Reasoning/PNFZizekOperator.agda; LacanZizekIdeologyBridge.agda; StageZeroToTwelveKantLacanZizekBridge.agda"
  true true
  "Philosophy/ideology/psychoanalysis; Žižek attribution remains source-bounded"

lacanAudit : ExistingLaneAudit
lacanAudit = existing-lane-audit lacanianPsychoanalysis
  "DASHI/Reasoning/LacanSignifierSubjectCore.agda; LacanDiscourseMatheme.agda; LacanFantasyDriveCore.agda; LacanRegisterSinthomeHyperfabric.agda"
  true true
  "Psychoanalysis + Philosophy/Psychology; formal carrier is not empirical clinical authority"

antiLacanianFeministAudit : ExistingLaneAudit
antiLacanianFeministAudit = existing-lane-audit antiLacanianFeministGrammar
  "DASHI/Core/LacanIrigarayTernaryGrammarBridgeExact.agda; CriticalRelationalGrammarSourceRegistryExact.agda; DifferenceWithoutHierarchyExact.agda"
  true true
  "Feminism + Philosophy + psychoanalytic critique; shared carrier does not imply shared grammar"

------------------------------------------------------------------------
-- QID bindings reuse the existing external-identity carrier.
------------------------------------------------------------------------

hegelQid zizekQid lacanQid irigarayQid feminismQid intersectionalityQid traditionalKnowledgeQid : Entity.ScientificReferenceEntity
hegelQid = Entity.verified "Georg Wilhelm Friedrich Hegel" Entity.personEntity "Q9235" "Wikidata lookup 2026-09-10"
zizekQid = Entity.verified "Slavoj Zizek" Entity.personEntity "Q184750" "Wikidata lookup 2026-09-10"
lacanQid = Entity.verified "Jacques Lacan" Entity.personEntity "Q169906" "Wikidata lookup 2026-09-10"
irigarayQid = Entity.verified "Luce Irigaray" Entity.personEntity "Q28918" "Wikidata lookup 2026-09-10"
feminismQid = Entity.verified "feminism" Entity.conceptEntity "Q7252" "Wikidata lookup 2026-09-10"
intersectionalityQid = Entity.verified "intersectionality" Entity.conceptEntity "Q1516555" "Wikidata lookup 2026-09-10"
traditionalKnowledgeQid = Entity.verified "traditional knowledge / indigenous knowledge" Entity.conceptEntity "Q1428168" "Wikidata lookup 2026-09-10"

------------------------------------------------------------------------
-- Funnel repair: selected conceptual bridges differ from raw first links.
------------------------------------------------------------------------

record SelectedPluralBridge : Set where
  constructor selected-plural-bridge
  field
    child : PluralKnowledgeLane
    selectedParents : String
    existingDashiAnchor : String
    sourceBoundaryRetained : Bool
    communityAuthorityRetained : Bool
    rawFirstLinkPromotedToOntologyParent : Bool
open SelectedPluralBridge public

indigenousSelected : SelectedPluralBridge
indigenousSelected = selected-plural-bridge indigenousKnowledge
  "Knowledge; Community; Place/Country"
  "Two-Eyed/Kimmerer/IndigenousKnowledge/Country source-bounded owners"
  true true false

intersectionalitySelected : SelectedPluralBridge
intersectionalitySelected = selected-plural-bridge intersectionality
  "Social science; society; law; power"
  "IntersectionalNonFactorability and query-indexed non-factorability consumers"
  true true false

feminismSelected : SelectedPluralBridge
feminismSelected = selected-plural-bridge feminism
  "Philosophy; political/social movement; equality/power"
  "Haraway/Plumwood/Butler/Trinh/Scott/Irigaray source-bounded owners"
  true true false

dialecticSelected : SelectedPluralBridge
dialecticSelected = selected-plural-bridge hegelDialectic
  "Philosophy; logic/history depending source role"
  "Hegel primary-source boundary + DASHI dialectical-material revision separation"
  true true false

antiLacanianSelected : SelectedPluralBridge
antiLacanianSelected = selected-plural-bridge antiLacanianFeministGrammar
  "Feminism; philosophy; psychoanalytic critique"
  "Lacan/Irigaray shared-carrier different-grammar bridge"
  true true false

------------------------------------------------------------------------
-- Coverage conclusion.
------------------------------------------------------------------------

record PluralKnowledgeCoverageReading : Set where
  constructor plural-knowledge-coverage-reading
  field
    indigenousKnowledgeMissing : Bool
    feminismMissing : Bool
    intersectionalityMissing : Bool
    dialecticsMissing : Bool
    lacanZizekMissing : Bool
    antiLacanianFeministConstructionMissing : Bool
    canonicalCrossFunnelBridgesRemainUseful : Bool
    rawFirstLinkEqualsOntologyParent : Bool
open PluralKnowledgeCoverageReading public

currentPluralKnowledgeCoverage : PluralKnowledgeCoverageReading
currentPluralKnowledgeCoverage =
  plural-knowledge-coverage-reading
    false false false false false false true false

------------------------------------------------------------------------
-- Firewalls.
------------------------------------------------------------------------

data IndigenousKnowledgeIsGenericScience : Set where
data BraidingAcknowledgementCreatesUniversalIndigenousTheory : Set where
data IntersectionalityIsIdentityChecklist : Set where
data HegelEqualsDashiDialectic : Set where
data LacanEqualsIrigarayGrammar : Set where
data FeminismHasOneCanonicalSchool : Set where
data WikipediaFirstLinkCreatesOntologyParent : Set where

indigenousKnowledgeDoesNotCollapseToGenericScience : IndigenousKnowledgeIsGenericScience → ⊥
indigenousKnowledgeDoesNotCollapseToGenericScience ()
braidingAcknowledgementDoesNotCreateUniversalTheory : BraidingAcknowledgementCreatesUniversalIndigenousTheory → ⊥
braidingAcknowledgementDoesNotCreateUniversalTheory ()
intersectionalityDoesNotCollapseToChecklist : IntersectionalityIsIdentityChecklist → ⊥
intersectionalityDoesNotCollapseToChecklist ()
hegelDoesNotBecomeDashiGenericDialectic : HegelEqualsDashiDialectic → ⊥
hegelDoesNotBecomeDashiGenericDialectic ()
lacanAndIrigarayGrammarsRemainDistinct : LacanEqualsIrigarayGrammar → ⊥
lacanAndIrigarayGrammarsRemainDistinct ()
feminismDoesNotHaveSingleCanonicalSchool : FeminismHasOneCanonicalSchool → ⊥
feminismDoesNotHaveSingleCanonicalSchool ()
rawFirstLinkDoesNotCreateOntologyParent : WikipediaFirstLinkCreatesOntologyParent → ⊥
rawFirstLinkDoesNotCreateOntologyParent ()

record PluralKnowledgeFunnelBoundary : Set where
  constructor plural-knowledge-funnel-boundary
  field
    ibrahimNavigationPriorRetained : Bool
    rawAndConceptualParentSeparated : Bool
    existingDashiOwnersReused : Bool
    qidLayerReused : Bool
    indigenousAuthorityRetained : Bool
    feministPluralityRetained : Bool
    philosopherAttributionRetained : Bool
    wikipediaCreatesFormalAuthority : Bool

canonicalPluralKnowledgeFunnelBoundary : PluralKnowledgeFunnelBoundary
canonicalPluralKnowledgeFunnelBoundary =
  plural-knowledge-funnel-boundary true true true true true true true false
