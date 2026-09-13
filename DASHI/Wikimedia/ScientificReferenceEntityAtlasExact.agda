module DASHI.Wikimedia.ScientificReferenceEntityAtlasExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)
open import Data.String using (_++_)
open import Data.Empty using (⊥)

import DASHI.Wikimedia.IdentifierExact as Id

------------------------------------------------------------------------
-- SCIENTIFIC REFERENCE ENTITY ATLAS
--
-- QIDs are related-entity identity handles only. DOI/arXiv/official source
-- identifiers remain the bibliographic/source identity for publications and
-- theorem statements. External entity lookup creates no theorem, source,
-- truth, or promotion authority.
------------------------------------------------------------------------

data ReferenceEntityKind : Set where
  personEntity projectEntity conceptEntity institutionEntity publicationEntity : ReferenceEntityKind

data QidResolution : Set where
  verifiedQid : Id.ItemId → String → QidResolution
  unresolvedQid : String → QidResolution

record ScientificReferenceEntity : Set where
  constructor scientific-reference-entity
  field
    canonicalName : String
    entityKind : ReferenceEntityKind
    qidResolution : QidResolution
    identityReference : String
open ScientificReferenceEntity public

verified : String → ReferenceEntityKind → String → String → ScientificReferenceEntity
verified name kind qid verification =
  scientific-reference-entity name kind
    (verifiedQid (Id.itemId qid) verification)
    ("wikidata:" ++ qid)

unresolved : String → ReferenceEntityKind → String → ScientificReferenceEntity
unresolved name kind note =
  scientific-reference-entity name kind (unresolvedQid note)
    ("qid-unresolved:" ++ name)

-- YM authors / entities.
arthurJaffe edwardWitten ludvigFaddeev victorPopov paulFederbush : ScientificReferenceEntity
konradOsterwalder davidGross frankWilczek hughPolitzer erhardSeiler : ScientificReferenceEntity
tadeuszBalaban robertSchrader : ScientificReferenceEntity
arthurJaffe = verified "Arthur Jaffe" personEntity "Q370094" "Wikidata lookup 2026-09-08"
edwardWitten = verified "Edward Witten" personEntity "Q201513" "Wikidata lookup 2026-09-08"
ludvigFaddeev = verified "Ludvig Faddeev" personEntity "Q1030228" "Wikidata lookup 2026-09-08"
victorPopov = verified "Victor Popov" personEntity "Q462638" "Wikidata lookup 2026-09-08"
paulFederbush = verified "Paul G. Federbush" personEntity "Q102115681" "Wikidata lookup 2026-09-08"
konradOsterwalder = verified "Konrad Osterwalder" personEntity "Q125728" "Wikidata lookup 2026-09-08"
davidGross = verified "David Gross" personEntity "Q40262" "Wikidata lookup 2026-09-08"
frankWilczek = verified "Frank Wilczek" personEntity "Q107450" "Wikidata lookup 2026-09-08"
hughPolitzer = verified "Hugh David Politzer" personEntity "Q107407" "Wikidata lookup 2026-09-08"
erhardSeiler = verified "Erhard Seiler" personEntity "Q74323177" "Wikidata lookup 2026-09-08"
tadeuszBalaban = unresolved "Tadeusz Balaban" personEntity "no trustworthy Wikidata item resolved in 2026-09-08 audit"
robertSchrader = unresolved "Robert Schrader" personEntity "OS physicist identity not safely resolved in 2026-09-08 audit"

-- NS authors / entities.
ronaldCoifman yvesMeyer jeanLeray eberhardHopf tosioKato : ScientificReferenceEntity
andrewMajda luisCaffarelli louisNirenberg gangTian vladimirSverak : ScientificReferenceEntity
jamesBeale robertKohn zhenLei xiaoRen gregorySeregin luisEscauriaza : ScientificReferenceEntity
ronaldCoifman = verified "Ronald Coifman" personEntity "Q2165588" "Wikidata lookup 2026-09-08"
yvesMeyer = verified "Yves Meyer" personEntity "Q574597" "Wikidata lookup 2026-09-08"
jeanLeray = verified "Jean Leray" personEntity "Q441143" "Wikidata lookup 2026-09-08"
eberhardHopf = verified "Eberhard Hopf" personEntity "Q86070" "Wikidata lookup 2026-09-08"
tosioKato = verified "Tosio Kato" personEntity "Q1335673" "Wikidata lookup 2026-09-08"
andrewMajda = verified "Andrew Majda" personEntity "Q506133" "Wikidata lookup 2026-09-08"
luisCaffarelli = verified "Luis Caffarelli" personEntity "Q1076636" "Wikidata lookup 2026-09-08"
louisNirenberg = verified "Louis Nirenberg" personEntity "Q596590" "Wikidata lookup 2026-09-08"
gangTian = verified "Gang Tian" personEntity "Q942908" "Wikidata lookup 2026-09-08"
vladimirSverak = verified "Vladimir Sverak" personEntity "Q1593578" "Wikidata lookup 2026-09-08"
jamesBeale = unresolved "James Thomas Beale" personEntity "no trustworthy Wikidata item resolved in 2026-09-08 audit"
robertKohn = unresolved "Robert V. Kohn" personEntity "no trustworthy Wikidata item resolved in 2026-09-08 audit"
zhenLei = unresolved "Zhen Lei" personEntity "no trustworthy Wikidata item resolved in 2026-09-08 audit"
xiaoRen = unresolved "Xiao Ren" personEntity "no trustworthy Wikidata item resolved in 2026-09-08 audit"
gregorySeregin = unresolved "Gregory Seregin" personEntity "no trustworthy Wikidata item resolved in 2026-09-08 audit"
luisEscauriaza = unresolved "Luis Escauriaza" personEntity "no trustworthy Wikidata item resolved in 2026-09-08 audit"

-- RH authors / projects / concepts.
bernhardRiemann nicolaasDeBruijn charlesNewman timothyTrudgian polymathProject : ScientificReferenceEntity
davePlatt judeGomila : ScientificReferenceEntity
bernhardRiemann = verified "Bernhard Riemann" personEntity "Q42299" "Wikidata lookup 2026-09-08"
nicolaasDeBruijn = verified "Nicolaas Govert de Bruijn" personEntity "Q1078285" "Wikidata lookup 2026-09-08"
charlesNewman = verified "Charles M. Newman" personEntity "Q5080476" "Wikidata lookup 2026-09-08"
timothyTrudgian = verified "Timothy Trudgian" personEntity "Q132064015" "Wikidata lookup 2026-09-08"
polymathProject = verified "Polymath Project" projectEntity "Q2000812" "Wikidata lookup 2026-09-08"
davePlatt = unresolved "Dave Platt" personEntity "mathematician identity ambiguous; no safe Wikidata mapping"
judeGomila = unresolved "Jude Gomila" personEntity "candidate-audit author not safely resolved to Wikidata"

-- Shared concepts / publication identities.
navierStokesEquations riemannHypothesis millenniumPrizeProblems gaugeFixing : ScientificReferenceEntity
gangTianGaugeCalibratedGeometryI : ScientificReferenceEntity
navierStokesEquations = verified "Navier-Stokes equations" conceptEntity "Q201321" "Wikidata lookup 2026-09-08"
riemannHypothesis = verified "Riemann hypothesis" conceptEntity "Q205966" "Wikidata lookup 2026-09-08"
millenniumPrizeProblems = verified "Millennium Prize Problems" conceptEntity "Q727000" "Wikidata lookup 2026-09-08"
gaugeFixing = verified "gauge fixing" conceptEntity "Q832289" "Wikidata lookup 2026-09-08"
gangTianGaugeCalibratedGeometryI = verified "Gauge theory and calibrated geometry, I" publicationEntity "Q116272041" "Wikidata item matched to DOI 10.2307/121116, 2026-09-08"

------------------------------------------------------------------------
-- Firewalls.
------------------------------------------------------------------------

data QidIsPublicationIdentity : Set where
data QidIsTheoremAuthority : Set where
data QidIsSourceTruth : Set where
data NameEqualityResolvesUnresolvedQid : Set where
data AuthorQidIsPublicationQid : Set where

qidDoesNotReplacePublicationIdentifier : QidIsPublicationIdentity → ⊥
qidDoesNotReplacePublicationIdentifier ()
qidDoesNotCreateTheoremAuthority : QidIsTheoremAuthority → ⊥
qidDoesNotCreateTheoremAuthority ()
qidDoesNotCreateSourceTruth : QidIsSourceTruth → ⊥
qidDoesNotCreateSourceTruth ()
nameEqualityDoesNotResolveQid : NameEqualityResolvesUnresolvedQid → ⊥
nameEqualityDoesNotResolveQid ()
authorQidDoesNotBecomePublicationQid : AuthorQidIsPublicationQid → ⊥
authorQidDoesNotBecomePublicationQid ()

record ScientificReferenceEntityAtlasBoundary : Set where
  constructor scientific-reference-entity-atlas-boundary
  field
    qidIsExternalIdentityMetadata : Bool
    publicationIdentifierRemainsPrimary : Bool
    unresolvedMappingsRemainExplicit : Bool
    qidCreatesTheoremAuthority : Bool
    qidCreatesSourceTruth : Bool

canonicalScientificReferenceEntityAtlasBoundary : ScientificReferenceEntityAtlasBoundary
canonicalScientificReferenceEntityAtlasBoundary =
  scientific-reference-entity-atlas-boundary true true true false false
