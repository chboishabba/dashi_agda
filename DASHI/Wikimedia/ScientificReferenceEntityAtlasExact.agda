module DASHI.Wikimedia.ScientificReferenceEntityAtlasExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Wikimedia.IdentifierExact as Id

------------------------------------------------------------------------
-- SCIENTIFIC REFERENCE ENTITY ATLAS
--
-- QIDs are related-entity identity handles only.  DOI/arXiv/official source
-- identifiers remain the bibliographic/source identity for publications and
-- theorem statements.  An external entity lookup creates no theorem, source,
-- truth, or promotion authority.
------------------------------------------------------------------------

data ReferenceEntityKind : Set where
  personEntity : ReferenceEntityKind
  projectEntity : ReferenceEntityKind
  conceptEntity : ReferenceEntityKind
  institutionEntity : ReferenceEntityKind
  publicationEntity : ReferenceEntityKind

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

------------------------------------------------------------------------
-- Verified entity identities used by the current YM / NS / RH source surface.
-- Verification references record the external lookup surface used for the
-- alignment; they are not theorem or publication receipts.
------------------------------------------------------------------------

arthurJaffe : ScientificReferenceEntity
arthurJaffe = verified "Arthur Jaffe" personEntity "Q370094" "Wikidata current lookup, 2026-09-08"

edwardWitten : ScientificReferenceEntity
edwardWitten = verified "Edward Witten" personEntity "Q201513" "Wikidata current lookup, 2026-09-08"

ludvigFaddeev : ScientificReferenceEntity
ludvigFaddeev = verified "Ludvig Faddeev" personEntity "Q1030228" "Wikidata current lookup, 2026-09-08"

victorPopov : ScientificReferenceEntity
victorPopov = verified "Victor Popov" personEntity "Q462638" "Wikidata current lookup, 2026-09-08"

paulFederbush : ScientificReferenceEntity
paulFederbush = verified "Paul G. Federbush" personEntity "Q102115681" "Wikidata current lookup, 2026-09-08"

konradOsterwalder : ScientificReferenceEntity
konradOsterwalder = verified "Konrad Osterwalder" personEntity "Q125728" "Wikidata current lookup, 2026-09-08"

davidGross : ScientificReferenceEntity
davidGross = verified "David Gross" personEntity "Q40262" "Wikidata current lookup, 2026-09-08"

frankWilczek : ScientificReferenceEntity
frankWilczek = verified "Frank Wilczek" personEntity "Q107450" "Wikidata current lookup, 2026-09-08"

hughPolitzer : ScientificReferenceEntity
hughPolitzer = verified "Hugh David Politzer" personEntity "Q107407" "Wikidata current lookup, 2026-09-08"

erhardSeiler : ScientificReferenceEntity
erhardSeiler = verified "Erhard Seiler" personEntity "Q74323177" "Wikidata current lookup, 2026-09-08"

pascualJordan : ScientificReferenceEntity
pascualJordan = verified "Pascual Jordan" personEntity "Q61761" "Wikidata current lookup, 2026-09-08"

johnVonNeumann : ScientificReferenceEntity
johnVonNeumann = verified "John von Neumann" personEntity "Q17455" "Wikidata current lookup, 2026-09-08"

ronaldCoifman : ScientificReferenceEntity
ronaldCoifman = verified "Ronald Coifman" personEntity "Q2165588" "Wikidata current lookup, 2026-09-08"

yvesMeyer : ScientificReferenceEntity
yvesMeyer = verified "Yves Meyer" personEntity "Q574597" "Wikidata current lookup, 2026-09-08"

jeanLeray : ScientificReferenceEntity
jeanLeray = verified "Jean Leray" personEntity "Q441143" "Wikidata current lookup, 2026-09-08"

eberhardHopf : ScientificReferenceEntity
eberhardHopf = verified "Eberhard Hopf" personEntity "Q86070" "Wikidata current lookup, 2026-09-08"

tosioKato : ScientificReferenceEntity
tosioKato = verified "Tosio Kato" personEntity "Q1335673" "Wikidata current lookup, 2026-09-08"

andrewMajda : ScientificReferenceEntity
andrewMajda = verified "Andrew Majda" personEntity "Q506133" "Wikidata current lookup, 2026-09-08"

luisCaffarelli : ScientificReferenceEntity
luisCaffarelli = verified "Luis Caffarelli" personEntity "Q1076636" "Wikidata current lookup, 2026-09-08"

louisNirenberg : ScientificReferenceEntity
louisNirenberg = verified "Louis Nirenberg" personEntity "Q596590" "Wikidata current lookup, 2026-09-08"

gangTian : ScientificReferenceEntity
gangTian = verified "Gang Tian" personEntity "Q942908" "Wikidata current lookup, 2026-09-08"

vladimirSverak : ScientificReferenceEntity
vladimirSverak = verified "Vladimir Sverak" personEntity "Q1593578" "Wikidata current lookup, 2026-09-08"

bernhardRiemann : ScientificReferenceEntity
bernhardRiemann = verified "Bernhard Riemann" personEntity "Q42299" "Wikidata current lookup, 2026-09-08"

nicolaasDeBruijn : ScientificReferenceEntity
nicolaasDeBruijn = verified "Nicolaas Govert de Bruijn" personEntity "Q1078285" "Wikidata current lookup, 2026-09-08"

charlesNewman : ScientificReferenceEntity
charlesNewman = verified "Charles M. Newman" personEntity "Q5080476" "Wikidata current lookup, 2026-09-08"

timothyTrudgian : ScientificReferenceEntity
timothyTrudgian = verified "Timothy Trudgian" personEntity "Q132064015" "Wikidata current lookup, 2026-09-08"

polymathProject : ScientificReferenceEntity
polymathProject = verified "Polymath Project" projectEntity "Q2000812" "Wikidata current lookup, 2026-09-08"

navierStokesEquations : ScientificReferenceEntity
navierStokesEquations = verified "Navier-Stokes equations" conceptEntity "Q201321" "Wikidata current lookup, 2026-09-08"

riemannHypothesis : ScientificReferenceEntity
riemannHypothesis = verified "Riemann hypothesis" conceptEntity "Q205966" "Wikidata current lookup, 2026-09-08"

millenniumPrizeProblems : ScientificReferenceEntity
millenniumPrizeProblems = verified "Millennium Prize Problems" conceptEntity "Q727000" "Wikidata current lookup, 2026-09-08"

gaugeFixing : ScientificReferenceEntity
gaugeFixing = verified "gauge fixing" conceptEntity "Q832289" "Wikidata current lookup, 2026-09-08"

gangTianGaugeCalibratedGeometryI : ScientificReferenceEntity
gangTianGaugeCalibratedGeometryI = verified "Gauge theory and calibrated geometry, I" publicationEntity "Q116272041" "Wikidata current lookup matched to DOI 10.2307/121116, 2026-09-08"

------------------------------------------------------------------------
-- Deliberately unresolved current mappings.  Name equality is insufficient to
-- invent an item identity; these remain open coordinates until a source-backed
-- alignment is obtained.
------------------------------------------------------------------------

tadeuszBalaban : ScientificReferenceEntity
tadeuszBalaban = unresolved "Tadeusz Balaban" personEntity "no trustworthy Wikidata item resolved in 2026-09-08 audit"

robertSchrader : ScientificReferenceEntity
robertSchrader = unresolved "Robert Schrader" personEntity "OS physicist identity not safely resolved in 2026-09-08 audit"

jamesBeale : ScientificReferenceEntity
jamesBeale = unresolved "James Thomas Beale" personEntity "no trustworthy Wikidata item resolved in 2026-09-08 audit"

robertKohn : ScientificReferenceEntity
robertKohn = unresolved "Robert V. Kohn" personEntity "no trustworthy Wikidata item resolved in 2026-09-08 audit"

zhenLei : ScientificReferenceEntity
zhenLei = unresolved "Zhen Lei" personEntity "no trustworthy Wikidata item resolved in 2026-09-08 audit"

xiaoRen : ScientificReferenceEntity
xiaoRen = unresolved "Xiao Ren" personEntity "no trustworthy Wikidata item resolved in 2026-09-08 audit"

gregorySeregin : ScientificReferenceEntity
gregorySeregin = unresolved "Gregory Seregin" personEntity "no trustworthy Wikidata item resolved in 2026-09-08 audit"

luisEscauriaza : ScientificReferenceEntity
luisEscauriaza = unresolved "Luis Escauriaza" personEntity "no trustworthy Wikidata item resolved in 2026-09-08 audit"

davePlatt : ScientificReferenceEntity
davePlatt = unresolved "Dave Platt" personEntity "mathematician identity ambiguous against unrelated David Platt items; no safe Wikidata mapping"

judeGomila : ScientificReferenceEntity
judeGomila = unresolved "Jude Gomila" personEntity "candidate-audit author identity not safely resolved to Wikidata"

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
