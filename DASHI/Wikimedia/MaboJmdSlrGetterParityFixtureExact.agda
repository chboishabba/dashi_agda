module DASHI.Wikimedia.MaboJmdSlrGetterParityFixtureExact where

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Wikimedia.JmdLeanGoldenAbiAttachmentExact as Jmd
import DASHI.Wikimedia.JmdLeanIntegratedMachineLineageExact as Machine
import DASHI.Wikimedia.MaboPropertyTripleProjectionExact as MaboTriple
import DASHI.Wikimedia.MaboReviewedContextFederationExact as MaboReview
import DASHI.Wikimedia.NativePropertyTripleProjectionExact as Property
open import DASHI.Wikimedia.LeanSlrWorldObservationBidiExact

------------------------------------------------------------------------
-- GOLDEN MABO GETTER-PARITY FIXTURE
------------------------------------------------------------------------

maboGoldenObservation : WorldObservation
maboGoldenObservation =
  mkWorldObservation
    "mabo:getter-parity:Q1501525:P710"
    "Q1501525"
    "P710"
    "wikidata"
    "wikidata:Q1501525:oldid:2333409615"
    "digest:runtime-must-supply-exact-content-digest"
    "Q975866"
    retrievalSucceeded
    unknownFreshness
    providerRevisionProvenance

maboLeanGetterFixture : LeanGetterObservation
maboLeanGetterFixture =
  mkLeanGetterObservation
    maboGoldenObservation
    "dashi_lean4@349f9b7dd49a7f23bfbd7d9da60416afa5440ccf:RequestProject.Cli.Fetch.fetchEntity"

maboSlrGetterFixture : SlrGetterObservation
maboSlrGetterFixture =
  mkSlrGetterObservation
    maboGoldenObservation
    "chboishabba/slr:Wikidata production getter adapter"

leanAndSlrFixtureNormalizeToSameObservation :
  normalizeLeanGetter maboLeanGetterFixture ≡
  normalizeSlrGetter maboSlrGetterFixture
leanAndSlrFixtureNormalizeToSameObservation = refl

maboJmdGetterAbiFixture : Jmd.JmdGetterAbiReceipt
maboJmdGetterAbiFixture =
  Jmd.mkJmdGetterAbiReceipt
    maboGoldenObservation
    "RequestProject.Cli.Fetch.fetchEntity"
    "golden-fixture:not-runtime-receipt"

record MaboGetterParityFixture : Set where
  constructor mabo-getter-parity-fixture
  field
    sourceTripleReference : String
    sourceRevisionReference : String
    jmdMachineCommitReference : String
    leanGetter : LeanGetterObservation
    slrGetter : SlrGetterObservation
    fixtureUsesExactMaboPropertyTriple : Bool
    sameNormalizedObservationByConstruction : Bool
    runtimeParityObserved : Bool
    exactRuntimeDigestObserved : Bool
    fixtureCreatesWorldTruth : Bool
    fixtureCreatesLegalAuthority : Bool

open MaboGetterParityFixture public

canonicalMaboGetterParityFixture : MaboGetterParityFixture
canonicalMaboGetterParityFixture =
  mabo-getter-parity-fixture
    "DASHI.Wikimedia.MaboPropertyTripleProjectionExact.maboParticipantPropertyTriple"
    MaboReview.maboRevision
    Machine.jmdIntegratedCommit
    maboLeanGetterFixture
    maboSlrGetterFixture
    true true false false false false

------------------------------------------------------------------------
-- Source-owner reuse pins.
------------------------------------------------------------------------

maboFixtureSubjectPinned :
  Property.tripleSubject MaboTriple.maboParticipantPropertyTriple ≡ "Q1501525"
maboFixtureSubjectPinned = MaboTriple.maboParticipantTripleSubject

maboFixturePropertyPinned :
  Property.tripleProperty MaboTriple.maboParticipantPropertyTriple ≡ "P710"
maboFixturePropertyPinned = MaboTriple.maboParticipantTripleProperty

maboFixtureObjectPinned :
  Property.tripleObject MaboTriple.maboParticipantPropertyTriple ≡ "Q975866"
maboFixtureObjectPinned = MaboTriple.maboParticipantTripleObject

------------------------------------------------------------------------
-- Firewalls.
------------------------------------------------------------------------

data GoldenParityFixtureEqualsObservedRuntimeParity : Set where
data SharedNormalizedObservationEqualsIndependentObservation : Set where
data PlaceholderDigestEqualsObservedContentDigest : Set where

goldenFixtureDoesNotEqualObservedRuntimeParity :
  GoldenParityFixtureEqualsObservedRuntimeParity → ⊥
goldenFixtureDoesNotEqualObservedRuntimeParity ()

sharedNormalizedObservationDoesNotEstablishIndependentObservation :
  SharedNormalizedObservationEqualsIndependentObservation → ⊥
sharedNormalizedObservationDoesNotEstablishIndependentObservation ()

placeholderDigestDoesNotEqualObservedContentDigest :
  PlaceholderDigestEqualsObservedContentDigest → ⊥
placeholderDigestDoesNotEqualObservedContentDigest ()
