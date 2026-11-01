module DASHI.Cognition.PNF.SensibLawGenericSourceCompilationCanonicalWeldRegression where

open import Agda.Builtin.Bool using (false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.String using (String)

import DASHI.Cognition.PNF.SensibLawGenericSourceCompilationExact as Ingest
import DASHI.Cognition.PNF.SensibLawGenericSourceCompilationCanonicalWeldExact as Weld
import DASHI.Interop.SLRCanonicalEvidenceSubstrateExact as Canonical

------------------------------------------------------------------------
-- One concrete long-document inhabitant through the real canonical ABI.
------------------------------------------------------------------------

fixtureManifestation : Canonical.EvidenceManifestation
fixtureManifestation =
  Canonical.mkCandidateManifestation
    "manifestation:book:fixture"
    Canonical.otherEvidence
    "book:fixture"
    "book-revision:fixture"
    "sha256:fixture"
    "receipt:book:fixture"

fixtureRevision : Canonical.EvidenceSourceRevision
fixtureRevision =
  Canonical.mkSourceRevision
    fixtureManifestation
    "receipt:book:fixture"

fixtureSource : Weld.GenericCompiledSource
fixtureSource =
  Weld.generic-compiled-source
    Ingest.document
    Ingest.contentSource
    "plain-text"
    fixtureManifestation
    fixtureRevision
    refl
    refl
    refl
    false refl
    false refl
    false refl
    false refl
    false refl

fixtureSpan : Canonical.EvidenceSpan
fixtureSpan =
  Canonical.mkTextRange
    "book-revision:fixture"
    "span:book:fixture:0-10"
    0
    10

fixtureRegion : Weld.GenericSourceRegion fixtureSource
fixtureRegion =
  Weld.generic-source-region
    "region:book:fixture:sentence:1"
    fixtureSpan
    refl
    Weld.semanticCandidate
    false refl
    false refl

fixtureObservation : Canonical.EvidenceObservation
fixtureObservation =
  Canonical.mkCandidateObservation
    "observation:book:fixture:1"
    "book-revision:fixture"
    fixtureSpan
    "predicate:fixture"
    "value:fixture"

fixtureObservationWeld : Canonical.ObservationRevisionWeld fixtureObservation
fixtureObservationWeld =
  Canonical.observation-revision-weld refl

fixtureCompiledCandidate :
  Weld.CompiledRegionCandidate fixtureSource fixtureRegion
fixtureCompiledCandidate =
  Weld.compiled-region-candidate
    fixtureObservation
    refl
    fixtureObservationWeld
    "parser-receipt:fixture"
    false refl
    true refl
    false refl
    false refl

fixtureAssignment : Weld.RegionCompilationAssignment fixtureSource
fixtureAssignment =
  Weld.region-compilation-assignment
    fixtureRegion
    (Weld.compiledCandidate fixtureCompiledCandidate)

fixtureLosslessReceipt : Weld.LosslessCompilationReceipt fixtureSource
fixtureLosslessReceipt =
  Weld.lossless-compilation-receipt
    (fixtureAssignment ∷ [])
    false refl
    false refl
    false refl
    false refl
    false refl

fixtureRegionReallyUsesCanonicalRevision :
  Canonical.spanSourceRevisionRef fixtureSpan
  ≡ Canonical.revisionSourceRevisionRef fixtureRevision
fixtureRegionReallyUsesCanonicalRevision = refl

fixtureObservationReallyUsesRegionSpan :
  Canonical.observationSpan fixtureObservation
  ≡ Weld.GenericSourceRegion.anchor fixtureRegion
fixtureObservationReallyUsesRegionSpan = refl
