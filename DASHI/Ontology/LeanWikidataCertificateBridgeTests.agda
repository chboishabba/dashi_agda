module DASHI.Ontology.LeanWikidataCertificateBridgeTests where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using ([]; _∷_)

open import DASHI.Ontology.EpistemicTrit
open import DASHI.Ontology.LeanWikidataCertificateBridge

------------------------------------------------------------------------
-- Worked fragment reported by James Michael DuPont on 2026-08-16:
-- artist as a (possibly overlapping) union of painter and sculptor, checked by
-- the theorem-backed executable `unionOk` surface in RequestProject/ClassAlgebra.
-- These string identifiers are provenance labels only; the formal claims below
-- concern the certificate import semantics, not the live Wikidata graph.
------------------------------------------------------------------------

artistUnionCertificate : LeanOntologyCertificate
artistUnionCertificate =
  leanOntologyCertificate
    "ae06ae06-2580-422a-8fc3-92aeaaca8762"
    "RequestProject.ClassAlgebra"
    "unionOk_sound"
    "unionOk"
    "worked-fragment:artist-painter-sculptor"
    "wd:artist"
    "wdt:P2737"
    "wd:painter|wd:sculptor"
    unionOf
    ("aristotle:ae06ae06-2580-422a-8fc3-92aeaaca8762"
      ∷ "reported-by:James-Michael-DuPont:2026-08-16"
      ∷ [])
    true
    true

artistUnionCertificateSupported :
  certificateState artistUnionCertificate ≡ supported
artistUnionCertificateSupported = refl

artistUnionReplicatedBySupportedExternalWitness :
  compareRelationStates
    (certificateState artistUnionCertificate)
    supported
  ≡ replicated
artistUnionReplicatedBySupportedExternalWitness = refl

artistUnionExplicitExternalOppositionConflicts :
  compareRelationStates
    (certificateState artistUnionCertificate)
    contradicted
  ≡ conflicting
artistUnionExplicitExternalOppositionConflicts = refl

failedArtistUnionCertificate : LeanOntologyCertificate
failedArtistUnionCertificate =
  leanOntologyCertificate
    "ae06ae06-2580-422a-8fc3-92aeaaca8762"
    "RequestProject.ClassAlgebra"
    "unionOk_sound"
    "unionOk"
    "worked-fragment:artist-painter-sculptor"
    "wd:artist"
    "wdt:P2737"
    "wd:painter|wd:sculptor"
    unionOf
    []
    false
    true

failedArtistUnionIsNotNegativeEvidence :
  certificateState failedArtistUnionCertificate ≡ unresolved
failedArtistUnionIsNotNegativeEvidence = refl

failedArtistUnionCannotConflictWithSupport :
  compareRelationStates
    (certificateState failedArtistUnionCertificate)
    supported
  ≡ comparisonUnresolved
failedArtistUnionCannotConflictWithSupport = refl

artistUnionCertificateNoTruthAuthority :
  certificateCarriesTruthAuthority artistUnionCertificate ≡ false
artistUnionCertificateNoTruthAuthority = refl

artistUnionCertificateNoEditAuthority :
  certificateCarriesEditAuthority artistUnionCertificate ≡ false
artistUnionCertificateNoEditAuthority = refl
