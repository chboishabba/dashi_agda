module DASHI.Ontology.LeanWikidataCertificateBridgeTests where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using ([]; _∷_)

open import DASHI.Ontology.EpistemicTrit
open import DASHI.Ontology.LeanWikidataCertificateBridge
open import DASHI.Ontology.LeanWikidataSourceSnapshot

------------------------------------------------------------------------
-- Source-faithful worked fragment from the uploaded Aristotle archive:
-- RequestProject/ClassAlgebra.lean, ClassAlgebraExample.artistKB.
--
-- `artist` (Q483501) is checked as the overlapping union P2737 of
-- `painter` (Q1028181) and `sculptor` (Q1281618).  The exact Lean checker
-- and proof names are pinned in LeanWikidataSourceSnapshot.
------------------------------------------------------------------------

artistUnionCertificate : LeanOntologyCertificate
artistUnionCertificate =
  leanOntologyCertificate
    aristotleRequestId
    classAlgebraModule
    unionSoundnessTheorem
    unionChecker
    "sha256:6ee3b2371498d67c159fe97389c9ca1e06144ad530e17554cb3f87968c9f899a#ClassAlgebraExample.artistKB"
    artistQid
    "wdt:P2737"
    artistUnionParts
    unionOf
    ("aristotle:ae06ae06-2580-422a-8fc3-92aeaaca8762"
      ∷ "lean:Wikidata.ClassAlgebraExample.artistKB_unionOk"
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
    aristotleRequestId
    classAlgebraModule
    unionSoundnessTheorem
    unionChecker
    "sha256:6ee3b2371498d67c159fe97389c9ca1e06144ad530e17554cb3f87968c9f899a#ClassAlgebraExample.artistKB"
    artistQid
    "wdt:P2737"
    artistUnionParts
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
