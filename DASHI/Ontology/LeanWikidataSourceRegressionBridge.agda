module DASHI.Ontology.LeanWikidataSourceRegressionBridge where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using ([]; _∷_)

open import DASHI.Ontology.EpistemicTrit
open import DASHI.Ontology.LeanWikidataFullSourceManifest
open import DASHI.Ontology.LeanWikidataTheoremSurfaceBridge
open import DASHI.Ontology.LeanWikidataVerdictBridge

------------------------------------------------------------------------
-- Concrete source-computed examples from the supplied Aristotle archive.
--
-- These are not re-proved by Agda.  They pin exact Lean theorem propositions
-- from the supplied source and exercise the bridge's positive/negative verdict
-- semantics.  This is the first regression lane based on actual KB fragments,
-- rather than only generic theorem names.
------------------------------------------------------------------------

artistUnionComputed : LeanTheoremContract
artistUnionComputed =
  leanTheoremContract classAlgebraSource
    "Wikidata.ClassAlgebraExample.artistKB_unionOk"
    "worked artist fragment accepts P2737 union of painter and sculptor"
    checkerSoundness

artistNotDisjointUnionComputed : LeanTheoremContract
artistNotDisjointUnionComputed =
  leanTheoremContract classAlgebraSource
    "Wikidata.ClassAlgebraExample.artistKB_not_dunOk"
    "worked artist fragment rejects disjoint union because membership overlaps"
    negativeConstraintTheorem

artistIntersectionComputed : LeanTheoremContract
artistIntersectionComputed =
  leanTheoremContract classAlgebraSource
    "Wikidata.ClassAlgebraExample.artistKB_interOk"
    "worked painter-sculptor class accepts intersection checker"
    checkerSoundness

brokenKbInvalidComputed : LeanTheoremContract
brokenKbInvalidComputed =
  leanTheoremContract diagnosticsSource
    "Wikidata.KB.brokenKB_not_valid"
    "diagnostic worked KB is explicitly invalid"
    diagnosticExactness

brokenKbCycleComputed : LeanTheoremContract
brokenKbCycleComputed =
  leanTheoremContract diagnosticsSource
    "Wikidata.KB.brokenKB_cycles"
    "diagnostic worked KB contains the reported subclass cycle"
    diagnosticExactness

brokenKbDisjointComputed : LeanTheoremContract
brokenKbDisjointComputed =
  leanTheoremContract diagnosticsSource
    "Wikidata.KB.brokenKB_disjoint"
    "diagnostic worked KB contains the reported disjointness violation"
    diagnosticExactness

redundantKbValidComputed : LeanTheoremContract
redundantKbValidComputed =
  leanTheoremContract redundancySource
    "Wikidata.KB.redundantKB_valid"
    "redundancy worked KB is valid before pruning"
    preservationTheorem

redundantKbPrunedComputed : LeanTheoremContract
redundantKbPrunedComputed =
  leanTheoremContract redundancySource
    "Wikidata.KB.redundantKB_pruned"
    "redundancy worked KB preserves derived facts after pruning"
    repairSoundness

badAlignmentRejectedComputed : LeanTheoremContract
badAlignmentRejectedComputed =
  leanTheoremContract alignmentSource
    "Wikidata.AlignmentExample.bad_links_alignOk_false"
    "worked bad cross-ontology alignment is explicitly rejected"
    crossOntologyTheorem

adamsInstanceComputed : LeanTheoremContract
adamsInstanceComputed =
  leanTheoremContract rdfSource
    "Wikidata.RdfExample.adams_entity_computed"
    "RDF worked fragment computes Q42 instance of Q35120"
    checkerExactness

refs =
  "aristotle:ae06ae06-2580-422a-8fc3-92aeaaca8762"
  ∷ "archive-sha256:d394cd224742dea06a47d2cc6c150e9284e2d6ea291a02c3ba2b2dd04d4f5f88"
  ∷ []

artistUnionVerdict : LeanCertifiedVerdict
artistUnionVerdict =
  leanCertifiedVerdict artistUnionComputed "artist union check" true true certifiedHolds refs

artistNotDisjointUnionVerdict : LeanCertifiedVerdict
artistNotDisjointUnionVerdict =
  leanCertifiedVerdict artistNotDisjointUnionComputed "artist is a disjoint union" true true certifiedRefuted refs

brokenKbValidityVerdict : LeanCertifiedVerdict
brokenKbValidityVerdict =
  leanCertifiedVerdict brokenKbInvalidComputed "brokenKB is valid" true true certifiedRefuted refs

badAlignmentVerdict : LeanCertifiedVerdict
badAlignmentVerdict =
  leanCertifiedVerdict badAlignmentRejectedComputed "bad links satisfy alignOk" true true certifiedRefuted refs

adamsInstanceVerdict : LeanCertifiedVerdict
adamsInstanceVerdict =
  leanCertifiedVerdict adamsInstanceComputed "Q42 isInstanceOf Q35120 in RDF worked fragment" true true certifiedHolds refs

artistUnionSupported : positivePropositionState artistUnionVerdict ≡ supported
artistUnionSupported = refl

artistDisjointUnionExplicitlyContradicted :
  positivePropositionState artistNotDisjointUnionVerdict ≡ contradicted
artistDisjointUnionExplicitlyContradicted = refl

brokenKbValidityExplicitlyContradicted :
  positivePropositionState brokenKbValidityVerdict ≡ contradicted
brokenKbValidityExplicitlyContradicted = refl

badAlignmentExplicitlyContradicted :
  positivePropositionState badAlignmentVerdict ≡ contradicted
badAlignmentExplicitlyContradicted = refl

adamsInstanceSupported : positivePropositionState adamsInstanceVerdict ≡ supported
adamsInstanceSupported = refl
