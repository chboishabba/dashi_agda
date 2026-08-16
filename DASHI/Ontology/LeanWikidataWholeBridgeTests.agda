module DASHI.Ontology.LeanWikidataWholeBridgeTests where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using ([]; _∷_)
open import DASHI.Ontology.EpistemicTrit
open import DASHI.Ontology.LeanWikidataCertificateBridge
open import DASHI.Ontology.LeanWikidataFullSourceManifest
open import DASHI.Ontology.LeanWikidataTheoremSurfaceBridge
open import DASHI.Ontology.LeanWikidataWholeBridge

------------------------------------------------------------------------
-- Diagnostics.lean: the actual source theorem
-- Wikidata.KB.errors_eq_nil_iff_valid is admitted only relative to the pinned
-- Diagnostics.lean source hash and the accepted theorem receipt.
------------------------------------------------------------------------

diagnosticsReceipt : WholeBridgeReceipt
diagnosticsReceipt =
  wholeBridgeReceipt
    diagnosticsSource
    contract28
    diagnosticFact
    true
    true
    ("aristotle:ae06ae06-2580-422a-8fc3-92aeaaca8762"
      ∷ "lean:Wikidata.KB.errors_eq_nil_iff_valid"
      ∷ [])

diagnosticsReceiptSupported :
  wholeBridgeState diagnosticsReceipt ≡ supported
diagnosticsReceiptSupported = refl

diagnosticsReceiptNoTruthAuthority :
  wholeBridgeCarriesTruthAuthority diagnosticsReceipt ≡ false
diagnosticsReceiptNoTruthAuthority = refl

diagnosticsReceiptNoEditAuthority :
  wholeBridgeCarriesEditAuthority diagnosticsReceipt ≡ false
diagnosticsReceiptNoEditAuthority = refl

------------------------------------------------------------------------
-- Rdf.lean: fullGraph_injective is imported as a serialization theorem about
-- the pinned source model, not as a global truth assertion.
------------------------------------------------------------------------

rdfReceipt : WholeBridgeReceipt
rdfReceipt =
  wholeBridgeReceipt
    rdfSource
    contract30
    rdfFact
    true
    true
    ("lean:Wikidata.Rdf.fullGraph_injective" ∷ [])

rdfReceiptSupported : wholeBridgeState rdfReceipt ≡ supported
rdfReceiptSupported = refl

------------------------------------------------------------------------
-- A source-hash mismatch remains unresolved even if a result was claimed.
------------------------------------------------------------------------

mismatchedRdfReceipt : WholeBridgeReceipt
mismatchedRdfReceipt =
  wholeBridgeReceipt
    rdfSource
    contract34
    rdfFact
    false
    true
    []

mismatchedRdfReceiptUnresolved :
  wholeBridgeState mismatchedRdfReceipt ≡ unresolved
mismatchedRdfReceiptUnresolved = refl

mismatchedRdfCannotConflictWithSupport :
  wholeBridgeComparison mismatchedRdfReceipt supported ≡ comparisonUnresolved
mismatchedRdfCannotConflictWithSupport = refl
