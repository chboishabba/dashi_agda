module DASHI.Ontology.LeanWikidataWholeBridge where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.String using (String)

-- Existing DASHI semantics reused by this bridge.
open import DASHI.Ontology.EpistemicTrit
open import DASHI.Ontology.ContextualClaimComposition
open import DASHI.Ontology.WikidataEpistemicBridge
open import DASHI.Ontology.LeanWikidataCertificateBridge
open import DASHI.Ontology.LeanWikidataFullSourceManifest
open import DASHI.Ontology.LeanWikidataTheoremSurfaceBridge
import DASHI.Cognition.PNF.WikidataRepairProposal as Repair
import DASHI.Core.AuthorityNonPromotionCore as Authority
import DASHI.Core.CandidateOnlyCore as Candidate
import DASHI.Interop.WikidataDerivationFibreBridge as Derivation
import DASHI.Interop.WikidataCandidateRoleBridge as CandidateRole

------------------------------------------------------------------------
-- Whole-development bridge.
--
-- James's Lean project remains the proof authority for its own propositions.
-- DASHI imports those propositions as provenance-bearing evidence and composes
-- them with its existing epistemic/review infrastructure. No theorem in this
-- module claims an Agda proof of a Lean proposition merely because the Lean
-- source snapshot has been supplied alongside it.
------------------------------------------------------------------------

data ImportedSurfaceKind : Set where
  classFact propertyFact constraintFact statementFact provenanceFact : ImportedSurfaceKind
  temporalFact identityFact lexicalFact rdfFact diagnosticFact repairFact : ImportedSurfaceKind

record WholeBridgeReceipt : Set where
  constructor wholeBridgeReceipt
  field
    leanModule : LeanSourceModule
    theoremContract : LeanTheoremContract
    surfaceKind : ImportedSurfaceKind
    sourceMatched : Bool
    checkerOrTheoremAccepted : Bool
    receiptReferences : List String

open WholeBridgeReceipt public

wholeBridgeState : WholeBridgeReceipt → EpistemicTrit
wholeBridgeState receipt =
  theoremReceiptState
    (checkerOrTheoremAccepted receipt)
    (sourceMatched receipt)

wholeBridgeScopedClaim : WholeBridgeReceipt → ScopedClaim ImportedSurfaceKind
wholeBridgeScopedClaim receipt =
  scopedClaim (λ _ → wholeBridgeState receipt) (receiptReferences receipt)

wholeBridgePreservesReferences :
  (receipt : WholeBridgeReceipt) →
  ContextualClaimComposition.references (wholeBridgeScopedClaim receipt)
    ≡ receiptReferences receipt
wholeBridgePreservesReferences receipt = refl

------------------------------------------------------------------------
-- Authority and repair boundaries are inherited from existing in-repo DASHI.
------------------------------------------------------------------------

wholeBridgeCarriesTruthAuthority : WholeBridgeReceipt → Bool
wholeBridgeCarriesTruthAuthority _ = false

wholeBridgeCarriesEditAuthority : WholeBridgeReceipt → Bool
wholeBridgeCarriesEditAuthority _ = false

wholeBridgeTruthAuthorityFalse :
  (receipt : WholeBridgeReceipt) →
  wholeBridgeCarriesTruthAuthority receipt ≡ false
wholeBridgeTruthAuthorityFalse receipt = refl

wholeBridgeEditAuthorityFalse :
  (receipt : WholeBridgeReceipt) →
  wholeBridgeCarriesEditAuthority receipt ≡ false
wholeBridgeEditAuthorityFalse receipt = refl

-- The imported diagnostic/repair lane intentionally points at the existing
-- WikidataRepairProposal review-only boundary rather than minting edit authority.
repairBoundary : Repair.WikidataRepairBoundary
repairBoundary = Repair.canonicalWikidataRepairBoundary

-- Reusable authority non-promotion core already used elsewhere in DASHI.
authorityBoundary : Authority.AuthorityNonPromotionBundle
authorityBoundary = Authority.mkClosedAuthorityNonPromotionBundle
  "James/Aristotle Wikidata Lean whole-development bridge"

------------------------------------------------------------------------
-- Cross-ontology comparison keeps open-world absence unresolved.
------------------------------------------------------------------------

wholeBridgeComparison : WholeBridgeReceipt → EpistemicTrit → RelationComparisonDisposition
wholeBridgeComparison receipt external = compareRelationStates (wholeBridgeState receipt) external

sourceMismatchCannotManufactureConflict :
  (receipt : WholeBridgeReceipt) →
  sourceMatched receipt ≡ false →
  wholeBridgeComparison receipt supported ≡ comparisonUnresolved
sourceMismatchCannotManufactureConflict receipt refl with checkerOrTheoremAccepted receipt
... | false = refl
... | true = refl
