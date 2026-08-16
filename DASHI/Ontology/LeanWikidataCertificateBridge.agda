module DASHI.Ontology.LeanWikidataCertificateBridge where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List)
open import Agda.Builtin.String using (String)

open import DASHI.Ontology.EpistemicTrit
open import DASHI.Ontology.ContextualClaimComposition

------------------------------------------------------------------------
-- Provenance
--
-- Integration surface for the machine-checked Lean 4 Wikidata ontology work
-- reported by James Michael DuPont on 2026-08-16, including executable
-- class-algebra checkers such as unionOk/interOk and a refined RDF rendering.
-- The reported WIP request was:
--   Aristotle request ae06ae06-2580-422a-8fc3-92aeaaca8762
--
-- No Lean source is copied here.  This module specifies the certificate
-- contract DASHI expects when importing results from that external checker.
-- A certificate carries theorem/checker provenance but does not acquire global
-- truth authority or edit authority merely by crossing the bridge.
------------------------------------------------------------------------

data LeanRelationKind : Set where
  instanceOf : LeanRelationKind
  subclassOf : LeanRelationKind
  unionOf : LeanRelationKind
  intersectionOf : LeanRelationKind
  disjointUnionOf : LeanRelationKind
  disjointWith : LeanRelationKind
  equivalentClass : LeanRelationKind
  rdfEntailment : LeanRelationKind

data RelationComparisonDisposition : Set where
  replicated : RelationComparisonDisposition
  conflicting : RelationComparisonDisposition
  comparisonUnresolved : RelationComparisonDisposition

record LeanOntologyCertificate : Set where
  constructor leanOntologyCertificate
  field
    requestId : String
    moduleName : String
    theoremName : String
    checkerName : String
    sourceSnapshot : String
    subjectRef : String
    predicateRef : String
    objectRef : String
    relationKind : LeanRelationKind
    sourceReferences : List String
    checkerAccepted : Bool
    theoremBacked : Bool

open LeanOntologyCertificate public

------------------------------------------------------------------------
-- A positive imported result requires BOTH executable acceptance and an
-- explicit theorem-backed checker contract.  Every other state is unresolved.
-- In particular, checker failure or absence is not converted into a negative
-- ontology fact: Wikidata/external ontologies are open-world evidence sources.
------------------------------------------------------------------------

certificateState : LeanOntologyCertificate → EpistemicTrit
certificateState cert with checkerAccepted cert | theoremBacked cert
... | true | true = supported
... | _    | _    = unresolved

acceptedTheoremBackedIsSupported :
  (cert : LeanOntologyCertificate) →
  checkerAccepted cert ≡ true →
  theoremBacked cert ≡ true →
  certificateState cert ≡ supported
acceptedTheoremBackedIsSupported cert refl refl = refl

failedCheckerIsUnresolved :
  (cert : LeanOntologyCertificate) →
  checkerAccepted cert ≡ false →
  certificateState cert ≡ unresolved
failedCheckerIsUnresolved cert refl with theoremBacked cert
... | false = refl
... | true = refl

unbackedCheckerIsUnresolved :
  (cert : LeanOntologyCertificate) →
  theoremBacked cert ≡ false →
  certificateState cert ≡ unresolved
unbackedCheckerIsUnresolved cert refl with checkerAccepted cert
... | false = refl
... | true = refl

------------------------------------------------------------------------
-- Adapter into the existing provenance-bearing DASHI epistemic carrier.
------------------------------------------------------------------------

certificateScopedClaim :
  LeanOntologyCertificate →
  ScopedClaim LeanRelationKind
certificateScopedClaim cert =
  scopedClaim
    (λ _ → certificateState cert)
    (sourceReferences cert)

certificateClaimPreservesState :
  (cert : LeanOntologyCertificate)
  (kind : LeanRelationKind) →
  stateAt (certificateScopedClaim cert) kind ≡ certificateState cert
certificateClaimPreservesState cert kind = refl

certificateClaimPreservesReferences :
  (cert : LeanOntologyCertificate) →
  references (certificateScopedClaim cert) ≡ sourceReferences cert
certificateClaimPreservesReferences cert = refl

------------------------------------------------------------------------
-- Cross-ontology relation comparison.
--
-- `replicated` requires determinate support on both sides.  A genuine conflict
-- requires one side to carry explicit contradictory evidence.  Missing edges,
-- failed checkers, incomplete mappings, or unbacked computations remain
-- unresolved and cannot manufacture a conflict.
------------------------------------------------------------------------

compareRelationStates :
  EpistemicTrit → EpistemicTrit → RelationComparisonDisposition
compareRelationStates supported supported = replicated
compareRelationStates supported contradicted = conflicting
compareRelationStates contradicted supported = conflicting
compareRelationStates contradicted contradicted = replicated
compareRelationStates _ _ = comparisonUnresolved

supportedPairReplicates :
  compareRelationStates supported supported ≡ replicated
supportedPairReplicates = refl

explicitOppositionConflictsLeft :
  compareRelationStates supported contradicted ≡ conflicting
explicitOppositionConflictsLeft = refl

explicitOppositionConflictsRight :
  compareRelationStates contradicted supported ≡ conflicting
explicitOppositionConflictsRight = refl

missingExternalEvidenceIsUnresolved :
  compareRelationStates supported unresolved ≡ comparisonUnresolved
missingExternalEvidenceIsUnresolved = refl

missingLeanEvidenceIsUnresolved :
  compareRelationStates unresolved supported ≡ comparisonUnresolved
missingLeanEvidenceIsUnresolved = refl

failedLeanCheckerCannotConflictWithSupport :
  (cert : LeanOntologyCertificate) →
  checkerAccepted cert ≡ false →
  compareRelationStates (certificateState cert) supported
    ≡ comparisonUnresolved
failedLeanCheckerCannotConflictWithSupport cert refl with theoremBacked cert
... | false = refl
... | true = refl

------------------------------------------------------------------------
-- Authority boundary: imported checker receipts are evidence only.
------------------------------------------------------------------------

certificateCarriesTruthAuthority : LeanOntologyCertificate → Bool
certificateCarriesTruthAuthority _ = false

certificateCarriesEditAuthority : LeanOntologyCertificate → Bool
certificateCarriesEditAuthority _ = false

certificateTruthAuthorityIsFalse :
  (cert : LeanOntologyCertificate) →
  certificateCarriesTruthAuthority cert ≡ false
certificateTruthAuthorityIsFalse cert = refl

certificateEditAuthorityIsFalse :
  (cert : LeanOntologyCertificate) →
  certificateCarriesEditAuthority cert ≡ false
certificateEditAuthorityIsFalse cert = refl
