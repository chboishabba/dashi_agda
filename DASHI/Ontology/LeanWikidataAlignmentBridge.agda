module DASHI.Ontology.LeanWikidataAlignmentBridge where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List)
open import Agda.Builtin.String using (String)

open import DASHI.Ontology.EpistemicTrit
open import DASHI.Ontology.LeanWikidataCertificateBridge
open import DASHI.Ontology.LeanWikidataTheoremSurfaceBridge
import DASHI.Interop.WikidataCandidateRoleBridge as CandidateRole
import DASHI.Core.AuthorityNonPromotionCore as Authority

------------------------------------------------------------------------
-- RequestProject.Alignment is the direct source-side realisation of the
-- mapped-ontology idea: preserve/reflect subclass and instance structure and
-- transport disjointness consequences through an explicit alignment map.
------------------------------------------------------------------------

data AlignmentWitnessKind : Set where
  subclassAlignment instanceAlignment disjointnessAlignment : AlignmentWitnessKind

record LeanAlignmentWitness : Set where
  constructor leanAlignmentWitness
  field
    witnessKind : AlignmentWitnessKind
    theoremContract : LeanTheoremContract
    sourceMatched : Bool
    theoremAccepted : Bool
    sourceReferences : List String

open LeanAlignmentWitness public

alignmentWitnessState : LeanAlignmentWitness → EpistemicTrit
alignmentWitnessState witness =
  theoremReceiptState (theoremAccepted witness) (sourceMatched witness)

alignmentComparison :
  LeanAlignmentWitness → EpistemicTrit → RelationComparisonDisposition
alignmentComparison witness external =
  compareRelationStates (alignmentWitnessState witness) external

subclassAlignmentContract : LeanTheoremContract
subclassAlignmentContract = contract7

disjointnessAlignmentContract : LeanTheoremContract
disjointnessAlignmentContract = contract8

sourceMismatchAlignmentUnresolved :
  (witness : LeanAlignmentWitness) →
  sourceMatched witness ≡ false →
  alignmentWitnessState witness ≡ unresolved
sourceMismatchAlignmentUnresolved witness refl with theoremAccepted witness
... | false = refl
... | true = refl

missingExternalAlignmentEvidenceUnresolved :
  (witness : LeanAlignmentWitness) →
  alignmentWitnessState witness ≡ supported →
  alignmentComparison witness unresolved ≡ comparisonUnresolved
missingExternalAlignmentEvidenceUnresolved witness refl = refl

------------------------------------------------------------------------
-- Alignment evidence is candidate/diagnostic evidence only.  It does not turn
-- an external ontology into DASHI truth authority.
------------------------------------------------------------------------

alignmentCarriesTruthAuthority : LeanAlignmentWitness → Bool
alignmentCarriesTruthAuthority _ = false

alignmentCarriesEditAuthority : LeanAlignmentWitness → Bool
alignmentCarriesEditAuthority _ = false

alignmentTruthAuthorityFalse :
  (witness : LeanAlignmentWitness) → alignmentCarriesTruthAuthority witness ≡ false
alignmentTruthAuthorityFalse witness = refl

alignmentEditAuthorityFalse :
  (witness : LeanAlignmentWitness) → alignmentCarriesEditAuthority witness ≡ false
alignmentEditAuthorityFalse witness = refl

authorityBoundary : Authority.AuthorityNonPromotionBundle
authorityBoundary = Authority.mkClosedAuthorityNonPromotionBundle
  "James/Aristotle Wikidata Alignment bridge"
