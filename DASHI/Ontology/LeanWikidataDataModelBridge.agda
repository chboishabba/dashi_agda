module DASHI.Ontology.LeanWikidataDataModelBridge where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List)
open import Agda.Builtin.String using (String)

open import DASHI.Ontology.EpistemicTrit
open import DASHI.Ontology.ContextualClaimComposition
open import DASHI.Ontology.WikidataEpistemicBridge
open import DASHI.Ontology.LeanWikidataTheoremSurfaceBridge

------------------------------------------------------------------------
-- James's Ranks/Rdf layers use Wikidata's native notion of a *truthy query
-- projection*: preferred statements, or normal statements when no preferred
-- statement exists, and never deprecated statements.  That is a data/query
-- semantics.  DASHI's `EpistemicTrit` is an evidence state.  They must not be
-- identified merely because both use truth-adjacent vocabulary.
------------------------------------------------------------------------

data LeanDataProjection : Set where
  fullStatementLayer truthyQueryLayer reifiedRdfLayer directRdfLayer : LeanDataProjection

record LeanDataModelWitness : Set where
  constructor leanDataModelWitness
  field
    projection : LeanDataProjection
    theoremContract : LeanTheoremContract
    sourceMatched : Bool
    theoremAccepted : Bool
    sourceReferences : List String

open LeanDataModelWitness public

data LeanDataContext : Set where
  rankContext qualifierContext referenceContext temporalContext serializationContext : LeanDataContext

dataModelWitnessState : LeanDataModelWitness → EpistemicTrit
dataModelWitnessState witness =
  theoremReceiptState (theoremAccepted witness) (sourceMatched witness)

dataModelScopedClaim : LeanDataModelWitness → ScopedClaim LeanDataContext
dataModelScopedClaim witness =
  scopedClaim (λ _ → dataModelWitnessState witness) (sourceReferences witness)

rankExclusionContract : LeanTheoremContract
rankExclusionContract = contract15

rdfLosslessnessContract : LeanTheoremContract
rdfLosslessnessContract = contract30

rdfEntailmentSoundnessContract : LeanTheoremContract
rdfEntailmentSoundnessContract = contract31

rdfSubclassExactnessContract : LeanTheoremContract
rdfSubclassExactnessContract = contract34

-- Native Wikidata rank remains metadata in the existing DASHI adapter.  A
-- preferred/deprecated rank does not by itself rewrite an epistemic state.
rankProjectionIsEpistemicTruth : Bool
rankProjectionIsEpistemicTruth = false

rankProjectionIsEpistemicTruthFalse : rankProjectionIsEpistemicTruth ≡ false
rankProjectionIsEpistemicTruthFalse = refl

-- A failed or source-mismatched serialization/entailment receipt is unresolved,
-- not evidence that the opposite world fact is true.
sourceMismatchUnresolved :
  (witness : LeanDataModelWitness) →
  sourceMatched witness ≡ false →
  dataModelWitnessState witness ≡ unresolved
sourceMismatchUnresolved witness refl with theoremAccepted witness
... | false = refl
... | true = refl
