module DASHI.Ontology.LeanWikidataRdfExactnessBridge where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List)
open import Agda.Builtin.String using (String)

open import DASHI.Ontology.EpistemicTrit
open import DASHI.Ontology.LeanWikidataTheoremSurfaceBridge
import DASHI.Interop.WikidataDerivationFibreBridge as Derivation

------------------------------------------------------------------------
-- RequestProject.Rdf supplies four distinct guarantees that should not be
-- conflated: lossless full reification, sound entailment, exact P279 entailment,
-- and exact P31 entailment.  This surface keeps those guarantees separate while
-- allowing them to feed DASHI's existing Wikidata derivation-fibre lane.
------------------------------------------------------------------------

data LeanRdfGuarantee : Set where
  fullReificationInjective : LeanRdfGuarantee
  entailmentSound : LeanRdfGuarantee
  subclassEntailmentExact : LeanRdfGuarantee
  instanceEntailmentExact : LeanRdfGuarantee
  executableSubclassAgreement : LeanRdfGuarantee

record LeanRdfWitness : Set where
  constructor leanRdfWitness
  field
    guarantee : LeanRdfGuarantee
    theoremContract : LeanTheoremContract
    sourceMatched : Bool
    theoremAccepted : Bool
    sourceReferences : List String

open LeanRdfWitness public

rdfWitnessState : LeanRdfWitness → EpistemicTrit
rdfWitnessState witness =
  theoremReceiptState (theoremAccepted witness) (sourceMatched witness)

fullReificationInjectiveContract : LeanTheoremContract
fullReificationInjectiveContract = contract30

entailmentSoundContract : LeanTheoremContract
entailmentSoundContract = contract31

subclassEntailmentExactContract : LeanTheoremContract
subclassEntailmentExactContract = contract32

instanceEntailmentExactContract : LeanTheoremContract
instanceEntailmentExactContract = contract33

executableSubclassAgreementContract : LeanTheoremContract
executableSubclassAgreementContract = contract34

rdfWitnessCarriesGlobalTruthAuthority : LeanRdfWitness → Bool
rdfWitnessCarriesGlobalTruthAuthority _ = false

rdfWitnessCarriesGlobalTruthAuthorityFalse :
  (witness : LeanRdfWitness) → rdfWitnessCarriesGlobalTruthAuthority witness ≡ false
rdfWitnessCarriesGlobalTruthAuthorityFalse witness = refl

sourceMismatchRdfUnresolved :
  (witness : LeanRdfWitness) →
  sourceMatched witness ≡ false →
  rdfWitnessState witness ≡ unresolved
sourceMismatchRdfUnresolved witness refl with theoremAccepted witness
... | false = refl
... | true = refl
