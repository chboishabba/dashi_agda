module DASHI.Ontology.InferenceLanguageIndexedAlignmentSafetyExact where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Empty using (⊥)

open import DASHI.Ontology.LeanWikidataTheoremSurfaceBridge using (LeanTheoremContract)
open import DASHI.Ontology.LeanWikidataLatestEpistemicConformanceBridge

jmdSubclassAlignmentExactness : LeanTheoremContract
jmdSubclassAlignmentExactness = jmdAlignmentSubclassExact

jmdDisjointnessReflectionNeedsTransport : LeanTheoremContract
jmdDisjointnessReflectionNeedsTransport = jmdAlignmentDisjointReflect

data InferenceLanguage : Set where
  subclassLanguage : InferenceLanguage
  instanceTransportLanguage : InferenceLanguage
  disjointnessLanguage : InferenceLanguage
  disjointUnionLanguage : InferenceLanguage

record AlignmentInferenceProfile : Set where
  constructor alignmentInferenceProfile
  field
    subclassPreserved : Bool
    instanceTransportAvailable : Bool
    targetDisjointnessAvailable : Bool
    finiteUnionCoverageAvailable : Bool
open AlignmentInferenceProfile public

infixr 6 _∧ᵇ_
_∧ᵇ_ : Bool → Bool → Bool
true ∧ᵇ x = x
false ∧ᵇ _ = false

safeFor : AlignmentInferenceProfile → InferenceLanguage → Bool
safeFor profile subclassLanguage = subclassPreserved profile
safeFor profile instanceTransportLanguage = instanceTransportAvailable profile
safeFor profile disjointnessLanguage = instanceTransportAvailable profile ∧ᵇ targetDisjointnessAvailable profile
safeFor profile disjointUnionLanguage =
  subclassPreserved profile ∧ᵇ instanceTransportAvailable profile ∧ᵇ
  targetDisjointnessAvailable profile ∧ᵇ finiteUnionCoverageAvailable profile

subclassOnlyAlignment : AlignmentInferenceProfile
subclassOnlyAlignment = alignmentInferenceProfile true false false false

subclassAndInstancesButNoDisjointness : AlignmentInferenceProfile
subclassAndInstancesButNoDisjointness = alignmentInferenceProfile true true false false

fullFiniteClassAlgebraAlignment : AlignmentInferenceProfile
fullFiniteClassAlgebraAlignment = alignmentInferenceProfile true true true true

subclassOnlyIsSafeForSubclassLookup : safeFor subclassOnlyAlignment subclassLanguage ≡ true
subclassOnlyIsSafeForSubclassLookup = refl

subclassOnlyIsNotSafeForDisjointness : safeFor subclassOnlyAlignment disjointnessLanguage ≡ false
subclassOnlyIsNotSafeForDisjointness = refl

instanceTransportStillDoesNotManufactureTargetDisjointness :
  safeFor subclassAndInstancesButNoDisjointness disjointnessLanguage ≡ false
instanceTransportStillDoesNotManufactureTargetDisjointness = refl

fullProfileSupportsFiniteDisjointUnionLanguage :
  safeFor fullFiniteClassAlgebraAlignment disjointUnionLanguage ≡ true
fullProfileSupportsFiniteDisjointUnionLanguage = refl

record AlignmentSafetyCountermodel : Set where
  constructor alignmentSafetyCountermodel
  field
    profile : AlignmentInferenceProfile
    safeForSubclass : safeFor profile subclassLanguage ≡ true
    unsafeForDisjointness : safeFor profile disjointnessLanguage ≡ false

subclassDoesNotImplyDisjointnessSafety : AlignmentSafetyCountermodel
subclassDoesNotImplyDisjointnessSafety = alignmentSafetyCountermodel subclassOnlyAlignment refl refl

safeForSubclassDoesNotPromoteToDisjointness :
  safeFor subclassOnlyAlignment subclassLanguage ≡ true →
  safeFor subclassOnlyAlignment disjointnessLanguage ≡ true → ⊥
safeForSubclassDoesNotPromoteToDisjointness _ ()
