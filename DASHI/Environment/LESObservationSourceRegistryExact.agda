module DASHI.Environment.LESObservationSourceRegistryExact where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)

------------------------------------------------------------------------
-- SOURCE-BOUNDED REGISTRY FOR LES SITUATED OBSERVATION
--
-- Repository policy: source calibration, DASHI reconstruction, cross-source
-- inference, new DASHI theorem, and external promotion remain distinct.
--
-- Holmgren is credited only with the permaculture design principle and its
-- observation/interaction motivation.  The observer-context hyperfabric,
-- non-factorability witnesses, PNF adapters, prediction-envelope bridges and
-- discovery-cone mathematics are repository-native DASHI extensions.
------------------------------------------------------------------------

data SourceKind : Set where
  book existingTypedOwner : SourceKind

data SourceRole : Set where
  observeInteractCalibration provenancePreservingKnowledgeBoundary : SourceRole

record SourceReference : Set where
  constructor sourceReference
  field
    authors : String
    title : String
    venue : String
    year : Nat
    identifier : String
    kind : SourceKind
    role : SourceRole
    boundedReading : String
    excludedPromotion : String

open SourceReference public

holmgren2002 : SourceReference
holmgren2002 =
  sourceReference
    "David Holmgren"
    "Permaculture: Principles & Pathways Beyond Sustainability"
    "Holmgren Design Services"
    2002
    "ISBN 9780646418445"
    book
    observeInteractCalibration
    "Source calibration for the permaculture design principle Observe and Interact and for iterative observation/interaction as a design orientation."
    "Does not state or prove DASHI observer-context hyperfabric, non-factorability, evidence-fibre, prediction-envelope, PNF, causal/discovery-cone, or authority theorems."

kimmererTypedOwner : SourceReference
kimmererTypedOwner =
  sourceReference
    "Source attribution inherited through DASHI.Culture.KimmererTwoEyedSeeingInterpretationBoundaryExact"
    "Typed Kimmerer / Two-Eyed Seeing interpretation boundary"
    "DASHI source-bounded cultural owner"
    2026
    "Repository-native typed source owner; consult imported module for its external bibliography"
    existingTypedOwner
    provenancePreservingKnowledgeBoundary
    "Reuses the existing typed owner for the distinction between coordinated ecological observation and retained knowledge provenance."
    "Does not flatten Indigenous and scientific knowledge histories into one sensor model and does not attribute DASHI factorisation theorems to the cited authors."

lesObservationSources : List SourceReference
lesObservationSources = holmgren2002 ∷ kimmererTypedOwner ∷ []

record LESObservationAttributionBoundary : Set where
  constructor lesObservationAttributionBoundary
  field
    holmgrenProvesDASHINonFactorability : Bool
    holmgrenProvesDASHINonFactorabilityIsFalse :
      holmgrenProvesDASHINonFactorability ≡ false

    permaculturePrincipleProvesEmpiricalDynamics : Bool
    permaculturePrincipleProvesEmpiricalDynamicsIsFalse :
      permaculturePrincipleProvesEmpiricalDynamics ≡ false

    inheritedKimmererOwnerMakesKnowledgeSystemsIdentical : Bool
    inheritedKimmererOwnerMakesKnowledgeSystemsIdenticalIsFalse :
      inheritedKimmererOwnerMakesKnowledgeSystemsIdentical ≡ false

    observerContextFormalismIsDASHIExtension : Bool
    observerContextFormalismIsDASHIExtensionIsTrue :
      observerContextFormalismIsDASHIExtension ≡ true

canonicalLESObservationAttributionBoundary : LESObservationAttributionBoundary
canonicalLESObservationAttributionBoundary =
  lesObservationAttributionBoundary
    false refl
    false refl
    false refl
    true refl
