module DASHI.Cognition.PNF.AccessActuationOrthogonalityExact where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Empty using (⊥)

------------------------------------------------------------------------
-- Abstract structural bridge to the institutional/AI discussion:
--
--   fast internal control may change accessibility while storage is fixed;
--   an external tool may change actionability while storage/access is fixed.
--
-- The theorem is only the orthogonality of these coordinates.  It does not
-- identify neural access with social/legal actuation.
------------------------------------------------------------------------

record CapabilitySurface : Set where
  constructor capabilitySurface
  field
    stored : Bool
    accessible : Bool
    actionable : Bool

open CapabilitySurface public

baseline : CapabilitySurface
baseline = capabilitySurface true false false

fastAccessExpansion : CapabilitySurface → CapabilitySurface
fastAccessExpansion (capabilitySurface stored access action) =
  capabilitySurface stored true action

externalActuationExpansion : CapabilitySurface → CapabilitySurface
externalActuationExpansion (capabilitySurface stored access action) =
  capabilitySurface stored access true

accessExpanded : CapabilitySurface
accessExpanded = fastAccessExpansion baseline

actuationExpanded : CapabilitySurface
actuationExpanded = externalActuationExpansion baseline

accessExpansionKeepsStoredCarrier : stored accessExpanded ≡ true
accessExpansionKeepsStoredCarrier = refl

actuationExpansionKeepsStoredCarrier : stored actuationExpanded ≡ true
actuationExpansionKeepsStoredCarrier = refl

accessExpansionDoesNotCreateActuation : actionable accessExpanded ≡ false
accessExpansionDoesNotCreateActuation = refl

actuationExpansionDoesNotCreateAccess : accessible actuationExpanded ≡ false
actuationExpansionDoesNotCreateAccess = refl

orthogonalExpansionsAreDistinct : accessExpanded ≡ actuationExpanded → ⊥
orthogonalExpansionsAreDistinct ()

bothExpansionsCompose :
  fastAccessExpansion (externalActuationExpansion baseline)
  ≡ capabilitySurface true true true
bothExpansionsCompose = refl

record AccessActuationBoundary : Set where
  constructor accessActuationBoundary
  field
    sameFormalShapeMeansSameDomainSemantics : Bool
    accessExpansionImpliesTruth : Bool
    actuationExpansionImpliesRefinement : Bool

canonicalAccessActuationBoundary : AccessActuationBoundary
canonicalAccessActuationBoundary =
  accessActuationBoundary false false false
