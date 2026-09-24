module DASHI.Core.ResolutionImpactIndexExact where

open import DASHI.Core.Prelude

------------------------------------------------------------------------
-- RESOLUTION IMPACT INDEX
--
-- The index stores reverse evidence for modules whose declarations may need
-- re-resolution after a source change. It accelerates invalidation planning;
-- it is not semantic authority and may not admit dependencies by itself.
------------------------------------------------------------------------

data ImpactEvidenceKind : Set where
  importsTarget : ImpactEvidenceKind
  opensTarget : ImpactEvidenceKind
  qualifiedReferenceTarget : ImpactEvidenceKind

record ResolutionImpactIndexBoundary : Set where
  constructor resolutionImpactIndexBoundary
  field
    indexMayInventDependency : Bool
    indexMayInventDependencyIsFalse :
      indexMayInventDependency ≡ false

    indexMayUseBareNameUniquenessAsEvidence : Bool
    indexMayUseBareNameUniquenessAsEvidenceIsFalse :
      indexMayUseBareNameUniquenessAsEvidence ≡ false

    changedFileUpdateMayRetainStaleReverseEvidence : Bool
    changedFileUpdateMayRetainStaleReverseEvidenceIsFalse :
      changedFileUpdateMayRetainStaleReverseEvidence ≡ false

    indexMayAccelerateAffectedScopeDiscovery : Bool
    indexMayAccelerateAffectedScopeDiscoveryIsTrue :
      indexMayAccelerateAffectedScopeDiscovery ≡ true

canonicalResolutionImpactIndexBoundary :
  ResolutionImpactIndexBoundary
canonicalResolutionImpactIndexBoundary =
  resolutionImpactIndexBoundary
    false refl
    false refl
    false refl
    true refl
