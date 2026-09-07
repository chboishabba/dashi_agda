module DASHI.Core.PathSensitiveSupportPolicyBidiExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

import DASHI.Core.TypedProvenancePathBidiExact as Path
import DASHI.Core.ProvenanceSensitiveConsumerAdequacyBidiExact as Adequacy

------------------------------------------------------------------------
-- TYPED PROVENANCE PATH -> CONSUMER ADEQUACY
--
-- Root support decides independence; lineage semantics say how evidence moved
-- through the provenance graph.  A consumer policy may require both, but the
-- semantic path labels do not substitute for an independent-root receipt.
------------------------------------------------------------------------

record PathSensitiveSupport
    {Evidence Root Consumer : Set}
    (policy : Adequacy.ProvenanceAdequacyPolicy Evidence Root Consumer)
    (consumer : Consumer)
    (left right : Evidence) : Set₁ where
  constructor path-sensitive-support
  field
    adequate : Adequacy.AdequatePairFor policy consumer left right
    leftPath : Path.TypedProvenancePath
    rightPath : Path.TypedProvenancePath
    lineagePolicyReference : String
    rootPolicyReference : String

open PathSensitiveSupport public

pathSensitiveSupportStillCarriesIndependentRoots :
  ∀ {Evidence Root Consumer : Set}
    {policy : Adequacy.ProvenanceAdequacyPolicy Evidence Root Consumer}
    {consumer : Consumer} {left right : Evidence} →
  PathSensitiveSupport policy consumer left right →
  Adequacy.IndependentSupport policy left right
pathSensitiveSupportStillCarriesIndependentRoots receipt =
  Adequacy.adequatePairCarriesIndependentSupport (adequate receipt)

------------------------------------------------------------------------
-- Same dependence class with different edge semantics is not independence.
-- The existing exact witness has reportedBy versus amplifiedBy paths while the
-- dependence relation remains definitionally identical.
------------------------------------------------------------------------

sameDependenceDifferentSemantics = Path.sameDependenceDifferentSemantics
reportedNotAmplified = Path.reportedNotAmplified

data DifferentLineageSemanticsCreateIndependentRoots : Set where

differentLineageSemanticsDoNotCreateIndependentRoots :
  DifferentLineageSemanticsCreateIndependentRoots → ⊥
differentLineageSemanticsDoNotCreateIndependentRoots ()

record PathSensitiveSupportBoundary : Set where
  constructor path-sensitive-support-boundary
  field
    rootIndependenceAndLineageSemanticsBothRetained : Bool
    differentEdgeKindsProveIndependentRoots : Bool
    pathSemanticsMayBeConsumerPolicyInput : Bool
    pathSemanticsCreateActionAuthority : Bool

canonicalPathSensitiveSupportBoundary : PathSensitiveSupportBoundary
canonicalPathSensitiveSupportBoundary =
  path-sensitive-support-boundary true false true false
