module DASHI.Core.ProvenanceClosureIndependenceExact where

------------------------------------------------------------------------
-- Evidence independence is about shared upstream lineage, not modality names.
-- Reuse the exact reflexive/transitive affected-closure object as provenance
-- reachability, then define independence by absence of a common declared root.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true)

import DASHI.Core.AffectedDependencyClosureExact as Closure

record ProvenanceSystem (Artifact : Set) : Set₁ where
  constructor provenanceSystem
  field
    Depends : Artifact → Artifact → Set
    Root : Artifact → Set

open ProvenanceSystem public

UpstreamOf :
  ∀ {Artifact} →
  ProvenanceSystem Artifact →
  Artifact → Artifact → Set
UpstreamOf system source target =
  Closure.AffectedClosure (Depends system) source target

IndependentByUpstreamClosure :
  ∀ {Artifact} →
  (system : ProvenanceSystem Artifact) →
  Artifact → Artifact → Set
IndependentByUpstreamClosure system left right =
  (root : _) →
  Root system root →
  UpstreamOf system root left →
  UpstreamOf system root right →
  ⊥

record SharedUpstreamRoot
    {Artifact : Set}
    (system : ProvenanceSystem Artifact)
    (left right : Artifact) : Set₁ where
  constructor sharedUpstreamRoot
  field
    root : Artifact
    rootDeclared : Root system root
    reachesLeft : UpstreamOf system root left
    reachesRight : UpstreamOf system root right

open SharedUpstreamRoot public

sharedUpstreamRootRefutesIndependence :
  ∀ {Artifact}
    {system : ProvenanceSystem Artifact}
    {left right : Artifact} →
  SharedUpstreamRoot system left right →
  IndependentByUpstreamClosure system left right →
  ⊥
sharedUpstreamRootRefutesIndependence shared independent =
  independent
    (root shared)
    (rootDeclared shared)
    (reachesLeft shared)
    (reachesRight shared)

record ProvenanceClosureBoundary : Set where
  constructor provenanceClosureBoundary
  field
    differentModalitiesNeedNotBeIndependent : Bool
    directParentsAreNotEnoughForIndependence : Bool
    sharedTransitiveRootRefutesIndependence : Bool
    provenanceClosureIsNotACorrelationModel : Bool
    absenceOfKnownSharedRootIsRelativeToDeclaredGraph : Bool

canonicalProvenanceClosureBoundary : ProvenanceClosureBoundary
canonicalProvenanceClosureBoundary =
  provenanceClosureBoundary true true true true true
