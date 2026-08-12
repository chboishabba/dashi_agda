module DASHI.Core.StructuralSupportEdge where

open import Agda.Builtin.String using (String)

import DASHI.Core.TypedDependencyCore as Dependency

------------------------------------------------------------------------
-- Canonical structural support / realisation edge.
--
-- Support evidence is endpoint-dependent: an exact seam proof may mention both
-- source and target. Therefore the core reuses the existing dependent
-- `Relation : Source -> Target -> Set` shape directly rather than flattening
-- evidence into an unindexed payload.
------------------------------------------------------------------------

StructuralSupportEdge :
  ∀ {Source Target : Set} →
  (Relation : Source → Target → Set) → Set
StructuralSupportEdge Relation = Dependency.DependencyWitness Relation

structuralSupportEdgeAt :
  ∀ {Source Target}
    {Relation : Source → Target → Set} →
  Dependency.DependencyLayer →
  Dependency.DependencyDisposition →
  (source : Source) →
  (target : Target) →
  Relation source target →
  String → String →
  StructuralSupportEdge Relation
structuralSupportEdgeAt layer disposition source target evidence provenance scope =
  Dependency.dependencyWitness
    source
    target
    evidence
    layer
    disposition
    provenance
    scope

structuralSupportEdge :
  ∀ {Source Target}
    {Relation : Source → Target → Set} →
  (source : Source) →
  (target : Target) →
  Relation source target →
  String → String →
  StructuralSupportEdge Relation
structuralSupportEdge =
  structuralSupportEdgeAt
    Dependency.structuralLayer
    Dependency.requiredDependency
