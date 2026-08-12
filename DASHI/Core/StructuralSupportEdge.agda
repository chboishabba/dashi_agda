module DASHI.Core.StructuralSupportEdge where

open import Agda.Builtin.String using (String)

import DASHI.Core.TypedDependencyCore as Dependency

------------------------------------------------------------------------
-- Canonical structural support / realisation edge.
--
-- The evidence payload states why one representation structurally supports
-- another.  The edge carries provenance/scope through DependencyWitness and
-- grants no identity authority.
------------------------------------------------------------------------

record StructuralSupportRelation
    {Source Target Evidence : Set}
    (source : Source)
    (target : Target) : Set where
  constructor structuralSupportRelation
  field
    supportEvidence : Evidence

open StructuralSupportRelation public

StructuralSupportEdge :
  (Source Target Evidence : Set) → Set
StructuralSupportEdge Source Target Evidence =
  Dependency.DependencyWitness
    (StructuralSupportRelation
      {Source = Source}
      {Target = Target}
      {Evidence = Evidence})

structuralSupportEdge :
  ∀ {Source Target Evidence} →
  (source : Source) →
  (target : Target) →
  Evidence → String → String →
  StructuralSupportEdge Source Target Evidence
structuralSupportEdge source target evidence provenance scope =
  Dependency.dependencyWitness
    source
    target
    (structuralSupportRelation evidence)
    Dependency.structuralLayer
    Dependency.requiredDependency
    provenance
    scope
