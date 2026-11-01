module DASHI.Core.ClassificationEdge where

open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)

import DASHI.Core.TypedDependencyCore as Dependency

------------------------------------------------------------------------
-- Canonical revisable classification edge.
--
-- Classification is a proposition-local, evidence-bearing dependency from a
-- stable subject to a target in some classification codomain.  The target may
-- be an entity candidate, a soft type, a domain category, etc.  Identity and
-- truth authority remain application-specific and are not supplied here.
------------------------------------------------------------------------

record ClassificationRelation
    {Subject Target Evidence : Set}
    (subject : Subject)
    (target : Target) : Set where
  constructor classificationRelation
  field
    classificationEvidence : Evidence
    classificationRevision : Nat

open ClassificationRelation public

ClassificationEdge :
  (Subject Target Evidence : Set) → Set
ClassificationEdge Subject Target Evidence =
  Dependency.DependencyWitness
    (ClassificationRelation {Subject = Subject} {Target = Target} {Evidence = Evidence})

classificationEdge :
  ∀ {Subject Target Evidence} →
  (subject : Subject) →
  (target : Target) →
  Evidence → Nat → String → String →
  ClassificationEdge Subject Target Evidence
classificationEdge subject target evidence revision provenance scope =
  Dependency.dependencyWitness
    subject
    target
    (classificationRelation evidence revision)
    Dependency.epistemicLayer
    Dependency.optionalDependency
    provenance
    scope
