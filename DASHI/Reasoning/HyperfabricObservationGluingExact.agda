module DASHI.Reasoning.HyperfabricObservationGluingExact where

------------------------------------------------------------------------
-- LOCAL OBSERVATIONS DO NOT AUTOMATICALLY GLUE TO A GLOBAL SECTION
--
-- TypedHyperfabricCore already makes global-section compatibility explicit.
-- This module extracts that obligation as an observer/reconstruction boundary
-- and gives a finite incompatible local assignment.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

import DASHI.Reasoning.TypedHyperfabricCore as Hyper

record LocalAssignment
    {Vertex Edge : Set}
    (fabric : Hyper.TypedHyperfabric Vertex Edge) : Set₁ where
  constructor localAssignment
  field
    vertexValue : (vertex : Vertex) → Hyper.vertexStalk fabric vertex
    edgeValue : (edge : Edge) → Hyper.edgeStalk fabric edge

open LocalAssignment public

AssignmentCompatible :
  ∀ {Vertex Edge : Set}
    {fabric : Hyper.TypedHyperfabric Vertex Edge} →
  LocalAssignment fabric → Set
AssignmentCompatible {fabric = fabric} assignment =
  ∀ {vertex edge}
    (membership : Hyper.incidence fabric vertex edge) →
  Hyper.restrict fabric membership (vertexValue assignment vertex)
    ≡ edgeValue assignment edge

compatibleAssignmentGivesGlobalSection :
  ∀ {Vertex Edge : Set}
    {fabric : Hyper.TypedHyperfabric Vertex Edge}
    (assignment : LocalAssignment fabric) →
  AssignmentCompatible assignment →
  String →
  Hyper.GlobalSection fabric
compatibleAssignmentGivesGlobalSection assignment compatible receipt = record
  { Hyper.vertexValue = vertexValue assignment
  ; Hyper.edgeValue = edgeValue assignment
  ; Hyper.compatible = compatible
  ; Hyper.sectionReceipt = receipt
  }

------------------------------------------------------------------------
-- Tiny falsifier: one local vertex says false while the shared edge says true.
------------------------------------------------------------------------

data One : Set where one : One

booleanFabric : Hyper.TypedHyperfabric One One
booleanFabric = record
  { Hyper.vertexStalk = λ _ → Bool
  ; Hyper.edgeStalk = λ _ → Bool
  ; Hyper.incidence = λ _ _ → ⊤
  ; Hyper.restrict = λ _ value → value
  ; Hyper.edgeProvenance = λ _ → []
  ; Hyper.edgeSalience = λ _ → zero
  ; Hyper.fabricLabel = "one-edge Boolean gluing falsifier"
  }

incompatibleLocalAssignment : LocalAssignment booleanFabric
incompatibleLocalAssignment =
  localAssignment (λ _ → false) (λ _ → true)

falseNotTrue : false ≡ true → ⊥
falseNotTrue ()

incompatibleAssignmentCannotGlue :
  AssignmentCompatible incompatibleLocalAssignment → ⊥
incompatibleAssignmentCannotGlue compatible = falseNotTrue (compatible tt)

record HyperfabricObservationGluingBoundary : Set where
  constructor hyperfabricObservationGluingBoundary
  field
    localValuesAutomaticallyFormGlobalSection : Bool
    localValuesAutomaticallyFormGlobalSectionIsFalse :
      localValuesAutomaticallyFormGlobalSection ≡ false
    compatibilityWitnessSufficesForGlobalSection : Bool
    compatibilityWitnessSufficesForGlobalSectionIsTrue :
      compatibilityWitnessSufficesForGlobalSection ≡ true
    localCompatibilityAutomaticallyImpliesSeparatingObservation : Bool
    localCompatibilityAutomaticallyImpliesSeparatingObservationIsFalse :
      localCompatibilityAutomaticallyImpliesSeparatingObservation ≡ false

canonicalHyperfabricObservationGluingBoundary :
  HyperfabricObservationGluingBoundary
canonicalHyperfabricObservationGluingBoundary =
  hyperfabricObservationGluingBoundary
    false refl
    true refl
    false refl
