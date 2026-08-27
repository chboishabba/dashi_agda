module DASHI.Core.OrderedSubstitutionGeometryExact where

------------------------------------------------------------------------
-- ORDERED SUBSTITUTION GEOMETRY
--
-- Generic owner for a distinction that matters in symbolic calculi,
-- rewriting systems, compiler passes and representation pipelines:
--
--   operation A followed by operation B
--
-- need not be licensed interchangeably with
--
--   operation B followed by operation A.
--
-- Merely recording a source-required order does not prove that the two
-- operations are mathematically non-commuting.  Conversely, a source may state
-- that order is irrelevant only under explicit side conditions.  This module
-- keeps those three notions separate.
------------------------------------------------------------------------

open import DASHI.Core.Prelude

record OrderedOperationPlan (Operation : Set) : Set where
  constructor orderedOperationPlan
  field
    first : Operation
    second : Operation

open OrderedOperationPlan public

data OrderStatus : Set where
  orderRequired : OrderStatus
  orderIndependentUnderConditions : OrderStatus
  orderNotYetEstablished : OrderStatus

record SourceOrderAssignment (Operation : Set) : Set where
  constructor sourceOrderAssignment
  field
    plan : OrderedOperationPlan Operation
    status : OrderStatus

open SourceOrderAssignment public

------------------------------------------------------------------------
-- Optional semantic witness.  This is stronger than a historical/source-level
-- order assignment because it actually exhibits a state on which the two
-- composed operations differ.
------------------------------------------------------------------------

record NonCommutationWitness (State : Set) : Set where
  constructor nonCommutationWitness
  field
    firstOperation : State → State
    secondOperation : State → State
    seed : State
    firstThenSecondDiffers :
      secondOperation (firstOperation seed)
        ≡ firstOperation (secondOperation seed) → ⊥

open NonCommutationWitness public

record OrderedSubstitutionGeometryBoundary : Set where
  constructor orderedSubstitutionGeometryBoundary
  field
    sourceRequiredOrderIsRepresentable : Bool
    sourceRequiredOrderIsRepresentableIsTrue :
      sourceRequiredOrderIsRepresentable ≡ true

    conditionalOrderIndependenceIsRepresentable : Bool
    conditionalOrderIndependenceIsRepresentableIsTrue :
      conditionalOrderIndependenceIsRepresentable ≡ true

    sourceRequiredOrderAlreadyProvesSemanticNonCommutation : Bool
    sourceRequiredOrderAlreadyProvesSemanticNonCommutationIsFalse :
      sourceRequiredOrderAlreadyProvesSemanticNonCommutation ≡ false

    sourceOrderIndependenceWithoutConditionsIsAutomatic : Bool
    sourceOrderIndependenceWithoutConditionsIsAutomaticIsFalse :
      sourceOrderIndependenceWithoutConditionsIsAutomatic ≡ false

canonicalOrderedSubstitutionGeometryBoundary :
  OrderedSubstitutionGeometryBoundary
canonicalOrderedSubstitutionGeometryBoundary =
  orderedSubstitutionGeometryBoundary
    true refl
    true refl
    false refl
    false refl
