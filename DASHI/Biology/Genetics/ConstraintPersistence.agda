module DASHI.Biology.Genetics.ConstraintPersistence where

-- Heredity is defined abstractly as persistence of organisation-generating
-- constraints under reproduction and transformation.  DNA/RNA is one concrete
-- carrier, not the definition of heredity itself.
record HereditaryRewriteSystem : Set₁ where
  field
    Carrier        : Set
    Constraint     : Set
    Transformation : Set
    Environment    : Set

    apply       : Environment → Transformation → Carrier → Carrier
    Satisfies   : Carrier → Constraint → Set
    Replicates  : Carrier → Carrier → Set
    Mutates     : Transformation → Set

record ConstraintPersistenceWitness
  (H : HereditaryRewriteSystem) : Set₁ where
  open HereditaryRewriteSystem H
  field
    parent child : Carrier
    constraint   : Constraint
    environment  : Environment
    transformation : Transformation

    parentSatisfies : Satisfies parent constraint
    reproduction    : Replicates parent child
    childSatisfies  : Satisfies child constraint

record HeritableVariationWitness
  (H : HereditaryRewriteSystem) : Set₁ where
  open HereditaryRewriteSystem H
  field
    ancestor descendant : Carrier
    environment : Environment
    transformation : Transformation
    ancestralConstraint derivedConstraint : Constraint

    mutation : Mutates transformation
    ancestorSatisfies : Satisfies ancestor ancestralConstraint
    descendantSatisfies : Satisfies descendant derivedConstraint

    ConstraintsDiffer : Constraint → Constraint → Set
    variation : ConstraintsDiffer ancestralConstraint derivedConstraint

-- A genetic sequence can realise a hereditary constraint system, but the bridge
-- must include expression, development, and environmental interpretation.
record GeneticCarrierRealisation
  (H : HereditaryRewriteSystem) : Set₁ where
  open HereditaryRewriteSystem H
  field
    Sequence : Set
    ExpressionState : Set
    DevelopmentalContext : Set

    encode      : Sequence → Carrier
    express     : DevelopmentalContext → Sequence → ExpressionState
    Realises    : ExpressionState → Constraint → Set

    sequenceDoesNotEncodeFinalPhenotype : Set
    heredityRequiresConstraintPersistence : Set
