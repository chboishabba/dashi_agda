module DASHI.Biology.IIT4FiniteRelationExact where

open import DASHI.Core.Prelude

import DASHI.Biology.IIT4FiniteCausalStructureExact as IIT4
import DASHI.Biology.IIT4FiniteDistinctionExact as Distinction

------------------------------------------------------------------------
-- IIT-4 FINITE RELATION SURFACE
------------------------------------------------------------------------

record RelationFace
    (system : IIT4.FiniteCausalSystem)
    (Score : Set) : Set₁ where
  constructor relationFace
  field
    faceRelata : List (Distinction.FiniteDistinction system Score)
    overlapPurview : IIT4.Purview system
    overlapState : IIT4.StateOf system
    congruentOverlapReceipt : String
    jointOverlapSize : Nat

open RelationFace public

record FiniteRelation
    (system : IIT4.FiniteCausalSystem)
    (Score : Set) : Set₁ where
  constructor finiteRelation
  field
    structuralRelation : IIT4.CausalRelation system
    relationRelata : List (Distinction.FiniteDistinction system Score)
    faces : List (RelationFace system Score)
    relationPhi : Score
    weakestDensityReceipt : String
    relationPhiReceipt : String
    positiveRelationReceipt : String

open FiniteRelation public

record RelationSearchReceipt
    (system : IIT4.FiniteCausalSystem)
    (Score : Set) : Set₁ where
  constructor relationSearchReceipt
  field
    nonemptyRelataSubsetsEnumerated : Bool
    congruentFacesEnumerated : Bool
    selfRelationsPermitted : Bool
    positiveRelations : List (FiniteRelation system Score)
    searchReceipt : String

open RelationSearchReceipt public

record IIT4RelationBoundary : Set where
  constructor iit4RelationBoundary
  field
    relationRequiresCongruentPurviewOverlap : Bool
    selfRelationMayExist : Bool
    relationPhiUsesWeakestRelatumDensity : Bool
    relationPhiScalesWithJointOverlap : Bool
    relationPhiEqualsDistinctionPhiByDefinition : Bool
    relationPhiEqualsSystemPhiByDefinition : Bool
    everyNonemptyRelataSubsetAutomaticallyFormsRelation : Bool

open IIT4RelationBoundary public

canonicalIIT4RelationBoundary : IIT4RelationBoundary
canonicalIIT4RelationBoundary =
  iit4RelationBoundary true true true true false false false

relationPhiNotDistinctionPhi :
  relationPhiEqualsDistinctionPhiByDefinition canonicalIIT4RelationBoundary ≡ false
relationPhiNotDistinctionPhi = refl

relationNeedsCongruentOverlap :
  everyNonemptyRelataSubsetAutomaticallyFormsRelation
    canonicalIIT4RelationBoundary ≡ false
relationNeedsCongruentOverlap = refl
