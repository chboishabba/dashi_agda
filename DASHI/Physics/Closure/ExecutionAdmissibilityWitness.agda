module DASHI.Physics.Closure.ExecutionAdmissibilityWitness where

open import Agda.Primitive using (Setω)
open import Data.Empty using (⊥)
open import Data.Sum using (_⊎_)
open import Relation.Binary.PropositionalEquality using (_≡_)

data StepClass : Set where
  Interior : StepClass
  ArrowBoundary : StepClass
  StructuralBoundary : StepClass
  Outside : StepClass

data FamilyClass : Set where
  InteriorFamily : FamilyClass
  ArrowLadderFamily : FamilyClass
  SingleArrowBreakFamily : FamilyClass
  MDLTailBoundaryFamily : FamilyClass

record ExecutionAdmissibilityWitness (StepId : Set) : Setω where
  field
    stepClass : StepId → StepClass
    coneOK : StepId → Set
    arrowOK : StepId → Set
    mdlOK : StepId → Set
    basinOK : StepId → Set
    eigenOK : StepId → Set
    interiorOrBoundary :
      ∀ step →
      stepClass step ≡ Interior ⊎ stepClass step ≡ ArrowBoundary
    noStructuralEscape :
      ∀ step →
      stepClass step ≡ StructuralBoundary ⊎ stepClass step ≡ Outside →
      ⊥

open ExecutionAdmissibilityWitness public

record FamilyClassificationWitness (FamilyId : Set) : Setω where
  field
    familyClass : FamilyId → FamilyClass
    coneOK : FamilyId → Set
    fejerOK : FamilyId → Set
    closestOK : FamilyId → Set
    mdlExactOK : FamilyId → Set
    tailLocalized : FamilyId → Set

open FamilyClassificationWitness public

record SomeExecutionAdmissibilityWitness : Setω where
  field
    StepId : Set
    witness : ExecutionAdmissibilityWitness StepId

open SomeExecutionAdmissibilityWitness public

record SomeFamilyClassificationWitness : Setω where
  field
    FamilyId : Set
    witness : FamilyClassificationWitness FamilyId

open SomeFamilyClassificationWitness public
