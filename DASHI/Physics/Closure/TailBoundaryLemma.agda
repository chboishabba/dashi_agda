module DASHI.Physics.Closure.TailBoundaryLemma where

open import Agda.Primitive using (Setω)
open import Data.Empty using (⊥)
open import Data.Fin using (Fin; zero; suc)
open import Data.Product using (_×_; _,_; Σ; Σ-syntax)
open import Data.Unit using (⊤; tt)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import DASHI.Physics.Closure.ExecutionAdmissibilityWitness as EAW
open import DASHI.Physics.Closure.ExecutionAdmissibilityCurrentFamilyWitness as EACFW

TailBoundaryConclusion :
  ∀ {FamilyId : Set} →
  EAW.FamilyClassificationWitness FamilyId →
  FamilyId →
  Set
TailBoundaryConclusion witness family =
  EAW.FamilyClassificationWitness.coneOK witness family
  ×
  (EAW.FamilyClassificationWitness.fejerOK witness family
   ×
   (EAW.FamilyClassificationWitness.closestOK witness family
    ×
    ((EAW.FamilyClassificationWitness.mdlExactOK witness family → ⊥)
     × EAW.FamilyClassificationWitness.tailLocalized witness family)))

record TailBoundaryLemma
  (FamilyId : Set)
  (witness : EAW.FamilyClassificationWitness FamilyId) : Setω where
  field
    mdlTailBoundaryImplies :
      ∀ family →
      EAW.FamilyClassificationWitness.familyClass witness family
      ≡ EAW.MDLTailBoundaryFamily →
      TailBoundaryConclusion witness family

open TailBoundaryLemma public

CurrentFamilyId : Set
CurrentFamilyId =
  EAW.SomeFamilyClassificationWitness.FamilyId
    EACFW.currentFamilyClassification

currentFamilyWitness : EAW.FamilyClassificationWitness CurrentFamilyId
currentFamilyWitness =
  EAW.SomeFamilyClassificationWitness.witness
    EACFW.currentFamilyClassification

pattern ttbarFamilyId =
  suc (suc (suc (suc (suc (suc (suc zero))))))

currentTTbarIsMDLTailBoundary :
  EAW.FamilyClassificationWitness.familyClass
    currentFamilyWitness ttbarFamilyId
  ≡ EAW.MDLTailBoundaryFamily
currentTTbarIsMDLTailBoundary = refl

currentTTbarTailBoundaryConclusion :
  TailBoundaryConclusion currentFamilyWitness ttbarFamilyId
currentTTbarTailBoundaryConclusion =
  tt , (tt , (tt , ((λ ()) , tt)))

currentTailBoundaryExample :
  Σ CurrentFamilyId
    (λ family →
      (EAW.FamilyClassificationWitness.familyClass
         currentFamilyWitness family
       ≡ EAW.MDLTailBoundaryFamily)
      × TailBoundaryConclusion currentFamilyWitness family)
currentTailBoundaryExample =
  ttbarFamilyId , (refl , currentTTbarTailBoundaryConclusion)

currentTailBoundaryLemma :
  TailBoundaryLemma CurrentFamilyId currentFamilyWitness
currentTailBoundaryLemma =
  record { mdlTailBoundaryImplies = lemma }
  where
    lemma :
      ∀ family →
      EAW.FamilyClassificationWitness.familyClass
        currentFamilyWitness family
      ≡ EAW.MDLTailBoundaryFamily →
      TailBoundaryConclusion currentFamilyWitness family
    lemma zero ()
    lemma (suc zero) ()
    lemma (suc (suc zero)) ()
    lemma (suc (suc (suc zero))) ()
    lemma (suc (suc (suc (suc zero)))) ()
    lemma (suc (suc (suc (suc (suc zero))))) ()
    lemma (suc (suc (suc (suc (suc (suc zero)))))) ()
    lemma ttbarFamilyId refl = currentTTbarTailBoundaryConclusion
    lemma (suc (suc (suc (suc (suc (suc (suc (suc zero)))))))) ()
