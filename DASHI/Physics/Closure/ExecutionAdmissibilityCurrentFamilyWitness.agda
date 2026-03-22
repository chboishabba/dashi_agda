module DASHI.Physics.Closure.ExecutionAdmissibilityCurrentFamilyWitness where

open import Data.Unit using (⊤; tt)
open import Data.Empty using (⊥)
open import Data.Fin using (Fin; zero; suc)
open import Agda.Builtin.Nat using (Nat)

open import DASHI.Physics.Closure.ExecutionAdmissibilityWitness as EAW

familyCount : Nat
familyCount = 9

TraceFamilyId : Set
TraceFamilyId = Fin familyCount

familyClassFn : TraceFamilyId → EAW.FamilyClass
familyClassFn zero = EAW.InteriorFamily
familyClassFn (suc zero) = EAW.InteriorFamily
familyClassFn (suc (suc zero)) = EAW.InteriorFamily
familyClassFn (suc (suc (suc zero))) = EAW.InteriorFamily
familyClassFn (suc (suc (suc (suc zero)))) = EAW.InteriorFamily
familyClassFn (suc (suc (suc (suc (suc zero))))) = EAW.InteriorFamily
familyClassFn (suc (suc (suc (suc (suc (suc zero)))))) = EAW.ArrowLadderFamily
familyClassFn (suc (suc (suc (suc (suc (suc (suc zero))))))) = EAW.MDLTailBoundaryFamily
familyClassFn (suc (suc (suc (suc (suc (suc (suc (suc zero)))))))) = EAW.SingleArrowBreakFamily

coneOKFn : TraceFamilyId → Set
coneOKFn zero = ⊤
coneOKFn (suc zero) = ⊤
coneOKFn (suc (suc zero)) = ⊤
coneOKFn (suc (suc (suc zero))) = ⊤
coneOKFn (suc (suc (suc (suc zero)))) = ⊤
coneOKFn (suc (suc (suc (suc (suc zero))))) = ⊤
coneOKFn (suc (suc (suc (suc (suc (suc zero)))))) = ⊤
coneOKFn (suc (suc (suc (suc (suc (suc (suc zero))))))) = ⊤
coneOKFn (suc (suc (suc (suc (suc (suc (suc (suc zero)))))))) = ⊤

fejerOKFn : TraceFamilyId → Set
fejerOKFn zero = ⊤
fejerOKFn (suc zero) = ⊤
fejerOKFn (suc (suc zero)) = ⊤
fejerOKFn (suc (suc (suc zero))) = ⊤
fejerOKFn (suc (suc (suc (suc zero)))) = ⊤
fejerOKFn (suc (suc (suc (suc (suc zero))))) = ⊤
fejerOKFn (suc (suc (suc (suc (suc (suc zero)))))) = ⊤
fejerOKFn (suc (suc (suc (suc (suc (suc (suc zero))))))) = ⊤
fejerOKFn (suc (suc (suc (suc (suc (suc (suc (suc zero)))))))) = ⊤

closestOKFn : TraceFamilyId → Set
closestOKFn zero = ⊤
closestOKFn (suc zero) = ⊤
closestOKFn (suc (suc zero)) = ⊤
closestOKFn (suc (suc (suc zero))) = ⊤
closestOKFn (suc (suc (suc (suc zero)))) = ⊤
closestOKFn (suc (suc (suc (suc (suc zero))))) = ⊤
closestOKFn (suc (suc (suc (suc (suc (suc zero)))))) = ⊤
closestOKFn (suc (suc (suc (suc (suc (suc (suc zero))))))) = ⊤
closestOKFn (suc (suc (suc (suc (suc (suc (suc (suc zero)))))))) = ⊤

mdlExactOKFn : TraceFamilyId → Set
mdlExactOKFn zero = ⊤
mdlExactOKFn (suc zero) = ⊤
mdlExactOKFn (suc (suc zero)) = ⊤
mdlExactOKFn (suc (suc (suc zero))) = ⊤
mdlExactOKFn (suc (suc (suc (suc zero)))) = ⊤
mdlExactOKFn (suc (suc (suc (suc (suc zero))))) = ⊤
mdlExactOKFn (suc (suc (suc (suc (suc (suc zero)))))) = ⊥
mdlExactOKFn (suc (suc (suc (suc (suc (suc (suc zero))))))) = ⊥
mdlExactOKFn (suc (suc (suc (suc (suc (suc (suc (suc zero)))))))) = ⊥

tailLocalizedFn : TraceFamilyId → Set
tailLocalizedFn zero = ⊥
tailLocalizedFn (suc zero) = ⊥
tailLocalizedFn (suc (suc zero)) = ⊥
tailLocalizedFn (suc (suc (suc zero))) = ⊥
tailLocalizedFn (suc (suc (suc (suc zero)))) = ⊥
tailLocalizedFn (suc (suc (suc (suc (suc zero))))) = ⊥
tailLocalizedFn (suc (suc (suc (suc (suc (suc zero)))))) = ⊤
tailLocalizedFn (suc (suc (suc (suc (suc (suc (suc zero))))))) = ⊤
tailLocalizedFn (suc (suc (suc (suc (suc (suc (suc (suc zero)))))))) = ⊤

currentFamilyClassification : EAW.SomeFamilyClassificationWitness
currentFamilyClassification =
  record
    { FamilyId = TraceFamilyId
    ; witness =
        record
          { familyClass = familyClassFn
          ; coneOK = coneOKFn
          ; fejerOK = fejerOKFn
          ; closestOK = closestOKFn
          ; mdlExactOK = mdlExactOKFn
          ; tailLocalized = tailLocalizedFn
          }
    }
