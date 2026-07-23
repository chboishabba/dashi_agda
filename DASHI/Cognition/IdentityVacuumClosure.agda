module DASHI.Cognition.IdentityVacuumClosure where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using ([]; _∷_)
open import Agda.Builtin.Nat using (Nat)
open import Data.Empty using (⊥)
open import Data.Nat using (_≤_; z≤n; s≤s)

import DASHI.Cognition.CognitiveVacuumClassBoundary as Vacuum
import DASHI.Cognition.DashiCognitiveSystem as Cognitive

------------------------------------------------------------------------
-- Identity-class vacuum principle.
--
-- An arbitrary stable class still need not be a vacuum.  The stronger witness
-- below singles out a representative that is fixed by coarse-graining and
-- involution and lies at a certified global defect floor.  From those laws the
-- existing VacuumClass follows constructively.
--
-- The floor is explicit and may be non-zero: categorical neutrality means
-- "adds no further admissibility defect", not necessarily zero measured energy.
------------------------------------------------------------------------

record IdentityClassAtDefectFloor
    (system : Cognitive.DASHICognitiveSystem)
    (model : Vacuum.MultiscaleDefectModel system)
    (representative : Cognitive.Hidden system) : Set where
  field
    stableClass : Cognitive.StableObservedClass system representative
    coarseIdentity :
      ∀ scale → Cognitive.DASHICognitiveSystem.coarseGrain system scale representative
        ≡ representative
    involutionIdentity :
      Cognitive.DASHICognitiveSystem.involution system representative
        ≡ representative
    defectFloor : Nat
    representativeAtFloor :
      Vacuum.totalDefect model representative ≡ defectFloor
    floorIsGlobalLowerBound :
      ∀ candidate → defectFloor ≤ Vacuum.totalDefect model candidate

open IdentityClassAtDefectFloor public

identityClassImpliesVacuum :
  ∀ {system model representative} →
  IdentityClassAtDefectFloor system model representative →
  Vacuum.VacuumClass system model representative
identityClassImpliesVacuum
  {system} {model} {representative} witness = record
  { classStable = stableClass witness
  ; globallyMinimal = λ candidate → minimal candidate
  }
  where
  minimal : ∀ candidate →
    Vacuum.totalDefect model representative ≤
    Vacuum.totalDefect model candidate
  minimal candidate rewrite representativeAtFloor witness =
    floorIsGlobalLowerBound witness candidate

------------------------------------------------------------------------
-- Existing zero-floor fixture.
------------------------------------------------------------------------

booleanIdentityWitness :
  IdentityClassAtDefectFloor
    Vacuum.booleanCognitiveSystem
    Vacuum.booleanDefectModel
    true
booleanIdentityWitness = record
  { stableClass = Vacuum.trueClassIsStable
  ; coarseIdentity = λ scale → refl
  ; involutionIdentity = refl
  ; defectFloor = 0
  ; representativeAtFloor = Vacuum.trueDefectIsZero
  ; floorIsGlobalLowerBound = λ candidate → z≤n
  }

booleanIdentityIsVacuum :
  Vacuum.VacuumClass
    Vacuum.booleanCognitiveSystem
    Vacuum.booleanDefectModel
    true
booleanIdentityIsVacuum = identityClassImpliesVacuum booleanIdentityWitness

------------------------------------------------------------------------
-- Non-zero floor fixture: the identity representative is still the unique
-- lower-defect class even though its measured residual is two rather than zero.
------------------------------------------------------------------------

shiftedBooleanDefectModel :
  Vacuum.MultiscaleDefectModel Vacuum.booleanCognitiveSystem
shiftedBooleanDefectModel = record
  { scales = 0 ∷ []
  ; weight = λ _ → 1
  ; defect = λ _ hidden → shifted hidden
  }
  where
  shifted : Bool → Nat
  shifted false = 3
  shifted true = 2

shiftedTrueDefectIsTwo :
  Vacuum.totalDefect shiftedBooleanDefectModel true ≡ 2
shiftedTrueDefectIsTwo = refl

shiftedFalseDefectIsThree :
  Vacuum.totalDefect shiftedBooleanDefectModel false ≡ 3
shiftedFalseDefectIsThree = refl

shiftedIdentityWitness :
  IdentityClassAtDefectFloor
    Vacuum.booleanCognitiveSystem
    shiftedBooleanDefectModel
    true
shiftedIdentityWitness = record
  { stableClass = Vacuum.trueClassIsStable
  ; coarseIdentity = λ scale → refl
  ; involutionIdentity = refl
  ; defectFloor = 2
  ; representativeAtFloor = shiftedTrueDefectIsTwo
  ; floorIsGlobalLowerBound = λ where
      false → s≤s (s≤s z≤n)
      true → s≤s (s≤s z≤n)
  }

nonzeroResidualIdentityIsVacuum :
  Vacuum.VacuumClass
    Vacuum.booleanCognitiveSystem
    shiftedBooleanDefectModel
    true
nonzeroResidualIdentityIsVacuum =
  identityClassImpliesVacuum shiftedIdentityWitness

------------------------------------------------------------------------
-- Correct implication surface.
------------------------------------------------------------------------

stableAloneStillInsufficient :
  Vacuum.VacuumClass
    Vacuum.booleanCognitiveSystem
    Vacuum.booleanDefectModel
    false →
  ⊥
stableAloneStillInsufficient = Vacuum.falseStableClassIsNotVacuum
