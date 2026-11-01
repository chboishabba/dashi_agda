module DASHI.Cognition.IdentityVacuumClosure where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using ([]; _∷_)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_)
open import Data.Empty using (⊥)
open import Data.Nat using (_≤_; z≤n; s≤s)

import DASHI.Cognition.CognitiveVacuumClassBoundary as Vacuum
import DASHI.Cognition.DashiCognitiveSystem as Cognitive

open Vacuum.MultiscaleDefectModel
open Vacuum.VacuumClass

------------------------------------------------------------------------
-- Elementary additive/order facts used to derive global minimality from a
-- neutral floor plus non-negative residual excess.
------------------------------------------------------------------------

leftAddLower : (floor excess : Nat) → floor ≤ floor + excess
leftAddLower zero excess = z≤n
leftAddLower (suc floor) excess = s≤s (leftAddLower floor excess)

rightAddIdentity : (value : Nat) → value + 0 ≡ value
rightAddIdentity zero = refl
rightAddIdentity (suc value) rewrite rightAddIdentity value = refl

------------------------------------------------------------------------
-- Identity-class vacuum principle.
--
-- An arbitrary stable class still need not be a vacuum.  The stronger witness
-- below singles out a representative that is fixed by coarse-graining and
-- involution and lies at a certified global defect floor.
------------------------------------------------------------------------

record IdentityClassAtDefectFloor
    (system : Cognitive.DASHICognitiveSystem)
    (model : Vacuum.MultiscaleDefectModel system)
    (representative : Cognitive.Hidden system) : Set where
  field
    stableClass : Cognitive.StableObservedClass system representative
    coarseIdentity :
      ∀ scale → Cognitive.coarseGrain system scale representative
        ≡ representative
    involutionIdentity :
      Cognitive.involution system representative
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
-- Stronger analytic law: identity neutrality supplies a decomposition
--
--   totalDefect(candidate) = neutralFloor + residualExcess(candidate)
--
-- with residualExcess(identity)=0.  Since residualExcess is a Nat, the global
-- lower bound is derived rather than separately assumed.
------------------------------------------------------------------------

record IdentityNeutralDefectLaw
    (system : Cognitive.DASHICognitiveSystem)
    (model : Vacuum.MultiscaleDefectModel system)
    (representative : Cognitive.Hidden system) : Set where
  field
    identityStableClass :
      Cognitive.StableObservedClass system representative
    identityUnderCoarseGraining :
      ∀ scale → Cognitive.coarseGrain system scale representative
        ≡ representative
    identityUnderInvolution :
      Cognitive.involution system representative
        ≡ representative
    neutralFloor : Nat
    residualExcess : Cognitive.Hidden system → Nat
    defectDecomposes :
      ∀ candidate →
      Vacuum.totalDefect model candidate
        ≡ neutralFloor + residualExcess candidate
    identityHasNoExcess : residualExcess representative ≡ 0

open IdentityNeutralDefectLaw public

neutralDefectLawImpliesFloorWitness :
  ∀ {system model representative} →
  IdentityNeutralDefectLaw system model representative →
  IdentityClassAtDefectFloor system model representative
neutralDefectLawImpliesFloorWitness
  {system} {model} {representative} law = record
  { stableClass = identityStableClass law
  ; coarseIdentity = identityUnderCoarseGraining law
  ; involutionIdentity = identityUnderInvolution law
  ; defectFloor = neutralFloor law
  ; representativeAtFloor = representativeIsAtFloor
  ; floorIsGlobalLowerBound = lowerBound
  }
  where
  representativeIsAtFloor :
    Vacuum.totalDefect model representative ≡ neutralFloor law
  representativeIsAtFloor
    rewrite defectDecomposes law representative
          | identityHasNoExcess law
          | rightAddIdentity (neutralFloor law) = refl

  lowerBound :
    ∀ candidate →
    neutralFloor law ≤ Vacuum.totalDefect model candidate
  lowerBound candidate rewrite defectDecomposes law candidate =
    leftAddLower (neutralFloor law) (residualExcess law candidate)

identityNeutralityImpliesVacuum :
  ∀ {system model representative} →
  IdentityNeutralDefectLaw system model representative →
  Vacuum.VacuumClass system model representative
identityNeutralityImpliesVacuum law =
  identityClassImpliesVacuum (neutralDefectLawImpliesFloorWitness law)

------------------------------------------------------------------------
-- Existing zero-floor fixture, now derived from the neutral decomposition.
------------------------------------------------------------------------

booleanIdentityLaw :
  IdentityNeutralDefectLaw
    Vacuum.booleanCognitiveSystem
    Vacuum.booleanDefectModel
    true
booleanIdentityLaw = record
  { identityStableClass = Vacuum.trueClassIsStable
  ; identityUnderCoarseGraining = λ scale → refl
  ; identityUnderInvolution = refl
  ; neutralFloor = 0
  ; residualExcess = λ where
      false → 1
      true → 0
  ; defectDecomposes = λ where
      false → refl
      true → refl
  ; identityHasNoExcess = refl
  }

booleanIdentityWitness :
  IdentityClassAtDefectFloor
    Vacuum.booleanCognitiveSystem
    Vacuum.booleanDefectModel
    true
booleanIdentityWitness =
  neutralDefectLawImpliesFloorWitness booleanIdentityLaw

booleanIdentityIsVacuum :
  Vacuum.VacuumClass
    Vacuum.booleanCognitiveSystem
    Vacuum.booleanDefectModel
    true
booleanIdentityIsVacuum = identityNeutralityImpliesVacuum booleanIdentityLaw

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

shiftedIdentityLaw :
  IdentityNeutralDefectLaw
    Vacuum.booleanCognitiveSystem
    shiftedBooleanDefectModel
    true
shiftedIdentityLaw = record
  { identityStableClass = Vacuum.trueClassIsStable
  ; identityUnderCoarseGraining = λ scale → refl
  ; identityUnderInvolution = refl
  ; neutralFloor = 2
  ; residualExcess = λ where
      false → 1
      true → 0
  ; defectDecomposes = λ where
      false → refl
      true → refl
  ; identityHasNoExcess = refl
  }

shiftedIdentityWitness :
  IdentityClassAtDefectFloor
    Vacuum.booleanCognitiveSystem
    shiftedBooleanDefectModel
    true
shiftedIdentityWitness =
  neutralDefectLawImpliesFloorWitness shiftedIdentityLaw

nonzeroResidualIdentityIsVacuum :
  Vacuum.VacuumClass
    Vacuum.booleanCognitiveSystem
    shiftedBooleanDefectModel
    true
nonzeroResidualIdentityIsVacuum =
  identityNeutralityImpliesVacuum shiftedIdentityLaw

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
