module DASHI.Physics.Closure.ShiftContractGeneratorFourthStepBoundary where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Empty using (⊥)
open import Data.Product using (proj₁)
open import Relation.Binary.PropositionalEquality using (cong)

open import DASHI.Physics.Closure.ShiftContractAnchoredTrajectoryFamily as SATJ
  using
    ( trajectoryGen
    ; trajectoryStep2Exit
    ; trajectoryExitFibre
    ; shiftStep
    )
open import DASHI.Physics.Closure.ShiftContractAnchoredTriadicFamily as SATF
  using (anchored0)
open import DASHI.Physics.Closure.ShiftContractBalancedComposedFamily as SBCF
  using
    ( balancedComposedGen
    ; balancedComposed≡x2
    )
open import DASHI.Physics.Closure.ShiftContractComposedFamily as SCF
  using
    ( composedGen
    ; composed≡dense2
    )
open import DASHI.Physics.Closure.ShiftContractDenseTriadicFamily as SDTF
  using
    ( dense0
    ; dense2
    ; denseGen
    )
open import DASHI.Physics.Closure.ShiftContractMdlLevelExplicitStateSearchAudit as ES
  using (oneHot0; oneHot1; oneHot2)
open import DASHI.Physics.Closure.ShiftContractMdlLevelCoarseObservable as SCMCO
  using (π-mdl-max)
open import DASHI.Physics.Closure.ShiftContractParametricTrajectoryCompositionFamily as SPTCF
  using
    ( GeneratorClass
    ; anchoredTrajectory
    ; balancedComposed
    ; balancedCycle
    ; denseComposed
    ; explicitWidth1
    ; explicitWidth2
    ; explicitWidth3
    )
open import DASHI.Physics.Closure.ShiftContractStatePrimeCompatibilityProfileInstance as SCSP
  using (ShiftContractState)
open import DASHI.Physics.Closure.ShiftContractSupportCascadeTrajectory as SSCT
  using
    ( cascadeStep01
    ; cascadeDenseFibre
    )
open import DASHI.Physics.Closure.ShiftContractTriadic3CycleInstance as ST3
  using (cycleGen)
open import DASHI.Physics.Closure.ShiftContractTriadicFamily as STF
  using (i0; i1; i2; triadic-π-mdl-max-constant)

------------------------------------------------------------------------
-- First reusable fourth-step boundary above the normalized generator surface.
--
-- The current generator-class interface packages successful same-carrier
-- 3-state prefixes.  This module adds the next dynamic layer without
-- pretending every class already has a certified live boundary.  For now we
-- have two certified shapes:
-- - anchored explicit/trajectory and balanced explicit/composed cycles exit
--   the fibre at the fourth step;
-- - explicit width-one/three and dense explicit/composed cycles stay in the
--   same fibre for one more step.

private
  _≢_ : {A : Set} → A → A → Set
  x ≢ y = x ≡ y → ⊥

record CertifiedFourthStepExit : Set₁ where
  field
    familyClass : GeneratorClass
    thirdState : ShiftContractState
    nextState : ShiftContractState
    liveStepFromThird :
      shiftStep thirdState ≡ nextState
    leavesFibreAtFourth :
      π-mdl-max thirdState
        ≢
      π-mdl-max nextState

anchoredTrajectoryFourthStepBoundary :
  CertifiedFourthStepExit
anchoredTrajectoryFourthStepBoundary =
  record
    { familyClass = anchoredTrajectory
    ; thirdState = trajectoryGen i2
    ; nextState = oneHot0
    ; liveStepFromThird = trajectoryStep2Exit
    ; leavesFibreAtFourth = trajectoryExitFibre
    }

anchoredExplicitFourthStepBoundary :
  CertifiedFourthStepExit
anchoredExplicitFourthStepBoundary =
  record
    { familyClass = explicitWidth2
    ; thirdState = anchored0
    ; nextState = oneHot0
    ; liveStepFromThird = refl
    ; leavesFibreAtFourth = trajectoryExitFibre
    }

record CertifiedFourthStepStay : Set₁ where
  field
    familyClass : GeneratorClass
    thirdState : ShiftContractState
    nextState : ShiftContractState
    liveStepFromThird :
      shiftStep thirdState ≡ nextState
    staysInFibreAtFourth :
      π-mdl-max thirdState
        ≡
      π-mdl-max nextState

oneHotExplicitFourthStepBoundary :
  CertifiedFourthStepStay
oneHotExplicitFourthStepBoundary =
  record
    { familyClass = explicitWidth1
    ; thirdState = oneHot2
    ; nextState = oneHot1
    ; liveStepFromThird = refl
    ; staysInFibreAtFourth = triadic-π-mdl-max-constant i2 i1
    }

record CertifiedFourthStepExitOnCycle : Set₁ where
  field
    familyClass : GeneratorClass
    thirdState : ShiftContractState
    nextState : ShiftContractState
    liveStepFromThird :
      shiftStep thirdState ≡ nextState
    leavesFibreAtFourth :
      π-mdl-max thirdState
        ≢
      π-mdl-max nextState

balancedCycleExitFibre :
  π-mdl-max (cycleGen i2)
    ≢
  π-mdl-max anchored0
balancedCycleExitFibre eq with cong proj₁ eq
... | ()

balancedCycleFourthStepBoundary :
  CertifiedFourthStepExitOnCycle
balancedCycleFourthStepBoundary =
  record
    { familyClass = balancedCycle
    ; thirdState = cycleGen i2
    ; nextState = anchored0
    ; liveStepFromThird = refl
    ; leavesFibreAtFourth = balancedCycleExitFibre
    }

balancedComposedExitFibre :
  π-mdl-max (balancedComposedGen i2)
    ≢
  π-mdl-max anchored0
balancedComposedExitFibre eq rewrite balancedComposed≡x2 =
  balancedCycleExitFibre eq

balancedComposedFourthStepBoundary :
  CertifiedFourthStepExitOnCycle
balancedComposedFourthStepBoundary =
  record
    { familyClass = balancedComposed
    ; thirdState = balancedComposedGen i2
    ; nextState = anchored0
    ; liveStepFromThird = refl
    ; leavesFibreAtFourth = balancedComposedExitFibre
    }

denseExplicitFourthStepBoundary :
  CertifiedFourthStepStay
denseExplicitFourthStepBoundary =
  record
    { familyClass = explicitWidth3
    ; thirdState = denseGen i2
    ; nextState = dense0
    ; liveStepFromThird = cascadeStep01
    ; staysInFibreAtFourth = cascadeDenseFibre
    }

denseComposedStepToDense0 :
  shiftStep (composedGen i2) ≡ dense0
denseComposedStepToDense0 rewrite composed≡dense2 = cascadeStep01

denseComposedStaysInFibre :
  π-mdl-max (composedGen i2) ≡ π-mdl-max dense0
denseComposedStaysInFibre rewrite composed≡dense2 = cascadeDenseFibre

denseComposedFourthStepBoundary :
  CertifiedFourthStepStay
denseComposedFourthStepBoundary =
  record
    { familyClass = denseComposed
    ; thirdState = composedGen i2
    ; nextState = dense0
    ; liveStepFromThird = denseComposedStepToDense0
    ; staysInFibreAtFourth = denseComposedStaysInFibre
    }

open CertifiedFourthStepExit public
open CertifiedFourthStepStay public
open CertifiedFourthStepExitOnCycle public
