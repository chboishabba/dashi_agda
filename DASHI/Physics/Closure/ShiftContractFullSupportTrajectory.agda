module DASHI.Physics.Closure.ShiftContractFullSupportTrajectory where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (suc; zero)
open import Data.Empty using (⊥)
open import Data.Product using (proj₁)
open import Data.Vec using (_∷_; [])
open import Relation.Binary.PropositionalEquality using (cong)

open import DASHI.Algebra.Trit using (pos)
open import DASHI.Execution.Contract as EC
open import DASHI.Geometry.ShiftLorentzEmergenceInstance as SLEI
open import DASHI.Physics.Closure.ShiftContractAnchoredTriadicFamily as SATF
  using (anchored0)
open import DASHI.Physics.Closure.ShiftContractDenseTriadicFamily as SDTF
  using (dense0)
open import DASHI.Physics.Closure.ShiftContractMdlLevelCoarseObservable as SCMCO
  using (π-mdl-max)
open import DASHI.Physics.Closure.ShiftContractMdlLevelExplicitStateSearchAudit as ES
  using (oneHot0)
open import DASHI.Physics.Closure.ShiftContractStatePrimeCompatibilityProfileInstance as SCSP
  using (ShiftContractState)

------------------------------------------------------------------------
-- A distinct trajectory source above the current explicit cyclic branch.
--
-- Start from the full-support positive state.  The live shift step then gives
-- a clean support cascade:
--   width 4 -> width 3 -> width 2 -> width 1
-- before reaching the one-hot fixed point.

private
  ShiftC : EC.Contract
  ShiftC = SLEI.shiftContract {suc zero} {suc (suc (suc zero))}

  _≢_ : {A : Set} → A → A → Set
  x ≢ y = x ≡ y → ⊥

shiftStep : ShiftContractState → ShiftContractState
shiftStep = EC.Contract.step ShiftC

fullSupport : ShiftContractState
fullSupport = pos ∷ pos ∷ pos ∷ pos ∷ []

fullStep01 : shiftStep fullSupport ≡ dense0
fullStep01 = refl

fullStep12 : shiftStep dense0 ≡ anchored0
fullStep12 = refl

fullStep23 : shiftStep anchored0 ≡ oneHot0
fullStep23 = refl

fullStep34 : shiftStep oneHot0 ≡ oneHot0
fullStep34 = refl

fullToDenseExit :
  π-mdl-max fullSupport
    ≢
  π-mdl-max dense0
fullToDenseExit eq with cong proj₁ eq
... | ()

denseToAnchoredExit :
  π-mdl-max dense0
    ≢
  π-mdl-max anchored0
denseToAnchoredExit eq with cong proj₁ eq
... | ()

anchoredToOneHotExit :
  π-mdl-max anchored0
    ≢
  π-mdl-max oneHot0
anchoredToOneHotExit eq with cong proj₁ eq
... | ()

record ShiftContractFullSupportTrajectory : Set₁ where
  field
    level4-start : ShiftContractState
    level3-next : ShiftContractState
    level2-next : ShiftContractState
    level1-next : ShiftContractState
    step01 : shiftStep level4-start ≡ level3-next
    step12 : shiftStep level3-next ≡ level2-next
    step23 : shiftStep level2-next ≡ level1-next
    step34 : shiftStep level1-next ≡ level1-next
    exit4to3 :
      π-mdl-max level4-start
        ≢
      π-mdl-max level3-next
    exit3to2 :
      π-mdl-max level3-next
        ≢
      π-mdl-max level2-next
    exit2to1 :
      π-mdl-max level2-next
        ≢
      π-mdl-max level1-next

canonicalShiftContractFullSupportTrajectory :
  ShiftContractFullSupportTrajectory
canonicalShiftContractFullSupportTrajectory =
  record
    { level4-start = fullSupport
    ; level3-next = dense0
    ; level2-next = anchored0
    ; level1-next = oneHot0
    ; step01 = fullStep01
    ; step12 = fullStep12
    ; step23 = fullStep23
    ; step34 = fullStep34
    ; exit4to3 = fullToDenseExit
    ; exit3to2 = denseToAnchoredExit
    ; exit2to1 = anchoredToOneHotExit
    }

open ShiftContractFullSupportTrajectory public
