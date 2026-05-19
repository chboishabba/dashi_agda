module DASHI.Physics.Closure.ShiftContractSupportCascadeTrajectory where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (suc; zero)
open import Data.Empty using (⊥)
open import Data.Product using (proj₁)
open import Relation.Binary.PropositionalEquality using (cong)

open import DASHI.Execution.Contract as EC
open import DASHI.Geometry.ShiftLorentzEmergenceInstance as SLEI
open import DASHI.Physics.Closure.ShiftContractAnchoredTriadicFamily as SATF
  using (anchored0)
open import DASHI.Physics.Closure.ShiftContractDenseTriadicFamily as SDTF
  using (dense0; dense2)
open import DASHI.Physics.Closure.ShiftContractMdlLevelCoarseObservable as SCMCO
  using (π-mdl-max)
open import DASHI.Physics.Closure.ShiftContractMdlLevelExplicitStateSearchAudit as ES
  using (oneHot0)
open import DASHI.Physics.Closure.ShiftContractStatePrimeCompatibilityProfileInstance as SCSP
  using (ShiftContractState)

------------------------------------------------------------------------
-- First mixed-scale trajectory on the noncanonical seam.
--
-- Starting from a dense support-width-three seed, the live shift step causes
-- a clean support cascade:
--   width 3 -> width 3 -> width 2 -> width 1
-- while descending through distinct `π-mdl-max` fibres before reaching the
-- one-hot fixed point.

private
  ShiftC : EC.Contract
  ShiftC = SLEI.shiftContract {suc zero} {suc (suc (suc zero))}

  _≢_ : {A : Set} → A → A → Set
  x ≢ y = x ≡ y → ⊥

shiftStep : ShiftContractState → ShiftContractState
shiftStep = EC.Contract.step ShiftC

cascade0 : ShiftContractState
cascade0 = dense2

cascade1 : ShiftContractState
cascade1 = dense0

cascade2 : ShiftContractState
cascade2 = anchored0

cascade3 : ShiftContractState
cascade3 = oneHot0

cascadeStep01 : shiftStep cascade0 ≡ cascade1
cascadeStep01 = refl

cascadeStep12 : shiftStep cascade1 ≡ cascade2
cascadeStep12 = refl

cascadeStep23 : shiftStep cascade2 ≡ cascade3
cascadeStep23 = refl

cascadeStep34 : shiftStep cascade3 ≡ cascade3
cascadeStep34 = refl

cascadeDenseFibre :
  π-mdl-max cascade0 ≡ π-mdl-max cascade1
cascadeDenseFibre = refl

cascadeDenseToAnchored :
  π-mdl-max cascade1
    ≢
  π-mdl-max cascade2
cascadeDenseToAnchored eq with cong proj₁ eq
... | ()

cascadeAnchoredToOneHot :
  π-mdl-max cascade2
    ≢
  π-mdl-max cascade3
cascadeAnchoredToOneHot eq with cong proj₁ eq
... | ()

record ShiftContractSupportCascadeTrajectory : Set₁ where
  field
    level3-start : ShiftContractState
    level3-next : ShiftContractState
    level2-next : ShiftContractState
    level1-next : ShiftContractState
    step01 : shiftStep level3-start ≡ level3-next
    step12 : shiftStep level3-next ≡ level2-next
    step23 : shiftStep level2-next ≡ level1-next
    step34 : shiftStep level1-next ≡ level1-next
    sameDenseFibre :
      π-mdl-max level3-start ≡ π-mdl-max level3-next
    denseToAnchoredExit :
      π-mdl-max level3-next
        ≢
      π-mdl-max level2-next
    anchoredToOneHotExit :
      π-mdl-max level2-next
        ≢
      π-mdl-max level1-next

canonicalShiftContractSupportCascadeTrajectory :
  ShiftContractSupportCascadeTrajectory
canonicalShiftContractSupportCascadeTrajectory =
  record
    { level3-start = cascade0
    ; level3-next = cascade1
    ; level2-next = cascade2
    ; level1-next = cascade3
    ; step01 = cascadeStep01
    ; step12 = cascadeStep12
    ; step23 = cascadeStep23
    ; step34 = cascadeStep34
    ; sameDenseFibre = cascadeDenseFibre
    ; denseToAnchoredExit = cascadeDenseToAnchored
    ; anchoredToOneHotExit = cascadeAnchoredToOneHot
    }

open ShiftContractSupportCascadeTrajectory public
