module DASHI.Physics.Closure.ShiftContractTailPatternTrajectoryObstruction where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (suc; zero)
open import Data.Empty using (⊥)
open import Data.Product using (proj₁)
open import Relation.Binary.PropositionalEquality using (cong)

open import DASHI.Execution.Contract as EC
open import DASHI.Geometry.ShiftLorentzEmergenceInstance as SLEI
open import DASHI.Physics.Closure.ShiftContractMdlLevelCoarseObservable as SCMCO
  using (π-mdl-max)
open import DASHI.Physics.Closure.ShiftContractMdlLevelExplicitStateSearchAudit as ES
  using (tailAltSigns; tailBlockSigns; tailCrossSigns)
open import DASHI.Physics.Closure.ShiftContractStatePrimeCompatibilityProfileInstance as SCSP
  using (ShiftContractState)

private
  ShiftC : EC.Contract
  ShiftC = SLEI.shiftContract {suc zero} {suc (suc (suc zero))}

  _≢_ : {A : Set} → A → A → Set
  x ≢ y = x ≡ y → ⊥

shiftStep : ShiftContractState → ShiftContractState
shiftStep = EC.Contract.step ShiftC

tailAltExitsFibre :
  π-mdl-max tailAltSigns
    ≢
  π-mdl-max (shiftStep tailAltSigns)
tailAltExitsFibre eq with cong proj₁ eq
... | ()

tailBlockExitsFibre :
  π-mdl-max tailBlockSigns
    ≢
  π-mdl-max (shiftStep tailBlockSigns)
tailBlockExitsFibre eq with cong proj₁ eq
... | ()

tailCrossExitsFibre :
  π-mdl-max tailCrossSigns
    ≢
  π-mdl-max (shiftStep tailCrossSigns)
tailCrossExitsFibre eq with cong proj₁ eq
... | ()

record ShiftContractTailPatternTrajectoryObstruction : Set₁ where
  field
    alt-exits-fibre :
      π-mdl-max tailAltSigns
        ≢
      π-mdl-max (shiftStep tailAltSigns)
    block-exits-fibre :
      π-mdl-max tailBlockSigns
        ≢
      π-mdl-max (shiftStep tailBlockSigns)
    cross-exits-fibre :
      π-mdl-max tailCrossSigns
        ≢
      π-mdl-max (shiftStep tailCrossSigns)

canonicalShiftContractTailPatternTrajectoryObstruction :
  ShiftContractTailPatternTrajectoryObstruction
canonicalShiftContractTailPatternTrajectoryObstruction =
  record
    { alt-exits-fibre = tailAltExitsFibre
    ; block-exits-fibre = tailBlockExitsFibre
    ; cross-exits-fibre = tailCrossExitsFibre
    }

open ShiftContractTailPatternTrajectoryObstruction public
