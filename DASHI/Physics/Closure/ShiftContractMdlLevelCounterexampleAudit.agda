module DASHI.Physics.Closure.ShiftContractMdlLevelCounterexampleAudit where

open import Agda.Builtin.Equality using (_≡_)
open import Data.Empty using (⊥)

open import DASHI.Physics.Closure.ShiftContractMdlLevelCoarseObservable as SCMCO
  using
    ( MdlLevelCoarseObservable
    ; π-mdl-max
    ; π-mdl-max-refines-π-max
    ; π-mdl-max-separates-obstruction-pair
    ; canonicalShiftContractMdlLevelCoarseObservablePackage
    ; ShiftContractMdlLevelCoarseObservablePackage
    )
open import DASHI.Physics.Closure.ShiftContractNoncanonicalP2ControlObstruction as OB
  using (coarseCounterexampleLeft; coarseCounterexampleRight)
open import DASHI.Physics.Closure.ShiftContractStatePrimeCompatibilityProfileInstance as SCSP
  using (ShiftContractState)

------------------------------------------------------------------------
-- Audit of the old coarse obstruction pair against the stronger
-- mdlLevel × π-max surface.
--
-- The bounded result is negative for the old blocker role: the obstruction
-- pair is already separated by the strengthened package, so it is no longer
-- the same obstruction on this surface.  This is still not a positive
-- p2-style control theorem on the full shift-contract carrier.

private
  _≢_ : {A : Set} → A → A → Set
  x ≢ y = x ≡ y → ⊥

oldCoarsePairSeparatedByMdlLevelSurface :
  π-mdl-max OB.coarseCounterexampleLeft
    ≢
  π-mdl-max OB.coarseCounterexampleRight
oldCoarsePairSeparatedByMdlLevelSurface =
  π-mdl-max-separates-obstruction-pair

record ShiftContractMdlLevelCounterexampleAudit : Set₁ where
  field
    surface : ShiftContractMdlLevelCoarseObservablePackage
    oldPair-separated :
      ShiftContractMdlLevelCoarseObservablePackage.projection surface
        OB.coarseCounterexampleLeft
        ≢
      ShiftContractMdlLevelCoarseObservablePackage.projection surface
        OB.coarseCounterexampleRight

canonicalShiftContractMdlLevelCounterexampleAudit :
  ShiftContractMdlLevelCounterexampleAudit
canonicalShiftContractMdlLevelCounterexampleAudit =
  record
    { surface = canonicalShiftContractMdlLevelCoarseObservablePackage
    ; oldPair-separated = oldCoarsePairSeparatedByMdlLevelSurface
    }

open ShiftContractMdlLevelCounterexampleAudit public
