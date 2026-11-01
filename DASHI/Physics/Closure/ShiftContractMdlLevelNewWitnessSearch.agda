module DASHI.Physics.Closure.ShiftContractMdlLevelNewWitnessSearch where

open import Agda.Builtin.Equality using (_≡_)
open import Data.Empty using (⊥)

open import DASHI.Physics.Closure.ShiftContractMdlLevelCounterexampleAudit as AUD
  using
    ( ShiftContractMdlLevelCounterexampleAudit
    ; canonicalShiftContractMdlLevelCounterexampleAudit
    ; oldCoarsePairSeparatedByMdlLevelSurface
    )
open import DASHI.Physics.Closure.ShiftContractMdlLevelCoarseObservable as SCMCO
  using
    ( MdlLevelCoarseObservable
    ; ShiftContractMdlLevelCoarseObservablePackage
    ; canonicalShiftContractMdlLevelCoarseObservablePackage
    ; π-mdl-max
    )
open import DASHI.Physics.Closure.ShiftContractNoncanonicalP2ControlObstruction as OB
  using (coarseCounterexampleLeft; coarseCounterexampleRight)
open import DASHI.Physics.Closure.ShiftContractStatePrimeCompatibilityProfileInstance as SCSP
  using (ShiftContractState)

------------------------------------------------------------------------
-- Bounded witness search on the stronger `mdlLevel × π-max` surface.
--
-- The retired old coarse counterexample pair is not a witness on this
-- surface anymore: it is already separated by the strengthening.  Within the
-- small explicit `ShiftContractState` examples already present in-repo, no
-- sharper witness pair is recovered here, so the clean search result is the
-- negative one.

private
  _≢_ : {A : Set} → A → A → Set
  x ≢ y = x ≡ y → ⊥

retiredOldPairRejected :
  π-mdl-max OB.coarseCounterexampleLeft
    ≢
  π-mdl-max OB.coarseCounterexampleRight
retiredOldPairRejected = oldCoarsePairSeparatedByMdlLevelSurface

data NewWitnessSearchOutcome : Set where
  noBetterSmallWitnessFound : NewWitnessSearchOutcome

record ShiftContractMdlLevelNewWitnessSearch : Set₁ where
  field
    surface : ShiftContractMdlLevelCoarseObservablePackage
    retiredPairRejected :
      ShiftContractMdlLevelCoarseObservablePackage.projection surface
        OB.coarseCounterexampleLeft
        ≢
      ShiftContractMdlLevelCoarseObservablePackage.projection surface
        OB.coarseCounterexampleRight
    outcome : NewWitnessSearchOutcome

canonicalShiftContractMdlLevelNewWitnessSearch :
  ShiftContractMdlLevelNewWitnessSearch
canonicalShiftContractMdlLevelNewWitnessSearch =
  record
    { surface = canonicalShiftContractMdlLevelCoarseObservablePackage
    ; retiredPairRejected = retiredOldPairRejected
    ; outcome = noBetterSmallWitnessFound
    }

open ShiftContractMdlLevelNewWitnessSearch public
