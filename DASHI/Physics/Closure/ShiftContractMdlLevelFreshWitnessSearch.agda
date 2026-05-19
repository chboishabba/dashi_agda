module DASHI.Physics.Closure.ShiftContractMdlLevelFreshWitnessSearch where

open import Agda.Builtin.Equality using (_≡_)
open import Data.Empty using (⊥)

open import DASHI.Physics.Closure.ShiftContractMdlLevelCounterexampleAudit as SCMA
  using (oldCoarsePairSeparatedByMdlLevelSurface)
open import DASHI.Physics.Closure.ShiftContractMdlLevelPrimeOrOrbitControl as SCMPOC
  using
    ( ShiftContractMdlLevelPrimeOrOrbitControlAttempt
    ; canonicalShiftContractMdlLevelPrimeOrOrbitControlAttempt
    ; mdlLevelFibrePrimeField
    ; mdlLevelFibreOrbitSummary
    )
open import DASHI.Physics.Closure.ShiftContractMdlLevelCoarseObservable as SCMCO
  using (MdlLevelCoarseObservable; π-mdl-max)
open import DASHI.Physics.Closure.ShiftContractNoncanonicalP2ControlObstruction as OB
  using (coarseCounterexampleLeft; coarseCounterexampleRight)
open import DASHI.Physics.Closure.ShiftContractStatePrimeCompatibilityProfileInstance as SCSP
  using (ShiftContractState; shiftContractStateTransportedPrimeEmbedding)

------------------------------------------------------------------------
-- Fresh witness search on the strengthened `mdlLevel × π-max` surface.
--
-- The retired old coarse counterexample pair is explicitly rejected here.
-- A fresh small witness pair for failure of prime-image or p2-orbit-summary
-- control is not recovered from the explicit examples already present in the
-- repo, so the bounded search result is the negative one.

private
  _≢_ : {A : Set} → A → A → Set
  x ≢ y = x ≡ y → ⊥

retiredPairRejected :
  π-mdl-max OB.coarseCounterexampleLeft
    ≢
  π-mdl-max OB.coarseCounterexampleRight
retiredPairRejected = oldCoarsePairSeparatedByMdlLevelSurface

data FreshWitnessSearchOutcome : Set where
  noFreshWitnessFound : FreshWitnessSearchOutcome

record ShiftContractMdlLevelFreshWitnessSearch : Set₁ where
  field
    surface : ShiftContractMdlLevelPrimeOrOrbitControlAttempt
    retiredPairRejectedBySurface :
      ShiftContractMdlLevelPrimeOrOrbitControlAttempt.projection surface
        OB.coarseCounterexampleLeft
        ≢
      ShiftContractMdlLevelPrimeOrOrbitControlAttempt.projection surface
        OB.coarseCounterexampleRight
    outcome : FreshWitnessSearchOutcome

canonicalShiftContractMdlLevelFreshWitnessSearch :
  ShiftContractMdlLevelFreshWitnessSearch
canonicalShiftContractMdlLevelFreshWitnessSearch =
  record
    { surface = canonicalShiftContractMdlLevelPrimeOrOrbitControlAttempt
    ; retiredPairRejectedBySurface = retiredPairRejected
    ; outcome = noFreshWitnessFound
    }

open ShiftContractMdlLevelFreshWitnessSearch public
