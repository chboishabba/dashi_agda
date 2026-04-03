module DASHI.Physics.Closure.ShiftContractMdlLevelWitnessSearchAudit where

open import Agda.Builtin.Equality using (_≡_)
open import Data.Empty using (⊥)

open import DASHI.Physics.Closure.ShiftContractMdlLevelCounterexampleAudit as SCMA
  using
    ( oldCoarsePairSeparatedByMdlLevelSurface
    ; canonicalShiftContractMdlLevelCounterexampleAudit
    )
open import DASHI.Physics.Closure.ShiftContractMdlLevelCoarseObservable as SCMCO
  using
    ( MdlLevelCoarseObservable
    ; π-mdl-max
    ; canonicalShiftContractMdlLevelCoarseObservablePackage
    )
open import DASHI.Physics.Closure.ShiftContractMdlLevelPrimeImageSubfamilyAttempt as SPMI
  using (MdlLevelPrimeImageSubfamily; subfamilyMember)
open import DASHI.Physics.Closure.ShiftContractNoncanonicalP2ControlObstruction as OB
  using (coarseCounterexampleLeft; coarseCounterexampleRight)

------------------------------------------------------------------------
-- Bounded same-carrier witness-search audit for the stronger
-- `mdlLevel × π-max` surface.
--
-- What was checked:
-- - the retired coarse counterexample pair from the old `π-max` surface;
-- - the only explicit same-carrier subfamily we can certify in-repo:
--   the singleton around `coarseCounterexampleLeft`.
--
-- What was ruled out:
-- - the old coarse pair is not a witness here because it is already
--   separated by `π-mdl-max`;
-- - no bounded pair with equal `π-mdl-max` and unequal transported prime
--   image was recovered from the explicit examples currently present in the
--   repo.

private
  _≢_ : {A : Set} → A → A → Set
  x ≢ y = x ≡ y → ⊥

data CheckedScope : Set where
  retiredPairChecked : CheckedScope
  singletonSubfamilyChecked : CheckedScope

data BoundedSameCarrierSearchOutcome : Set where
  noWitnessRecovered : BoundedSameCarrierSearchOutcome

oldPairRejectedByMdlLevelSurface :
  π-mdl-max OB.coarseCounterexampleLeft
    ≢
  π-mdl-max OB.coarseCounterexampleRight
oldPairRejectedByMdlLevelSurface =
  oldCoarsePairSeparatedByMdlLevelSurface

record ShiftContractMdlLevelWitnessSearchAudit : Set₁ where
  field
    surface : MdlLevelCoarseObservable
    checkedScope : CheckedScope
    singletonSubfamily : MdlLevelPrimeImageSubfamily
    retiredPairRejected :
      π-mdl-max OB.coarseCounterexampleLeft
        ≢
      π-mdl-max OB.coarseCounterexampleRight
    outcome : BoundedSameCarrierSearchOutcome

canonicalShiftContractMdlLevelWitnessSearchAudit :
  ShiftContractMdlLevelWitnessSearchAudit
canonicalShiftContractMdlLevelWitnessSearchAudit =
  record
    { surface = SCMCO.π-mdl-max coarseCounterexampleLeft
    ; checkedScope = singletonSubfamilyChecked
    ; singletonSubfamily = subfamilyMember
    ; retiredPairRejected = oldPairRejectedByMdlLevelSurface
    ; outcome = noWitnessRecovered
    }

