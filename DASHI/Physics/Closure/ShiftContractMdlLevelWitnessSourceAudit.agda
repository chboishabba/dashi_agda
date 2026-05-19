module DASHI.Physics.Closure.ShiftContractMdlLevelWitnessSourceAudit where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Sigma using (fst)
open import Data.Empty using (⊥)

open import DASHI.Physics.Closure.ShiftContractMdlLevelCounterexampleAudit as SCMA
  using (oldCoarsePairSeparatedByMdlLevelSurface)
open import DASHI.Physics.Closure.ShiftContractMdlLevelCoarseObservable as SCMCO
  using
    ( MdlLevelCoarseObservable
    ; π-mdl-max
    )
open import DASHI.Physics.Closure.ShiftContractMdlLevelFreshWitnessSearch as SCMFS
  using
    ( FreshWitnessSearchOutcome
    ; noFreshWitnessFound
    )
open import DASHI.Physics.Closure.ShiftContractMdlLevelNewWitnessSearch as SCMNS
  using
    ( NewWitnessSearchOutcome
    ; noBetterSmallWitnessFound
    )
open import DASHI.Physics.Closure.ShiftContractMdlLevelPrimeImageSubfamilyAttempt as SPMI
  using
    ( MdlLevelPrimeImageSubfamily
    ; subfamilyMember
    ; primeImage-equal-on-subfamily
    ; subfamily-π-mdl-max
    ; subfamily-prime-image
    )
open import DASHI.Physics.Closure.ShiftContractStatePrimeCompatibilityProfileInstance as SCSP
  using (shiftContractStateTransportedPrimeEmbedding)
open import DASHI.Physics.Closure.ShiftContractNoncanonicalP2ControlObstruction as OB
  using (coarseCounterexampleLeft; coarseCounterexampleRight)

------------------------------------------------------------------------
-- Same-carrier witness-source audit for the strengthened `mdlLevel × π-max`
-- surface.
--
-- Checked pools:
-- - the retired coarse pair on `ShiftContractState`;
-- - the singleton subfamily around `coarseCounterexampleLeft`;
-- - the bounded fresh/new witness-search modules already present in-repo.
--
-- Exhaustion result:
-- - no explicit same-carrier pair with equal `π-mdl-max` and unequal
--   transported prime image is recovered from those pools.
--
-- Next plausible explicit source in-tree:
-- - a new two-point or larger explicit `ShiftContractState` family, since the
--   singleton subfamily and the bounded search wrappers are already exhausted.

private
  _≢_ : {A : Set} → A → A → Set
  x ≢ y = x ≡ y → ⊥

data WitnessSourceStatus : Set where
  checkedPoolsExhausted : WitnessSourceStatus

oldPairRejectedByMdlLevelSurface :
  π-mdl-max OB.coarseCounterexampleLeft
    ≢
  π-mdl-max OB.coarseCounterexampleRight
oldPairRejectedByMdlLevelSurface = oldCoarsePairSeparatedByMdlLevelSurface

record ShiftContractMdlLevelWitnessSourceAudit : Set₁ where
  field
    surface : MdlLevelCoarseObservable
    retiredPairRejected :
      π-mdl-max OB.coarseCounterexampleLeft
        ≢
      π-mdl-max OB.coarseCounterexampleRight
    singletonSubfamily : MdlLevelPrimeImageSubfamily
    singletonPrimeImageStable :
      shiftContractStateTransportedPrimeEmbedding (fst singletonSubfamily)
        ≡
      shiftContractStateTransportedPrimeEmbedding (fst singletonSubfamily)
    freshWitnessSearchOutcome : FreshWitnessSearchOutcome
    newWitnessSearchOutcome : NewWitnessSearchOutcome
    status : WitnessSourceStatus

canonicalShiftContractMdlLevelWitnessSourceAudit :
  ShiftContractMdlLevelWitnessSourceAudit
canonicalShiftContractMdlLevelWitnessSourceAudit =
  record
    { surface = π-mdl-max coarseCounterexampleLeft
    ; retiredPairRejected = oldPairRejectedByMdlLevelSurface
    ; singletonSubfamily = subfamilyMember
    ; singletonPrimeImageStable = refl
    ; freshWitnessSearchOutcome = noFreshWitnessFound
    ; newWitnessSearchOutcome = noBetterSmallWitnessFound
    ; status = checkedPoolsExhausted
    }
