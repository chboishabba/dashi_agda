module DASHI.Empirical.DarkDimensionBedroyaBAOReadinessExact where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Empty using (⊥)

import DASHI.Core.RequiredObserverAxisJoinAdequacyExact as AxisJoin
import DASHI.Core.IntersectionalNonFactorability as NonFactor
import DASHI.Empirical.DarkDimensionBedroyaBackgroundInputContractExact as Input
import DASHI.Empirical.DarkDimensionBedroyaConditionalRuntimeExact as Runtime

------------------------------------------------------------------------
-- TWO-STAGE BEDROYA SAME-KEY BAO READINESS
--
-- Finite dependency model only: background-vector readiness and same-fit
-- baryon-drag-horizon readiness are independent required axes for the declared
-- BAO-ratio consumer.  This does not assert empirical world completeness.
------------------------------------------------------------------------

data BAOReadinessState : Set where
  nothingPaid : BAOReadinessState
  backgroundOnlyPaid : BAOReadinessState
  rDragOnlyPaid : BAOReadinessState
  backgroundAndRDragPaid : BAOReadinessState

data BackgroundReadiness : Set where
  backgroundMissing : BackgroundReadiness
  backgroundPaid : BackgroundReadiness

data RDragReadiness : Set where
  rDragMissing : RDragReadiness
  rDragPaid : RDragReadiness

backgroundReadinessAxis : BAOReadinessState → BackgroundReadiness
backgroundReadinessAxis nothingPaid = backgroundMissing
backgroundReadinessAxis backgroundOnlyPaid = backgroundPaid
backgroundReadinessAxis rDragOnlyPaid = backgroundMissing
backgroundReadinessAxis backgroundAndRDragPaid = backgroundPaid

rDragReadinessAxis : BAOReadinessState → RDragReadiness
rDragReadinessAxis nothingPaid = rDragMissing
rDragReadinessAxis backgroundOnlyPaid = rDragMissing
rDragReadinessAxis rDragOnlyPaid = rDragPaid
rDragReadinessAxis backgroundAndRDragPaid = rDragPaid

sameKeyBAOReadinessJoin :
  BAOReadinessState → BackgroundReadiness × RDragReadiness
sameKeyBAOReadinessJoin =
  AxisJoin.jointAxis backgroundReadinessAxis rDragReadinessAxis

rDragDiffersUnderBackgroundCollision :
  rDragReadinessAxis nothingPaid ≡ rDragReadinessAxis rDragOnlyPaid → ⊥
rDragDiffersUnderBackgroundCollision ()

backgroundDiffersUnderRDragCollision :
  backgroundReadinessAxis nothingPaid ≡
  backgroundReadinessAxis backgroundOnlyPaid → ⊥
backgroundDiffersUnderRDragCollision ()

backgroundObserverRDragWitness :
  NonFactor.NonFactorabilityWitness
    backgroundReadinessAxis
    rDragReadinessAxis
backgroundObserverRDragWitness =
  NonFactor.nonFactorabilityWitness
    nothingPaid
    rDragOnlyPaid
    refl
    rDragDiffersUnderBackgroundCollision

rDragObserverBackgroundWitness :
  NonFactor.NonFactorabilityWitness
    rDragReadinessAxis
    backgroundReadinessAxis
rDragObserverBackgroundWitness =
  NonFactor.nonFactorabilityWitness
    nothingPaid
    backgroundOnlyPaid
    refl
    backgroundDiffersUnderRDragCollision

backgroundOnlyCannotRecoverRDrag :
  AxisJoin.RetainsAxis backgroundReadinessAxis rDragReadinessAxis → ⊥
backgroundOnlyCannotRecoverRDrag =
  NonFactor.witnessRulesOutEveryFlatFactorisation backgroundObserverRDragWitness

rDragOnlyCannotRecoverBackground :
  AxisJoin.RetainsAxis rDragReadinessAxis backgroundReadinessAxis → ⊥
rDragOnlyCannotRecoverBackground =
  NonFactor.witnessRulesOutEveryFlatFactorisation rDragObserverBackgroundWitness

bothAxesRequiredForSameKeyBAO :
  AxisJoin.RetainsBothRequiredAxes
    sameKeyBAOReadinessJoin
    backgroundReadinessAxis
    rDragReadinessAxis
bothAxesRequiredForSameKeyBAO =
  AxisJoin.retainsBothRequiredAxes
    (AxisJoin.jointRetainsLeft backgroundReadinessAxis rDragReadinessAxis)
    (AxisJoin.jointRetainsRight backgroundReadinessAxis rDragReadinessAxis)

backgroundInputStillOpen :
  Input.completeBackgroundInputManifestLocated
    Input.canonicalBedroyaBackgroundInputStatus
  ≡ false
backgroundInputStillOpen = Input.completeBackgroundInputStillOpen

rDragStillOpen :
  Input.exactRDragSameFitLocated
    Input.canonicalBedroyaBackgroundInputStatus
  ≡ false
rDragStillOpen = Input.exactRDragSameFitStillOpen

data RuntimeSchemaManufacturesReadinessAxes : Set where

runtimeSchemaDoesNotManufactureEitherAxis :
  RuntimeSchemaManufacturesReadinessAxes → ⊥
runtimeSchemaDoesNotManufactureEitherAxis ()

runtimeContractRemainsBackgroundBlocked :
  Input.completeBackgroundInputManifestLocated
    Input.canonicalBedroyaBackgroundInputStatus
  ≡ false
runtimeContractRemainsBackgroundBlocked = Runtime.canonicalRuntimeRequestStillBlocked

runtimeContractRemainsRDragBlocked :
  Input.exactRDragSameFitLocated
    Input.canonicalBedroyaBackgroundInputStatus
  ≡ false
runtimeContractRemainsRDragBlocked = Runtime.canonicalBAONormalizationStillBlocked
