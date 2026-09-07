module DASHI.Core.DialecticalMaterialFutureSafetyExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)

import DASHI.Core.DialecticalMaterialRevisionExact as Material
import DASHI.Core.ConsumerIndexedResidualRefinementExact as Consumer

------------------------------------------------------------------------
-- FUTURE SAFETY UNDER MATERIAL REVISION
--
-- A surface adequate under one material regime need not remain adequate after
-- conditions change.  The repair is consumer-indexed: retain/reopen the
-- material coordinate that distinguishes the newly divergent consumer answer.
------------------------------------------------------------------------

data World : Set where
  lowPressureWorld highPressureWorld : World

data Surface : Set where
  sameDeclaredSurface : Surface

data Outcome : Set where
  stableOutcome contestedOutcome : Outcome

observe : World → Surface
observe _ = sameDeclaredSurface

materialOutcome : World → Outcome
materialOutcome lowPressureWorld = stableOutcome
materialOutcome highPressureWorld = contestedOutcome

materialCollision : Consumer.ConsumerRelevantCollision observe materialOutcome
materialCollision =
  Consumer.consumer-relevant-collision
    lowPressureWorld highPressureWorld refl (λ ())

surfaceCannotDetermineMateriallyRevisedOutcome :
  Consumer.ConsumerSufficient observe materialOutcome → ⊥
surfaceCannotDetermineMateriallyRevisedOutcome =
  Consumer.coarseCollisionBlocksSufficiency materialCollision

-- A fine observer retaining the material regime separates the witness.
data MaterialRegime : Set where lowRegime highRegime : MaterialRegime

refinedObserve : World → Surface × MaterialRegime
refinedObserve lowPressureWorld = sameDeclaredSurface , lowRegime
refinedObserve highPressureWorld = sameDeclaredSurface , highRegime

refinedObserverIsSufficient :
  Consumer.ConsumerSufficient refinedObserve materialOutcome
refinedObserverIsSufficient lowPressureWorld lowPressureWorld same = refl
refinedObserverIsSufficient lowPressureWorld highPressureWorld ()
refinedObserverIsSufficient highPressureWorld lowPressureWorld ()
refinedObserverIsSufficient highPressureWorld highPressureWorld same = refl

record DialecticalMaterialFutureSafetyBoundary : Set where
  constructor dialectical-material-future-safety-boundary
  field
    sameDeclaredSurfaceImpliesSameFutureOutcomeAcrossMaterialRegimes : Bool
    materialCoordinateMayBeRequiredForFutureSafety : Bool
    observerFailureMeansDeclaredSurfaceWasAlwaysFalse : Bool
    materialRefinementAutomaticallyCreatesActionAuthority : Bool

canonicalDialecticalMaterialFutureSafetyBoundary :
  DialecticalMaterialFutureSafetyBoundary
canonicalDialecticalMaterialFutureSafetyBoundary =
  dialectical-material-future-safety-boundary false true false false

existingMaterialRevisionBoundary : Material.DialecticalMaterialRevisionBoundary
existingMaterialRevisionBoundary = Material.canonicalDialecticalMaterialRevisionBoundary
