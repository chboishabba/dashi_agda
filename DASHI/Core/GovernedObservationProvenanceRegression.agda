module DASHI.Core.GovernedObservationProvenanceRegression where

------------------------------------------------------------------------
-- FINITE REGRESSION FOR GOVERNED OBSERVATION / PROVENANCE
--
-- Three neutral finite witnesses mirror the structural shapes appearing in
-- situated-knowledge translation, released-artifact provenance, and historical
-- event attribution.  They are intentionally domain-free: the point is to pin
-- the reusable theorem pattern, not to re-state any source-specific claims.
------------------------------------------------------------------------

open import DASHI.Core.Prelude

import DASHI.Core.ConsumerIndexedResidualRefinementExact as Consumer
import DASHI.Core.GovernedObservationProvenanceExact as Governed

------------------------------------------------------------------------
-- 1. Same value surface, different permission.
------------------------------------------------------------------------

data KnowledgeState : Set where
  restrictedCarrier openCarrier : KnowledgeState

data ValueSurface : Set where
  sameValue : ValueSurface

data Permission : Set where
  restrictedUse openUse : Permission

knowledgeValue : KnowledgeState → ValueSurface
knowledgeValue restrictedCarrier = sameValue
knowledgeValue openCarrier = sameValue

knowledgePermission : KnowledgeState → Permission
knowledgePermission restrictedCarrier = restrictedUse
knowledgePermission openCarrier = openUse

knowledgePermissionCollision :
  Consumer.ConsumerRelevantCollision knowledgeValue knowledgePermission
knowledgePermissionCollision =
  Consumer.consumer-relevant-collision
    restrictedCarrier openCarrier refl (λ ())

knowledgeValueCannotBePermissionSafe :
  Governed.PermissionSafe knowledgeValue knowledgePermission → ⊥
knowledgeValueCannotBePermissionSafe =
  Consumer.coarseCollisionBlocksSufficiency knowledgePermissionCollision

------------------------------------------------------------------------
-- 2. Same release surface, different epistemic verification.
------------------------------------------------------------------------

data ReleaseState : Set where
  unverifiedRelease verifiedRelease : ReleaseState

data ReleaseSurface : Set where
  sameRelease : ReleaseSurface

data Verification : Set where
  unverified verified : Verification

releaseSurface : ReleaseState → ReleaseSurface
releaseSurface unverifiedRelease = sameRelease
releaseSurface verifiedRelease = sameRelease

verificationStatus : ReleaseState → Verification
verificationStatus unverifiedRelease = unverified
verificationStatus verifiedRelease = verified

releaseVerificationCollision :
  Consumer.ConsumerRelevantCollision releaseSurface verificationStatus
releaseVerificationCollision =
  Consumer.consumer-relevant-collision
    unverifiedRelease verifiedRelease refl (λ ())

releaseSurfaceCannotBeEpistemicallySafe :
  Governed.EpistemicSafe releaseSurface verificationStatus → ⊥
releaseSurfaceCannotBeEpistemicallySafe =
  Consumer.coarseCollisionBlocksSufficiency releaseVerificationCollision

------------------------------------------------------------------------
-- 3. Same event surface, different cause attribution.
------------------------------------------------------------------------

data EventState : Set where
  causeA causeB : EventState

data EventSurface : Set where
  sameEvent : EventSurface

data CauseAttribution : Set where
  firstCause secondCause : CauseAttribution

eventSurface : EventState → EventSurface
eventSurface causeA = sameEvent
eventSurface causeB = sameEvent

causeAttribution : EventState → CauseAttribution
causeAttribution causeA = firstCause
causeAttribution causeB = secondCause

eventCauseCollision :
  Consumer.ConsumerRelevantCollision eventSurface causeAttribution
eventCauseCollision =
  Consumer.consumer-relevant-collision causeA causeB refl (λ ())

eventSurfaceCannotRecoverCause :
  Consumer.ConsumerSufficient eventSurface causeAttribution → ⊥
eventSurfaceCannotRecoverCause =
  Consumer.coarseCollisionBlocksSufficiency eventCauseCollision

------------------------------------------------------------------------
-- 4. Coordinate-lineage regression.
------------------------------------------------------------------------

eraseThenAddProducesNewLineage :
  Governed.applyTwoEffects
    Governed.erasesCoordinate
    Governed.addsCoordinate
    Governed.inheritedCoordinate
  ≡ Governed.introducedCoordinate
eraseThenAddProducesNewLineage =
  Governed.additionAfterErasureIsIntroducedNotInherited

eraseThenAddCannotRestoreOldLineage :
  Governed.applyTwoEffects
    Governed.erasesCoordinate
    Governed.addsCoordinate
    Governed.inheritedCoordinate
  ≡ Governed.inheritedCoordinate → ⊥
eraseThenAddCannotRestoreOldLineage =
  Governed.additionAfterErasureDoesNotRestoreInheritedLineage

record GovernedObservationRegressionBoundary : Set where
  field
    sameValueCanHidePermission : Bool
    sameReleaseCanHideVerification : Bool
    sameEventCanHideCause : Bool
    laterAddedCoordinateRestoresErasedLineage : Bool

canonicalGovernedObservationRegressionBoundary :
  GovernedObservationRegressionBoundary
canonicalGovernedObservationRegressionBoundary = record
  { sameValueCanHidePermission = true
  ; sameReleaseCanHideVerification = true
  ; sameEventCanHideCause = true
  ; laterAddedCoordinateRestoresErasedLineage = false
  }
