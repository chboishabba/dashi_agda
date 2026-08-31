module DASHI.Core.GovernedObservationProvenanceExact where

------------------------------------------------------------------------
-- GOVERNED OBSERVATION / PROVENANCE / COORDINATE-LINEAGE CALCULUS
--
-- Cross-domain rule:
--
--   preserving a value surface
--   != preserving provenance
--   != preserving epistemic status
--   != preserving authority / permission / obligation.
--
-- A second rule concerns multi-stage pipelines.  Stage annotations such as
-- "preserve / add / erase / unresolved" are not safely compositional unless
-- the lineage of a coordinate is retained.  In particular:
--
--   erase inherited coordinate -> add a coordinate later
--
-- does NOT restore the inherited coordinate.  The later coordinate is newly
-- introduced information and therefore has different provenance.
------------------------------------------------------------------------

open import DASHI.Core.Prelude

import DASHI.Core.ConsumerIndexedResidualRefinementExact as Consumer

------------------------------------------------------------------------
-- 1. Governance-aware consumer sufficiency.
------------------------------------------------------------------------

record GovernedConsumerSufficiency
    {State Surface Value Provenance Epistemic Authority Permission Obligation : Set}
    (observe : State → Surface)
    (value : State → Value)
    (provenance : State → Provenance)
    (epistemic : State → Epistemic)
    (authority : State → Authority)
    (permission : State → Permission)
    (obligation : State → Obligation) : Set where
  constructor governed-consumer-sufficiency
  field
    valueSufficient : Consumer.ConsumerSufficient observe value
    provenanceSufficient : Consumer.ConsumerSufficient observe provenance
    epistemicSufficient : Consumer.ConsumerSufficient observe epistemic
    authoritySufficient : Consumer.ConsumerSufficient observe authority
    permissionSufficient : Consumer.ConsumerSufficient observe permission
    obligationSufficient : Consumer.ConsumerSufficient observe obligation

open GovernedConsumerSufficiency public

-- A collision on any governed axis blocks the claim that the observer is safe
-- for the complete governed consumer bundle.
authorityCollisionBlocksGovernedSufficiency :
  ∀ {State Surface Value Provenance Epistemic Authority Permission Obligation : Set}
    {observe : State → Surface}
    {value : State → Value}
    {provenance : State → Provenance}
    {epistemic : State → Epistemic}
    {authority : State → Authority}
    {permission : State → Permission}
    {obligation : State → Obligation} →
  Consumer.ConsumerRelevantCollision observe authority →
  GovernedConsumerSufficiency
    observe value provenance epistemic authority permission obligation →
  ⊥
authorityCollisionBlocksGovernedSufficiency collision governed =
  Consumer.coarseCollisionBlocksSufficiency collision (authoritySufficient governed)

permissionCollisionBlocksGovernedSufficiency :
  ∀ {State Surface Value Provenance Epistemic Authority Permission Obligation : Set}
    {observe : State → Surface}
    {value : State → Value}
    {provenance : State → Provenance}
    {epistemic : State → Epistemic}
    {authority : State → Authority}
    {permission : State → Permission}
    {obligation : State → Obligation} →
  Consumer.ConsumerRelevantCollision observe permission →
  GovernedConsumerSufficiency
    observe value provenance epistemic authority permission obligation →
  ⊥
permissionCollisionBlocksGovernedSufficiency collision governed =
  Consumer.coarseCollisionBlocksSufficiency collision (permissionSufficient governed)

provenanceCollisionBlocksGovernedSufficiency :
  ∀ {State Surface Value Provenance Epistemic Authority Permission Obligation : Set}
    {observe : State → Surface}
    {value : State → Value}
    {provenance : State → Provenance}
    {epistemic : State → Epistemic}
    {authority : State → Authority}
    {permission : State → Permission}
    {obligation : State → Obligation} →
  Consumer.ConsumerRelevantCollision observe provenance →
  GovernedConsumerSufficiency
    observe value provenance epistemic authority permission obligation →
  ⊥
provenanceCollisionBlocksGovernedSufficiency collision governed =
  Consumer.coarseCollisionBlocksSufficiency collision (provenanceSufficient governed)

epistemicCollisionBlocksGovernedSufficiency :
  ∀ {State Surface Value Provenance Epistemic Authority Permission Obligation : Set}
    {observe : State → Surface}
    {value : State → Value}
    {provenance : State → Provenance}
    {epistemic : State → Epistemic}
    {authority : State → Authority}
    {permission : State → Permission}
    {obligation : State → Obligation} →
  Consumer.ConsumerRelevantCollision observe epistemic →
  GovernedConsumerSufficiency
    observe value provenance epistemic authority permission obligation →
  ⊥
epistemicCollisionBlocksGovernedSufficiency collision governed =
  Consumer.coarseCollisionBlocksSufficiency collision (epistemicSufficient governed)

obligationCollisionBlocksGovernedSufficiency :
  ∀ {State Surface Value Provenance Epistemic Authority Permission Obligation : Set}
    {observe : State → Surface}
    {value : State → Value}
    {provenance : State → Provenance}
    {epistemic : State → Epistemic}
    {authority : State → Authority}
    {permission : State → Permission}
    {obligation : State → Obligation} →
  Consumer.ConsumerRelevantCollision observe obligation →
  GovernedConsumerSufficiency
    observe value provenance epistemic authority permission obligation →
  ⊥
obligationCollisionBlocksGovernedSufficiency collision governed =
  Consumer.coarseCollisionBlocksSufficiency collision (obligationSufficient governed)

------------------------------------------------------------------------
-- 2. Stage effects with coordinate lineage.
------------------------------------------------------------------------

data CoordinateEffect : Set where
  preservesCoordinate addsCoordinate erasesCoordinate unresolvedCoordinate
  : CoordinateEffect

-- Lineage is deliberately richer than an availability Bool.  It distinguishes
-- an inherited coordinate from information introduced downstream.
data CoordinateLineage : Set where
  absentCoordinate : CoordinateLineage
  inheritedCoordinate : CoordinateLineage
  introducedCoordinate : CoordinateLineage
  inheritedAndIntroducedCoordinate : CoordinateLineage
  unresolvedLineage : CoordinateLineage

applyCoordinateEffect : CoordinateEffect → CoordinateLineage → CoordinateLineage
applyCoordinateEffect preservesCoordinate lineage = lineage
applyCoordinateEffect addsCoordinate absentCoordinate = introducedCoordinate
applyCoordinateEffect addsCoordinate inheritedCoordinate = inheritedAndIntroducedCoordinate
applyCoordinateEffect addsCoordinate introducedCoordinate = introducedCoordinate
applyCoordinateEffect addsCoordinate inheritedAndIntroducedCoordinate = inheritedAndIntroducedCoordinate
applyCoordinateEffect addsCoordinate unresolvedLineage = unresolvedLineage
applyCoordinateEffect erasesCoordinate lineage = absentCoordinate
applyCoordinateEffect unresolvedCoordinate lineage = unresolvedLineage

applyTwoEffects :
  CoordinateEffect → CoordinateEffect → CoordinateLineage → CoordinateLineage
applyTwoEffects first second lineage =
  applyCoordinateEffect second (applyCoordinateEffect first lineage)

preservationIsIdentity :
  ∀ lineage →
  applyCoordinateEffect preservesCoordinate lineage ≡ lineage
preservationIsIdentity lineage = refl

erasureRemovesInheritedLineage :
  applyCoordinateEffect erasesCoordinate inheritedCoordinate ≡ absentCoordinate
erasureRemovesInheritedLineage = refl

additionAfterErasureIsIntroducedNotInherited :
  applyTwoEffects erasesCoordinate addsCoordinate inheritedCoordinate
  ≡ introducedCoordinate
additionAfterErasureIsIntroducedNotInherited = refl

additionAfterErasureDoesNotRestoreInheritedLineage :
  applyTwoEffects erasesCoordinate addsCoordinate inheritedCoordinate
  ≡ inheritedCoordinate → ⊥
additionAfterErasureDoesNotRestoreInheritedLineage ()

additionPreservesAndMarksExistingInheritedInformation :
  applyCoordinateEffect addsCoordinate inheritedCoordinate
  ≡ inheritedAndIntroducedCoordinate
additionPreservesAndMarksExistingInheritedInformation = refl

------------------------------------------------------------------------
-- 3. Promotion boundaries.
------------------------------------------------------------------------

-- A promotion is safe for one declared axis only when that axis factors
-- through the released / translated surface.  The aliases below are kept
-- explicit because downstream code often needs to say which semantic strength
-- is being preserved rather than merely that "something factors".

ProvenanceSafe :
  ∀ {State Surface Provenance : Set} →
  (State → Surface) → (State → Provenance) → Set
ProvenanceSafe = Consumer.ConsumerSufficient

EpistemicSafe :
  ∀ {State Surface Epistemic : Set} →
  (State → Surface) → (State → Epistemic) → Set
EpistemicSafe = Consumer.ConsumerSufficient

AuthoritySafe :
  ∀ {State Surface Authority : Set} →
  (State → Surface) → (State → Authority) → Set
AuthoritySafe = Consumer.ConsumerSufficient

PermissionSafe :
  ∀ {State Surface Permission : Set} →
  (State → Surface) → (State → Permission) → Set
PermissionSafe = Consumer.ConsumerSufficient

ObligationSafe :
  ∀ {State Surface Obligation : Set} →
  (State → Surface) → (State → Obligation) → Set
ObligationSafe = Consumer.ConsumerSufficient

record GovernedObservationProvenanceBoundary : Set where
  field
    valuePreservationImpliesProvenancePreservation : Bool
    releasePresenceImpliesEpistemicVerification : Bool
    provenancePreservationImpliesAuthorityPreservation : Bool
    authorityPreservationImpliesPermissionPreservation : Bool
    eraseThenAddRestoresInheritedCoordinate : Bool
    downstreamAdditionCanCarryNewInformation : Bool
    governedSafetyIsAxisIndexed : Bool

canonicalGovernedObservationProvenanceBoundary :
  GovernedObservationProvenanceBoundary
canonicalGovernedObservationProvenanceBoundary = record
  { valuePreservationImpliesProvenancePreservation = false
  ; releasePresenceImpliesEpistemicVerification = false
  ; provenancePreservationImpliesAuthorityPreservation = false
  ; authorityPreservationImpliesPermissionPreservation = false
  ; eraseThenAddRestoresInheritedCoordinate = false
  ; downstreamAdditionCanCarryNewInformation = true
  ; governedSafetyIsAxisIndexed = true
  }
