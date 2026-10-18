module DASHI.Law.QueryScopedWorldCoordinateImpactExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Empty using (⊥)

------------------------------------------------------------------------
-- S15 × S18: query-scoped time and jurisdiction coordinates.
--
-- A world coordinate participates in the consumer projection exactly when Q
-- requires that axis.  Therefore changing as-at/jurisdiction outside Q's
-- required axes is consumer-invariant; changing a required coordinate changes
-- the query-world observation.
------------------------------------------------------------------------

data Time : Set where
  t₀ t₁ : Time

data Jurisdiction : Set where
  au qld nsw : Jurisdiction

record World : Set where
  constructor world
  field
    asAt : Time
    jurisdiction : Jurisdiction

open World public

record RequiredAxes : Set where
  constructor requiredAxes
  field
    temporal : Bool
    jurisdictional : Bool

open RequiredAxes public

data OptionalTime : Set where
  noTime : OptionalTime
  someTime : Time → OptionalTime

data OptionalJurisdiction : Set where
  noJurisdiction : OptionalJurisdiction
  someJurisdiction : Jurisdiction → OptionalJurisdiction

record QueryWorldObservation : Set where
  constructor queryWorldObservation
  field
    timeCoordinate : OptionalTime
    jurisdictionCoordinate : OptionalJurisdiction

projectTime : Bool → Time → OptionalTime
projectTime false t = noTime
projectTime true t = someTime t

projectJurisdiction : Bool → Jurisdiction → OptionalJurisdiction
projectJurisdiction false j = noJurisdiction
projectJurisdiction true j = someJurisdiction j

queryWorldProject : RequiredAxes → World → QueryWorldObservation
queryWorldProject axes w =
  queryWorldObservation
    (projectTime (temporal axes) (asAt w))
    (projectJurisdiction (jurisdictional axes) (jurisdiction w))

noWorldAxes : RequiredAxes
noWorldAxes = requiredAxes false false

temporalOnly : RequiredAxes
temporalOnly = requiredAxes true false

jurisdictionOnly : RequiredAxes
jurisdictionOnly = requiredAxes false true

oldWorld : World
oldWorld = world t₀ qld

laterWorld : World
laterWorld = world t₁ qld

nswWorld : World
nswWorld = world t₀ nsw

irrelevantTimeChangePreservesProjection :
  queryWorldProject noWorldAxes oldWorld
  ≡
  queryWorldProject noWorldAxes laterWorld
irrelevantTimeChangePreservesProjection = refl

irrelevantJurisdictionChangePreservesProjection :
  queryWorldProject noWorldAxes oldWorld
  ≡
  queryWorldProject noWorldAxes nswWorld
irrelevantJurisdictionChangePreservesProjection = refl

t₀≠t₁ : t₀ ≡ t₁ → ⊥
t₀≠t₁ ()

qld≠nsw : qld ≡ nsw → ⊥
qld≠nsw ()

requiredTimeChangeChangesProjection :
  queryWorldProject temporalOnly oldWorld
  ≡
  queryWorldProject temporalOnly laterWorld
  → ⊥
requiredTimeChangeChangesProjection ()

requiredJurisdictionChangeChangesProjection :
  queryWorldProject jurisdictionOnly oldWorld
  ≡
  queryWorldProject jurisdictionOnly nswWorld
  → ⊥
requiredJurisdictionChangeChangesProjection ()

data QueryWorldImpactKind : Set where
  noWorldCoordinateChange : QueryWorldImpactKind
  worldChangedConsumerInvariant : QueryWorldImpactKind
  worldChangedConsumerRelevant : QueryWorldImpactKind

record QueryScopedWorldCoordinateImpactBoundary : Set where
  constructor queryScopedWorldCoordinateImpactBoundary
  field
    unrequiredTimeChangeMayPreserveQueryProjection : Bool
    unrequiredTimeChangeMayPreserveQueryProjectionIsTrue :
      unrequiredTimeChangeMayPreserveQueryProjection ≡ true

    requiredTimeChangeMayChangeQueryProjection : Bool
    requiredTimeChangeMayChangeQueryProjectionIsTrue :
      requiredTimeChangeMayChangeQueryProjection ≡ true

    unrequiredJurisdictionChangeMayPreserveQueryProjection : Bool
    unrequiredJurisdictionChangeMayPreserveQueryProjectionIsTrue :
      unrequiredJurisdictionChangeMayPreserveQueryProjection ≡ true

    requiredJurisdictionChangeMayChangeQueryProjection : Bool
    requiredJurisdictionChangeMayChangeQueryProjectionIsTrue :
      requiredJurisdictionChangeMayChangeQueryProjection ≡ true

    unrequiredWorldCoordinateChangeReopensResearch : Bool
    unrequiredWorldCoordinateChangeReopensResearchIsFalse :
      unrequiredWorldCoordinateChangeReopensResearch ≡ false

    requiredWorldCoordinateChangeMayReopenResearch : Bool
    requiredWorldCoordinateChangeMayReopenResearchIsTrue :
      requiredWorldCoordinateChangeMayReopenResearch ≡ true

    worldCoordinateProjectionCreatesSemanticAuthority : Bool
    worldCoordinateProjectionCreatesSemanticAuthorityIsFalse :
      worldCoordinateProjectionCreatesSemanticAuthority ≡ false

    worldCoordinateProjectionCreatesClaimTruth : Bool
    worldCoordinateProjectionCreatesClaimTruthIsFalse :
      worldCoordinateProjectionCreatesClaimTruth ≡ false

open QueryScopedWorldCoordinateImpactBoundary public

canonicalQueryScopedWorldCoordinateImpactBoundary :
  QueryScopedWorldCoordinateImpactBoundary
canonicalQueryScopedWorldCoordinateImpactBoundary =
  queryScopedWorldCoordinateImpactBoundary
    true refl
    true refl
    true refl
    true refl
    false refl
    true refl
    false refl
    false refl
