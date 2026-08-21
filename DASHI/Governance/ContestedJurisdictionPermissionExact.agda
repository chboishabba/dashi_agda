module DASHI.Governance.ContestedJurisdictionPermissionExact where

------------------------------------------------------------------------
-- CONTESTED JURISDICTION / PERMISSION NON-MEET
--
-- A thin application of ContestedAmbientAuthorityHyperformalismExact.  Two
-- independently constituted carriers may classify permission for the same act
-- differently.  Permission disagreement does not select an ambient carrier,
-- and administrative/physical clearance does not prove the jurisdictional
-- residual has closed.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Core.ObserverRefinementLatticeExact as Observer
import DASHI.Governance.AuthorityMandateCore as Authority
import DASHI.Governance.ContestedAmbientAuthorityHyperformalismExact as Ambient

data SharedAct : Set where
  maintainAssembly : SharedAct

data PermissionStatus : Set where
  permitted denied : PermissionStatus

record JurisdictionalPermissionSystem : Set where
  constructor jurisdictionalPermissionSystem
  field
    carrier : Ambient.NormativeCarrier
    ambientClaim : Ambient.AmbientAuthorityClaim carrier
    permit : SharedAct → PermissionStatus

open JurisdictionalPermissionSystem public

sourcePermissionSystem : JurisdictionalPermissionSystem
sourcePermissionSystem =
  jurisdictionalPermissionSystem
    Ambient.sourceCarrier
    Ambient.sourceAmbientClaim
    (λ { maintainAssembly → permitted })

otherPermissionSystem : JurisdictionalPermissionSystem
otherPermissionSystem =
  jurisdictionalPermissionSystem
    Ambient.otherCarrier
    Ambient.forceDominantAmbientClaim
    (λ { maintainAssembly → denied })

record PermissionNonMeet : Set where
  constructor permissionNonMeet
  field
    act : SharedAct
    sourceStatus : PermissionStatus
    otherStatus : PermissionStatus
    sourceExact : permit sourcePermissionSystem act ≡ sourceStatus
    otherExact : permit otherPermissionSystem act ≡ otherStatus
    statusesConflict : sourceStatus ≡ otherStatus → ⊥

canonicalPermissionNonMeet : PermissionNonMeet
canonicalPermissionNonMeet =
  permissionNonMeet
    maintainAssembly
    permitted
    denied
    refl
    refl
    (λ ())

permissionDenialDoesNotSelfLegitimateAmbientClaim :
  Ambient.LegitimateAmbientAuthority Ambient.forceDominantAmbientClaim →
  Authority.Never
permissionDenialDoesNotSelfLegitimateAmbientClaim =
  Ambient.coerciveDominanceDoesNotEstablishLegitimateAmbientAuthority

data JurisdictionalFineState : Set where
  administrativeViolationState independentlyAuthorisedPresenceState :
    JurisdictionalFineState

data AdministrativeSurface : Set where
  unauthorisedPresenceSurface : AdministrativeSurface

data JurisdictionalSurface : Set where
  hostOnlyReading independentAuthorityReading : JurisdictionalSurface

administrativeObserver :
  Observer.Observer JurisdictionalFineState AdministrativeSurface
administrativeObserver _ = unauthorisedPresenceSurface

jurisdictionalObserver :
  Observer.Observer JurisdictionalFineState JurisdictionalSurface
jurisdictionalObserver administrativeViolationState = hostOnlyReading
jurisdictionalObserver independentlyAuthorisedPresenceState = independentAuthorityReading

administrativeCollision : Observer.ObserverCollision administrativeObserver
administrativeCollision =
  Observer.observerCollision
    administrativeViolationState
    independentlyAuthorisedPresenceState
    refl
    (λ ())

administrativeSurfaceCannotSeparateJurisdiction :
  Observer.Separating administrativeObserver → ⊥
administrativeSurfaceCannotSeparateJurisdiction =
  Observer.collisionBlocksSeparation administrativeCollision

jurisdictionalRefinesAdministrative :
  Observer.StrictRefinement administrativeObserver jurisdictionalObserver
jurisdictionalRefinesAdministrative =
  Observer.strictRefinement
    (λ x y same → refl)
    administrativeViolationState
    independentlyAuthorisedPresenceState
    refl
    (λ ())

data PhysicalSurface : Set where
  occupiedSurface clearedSurface : PhysicalSurface

data SourceAuthorityResidual : Set where
  residualOpen : SourceAuthorityResidual

record ClearanceWithoutJurisdictionClosure : Set where
  constructor clearanceWithoutJurisdictionClosure
  field
    beforeSurface : PhysicalSurface
    afterSurface : PhysicalSurface
    changedSurface : beforeSurface ≡ afterSurface → ⊥
    residualBefore : SourceAuthorityResidual
    residualAfter : SourceAuthorityResidual
    residualPreserved : residualAfter ≡ residualBefore

canonicalClearanceWithoutJurisdictionClosure :
  ClearanceWithoutJurisdictionClosure
canonicalClearanceWithoutJurisdictionClosure =
  clearanceWithoutJurisdictionClosure
    occupiedSurface
    clearedSurface
    (λ ())
    residualOpen
    residualOpen
    refl

record ContestedJurisdictionPermissionBoundary : Set where
  constructor contestedJurisdictionPermissionBoundary
  field
    permissionDisagreementSelectsUniversalHost : Bool
    coerciveDenialCreatesLegitimateAuthority : Bool
    administrativeClassificationExhaustsJurisdiction : Bool
    physicalClearanceClosesAuthorityResidual : Bool
    independentlySourcedPermissionFunctionsAllowed : Bool

canonicalContestedJurisdictionPermissionBoundary :
  ContestedJurisdictionPermissionBoundary
canonicalContestedJurisdictionPermissionBoundary =
  contestedJurisdictionPermissionBoundary false false false false true
