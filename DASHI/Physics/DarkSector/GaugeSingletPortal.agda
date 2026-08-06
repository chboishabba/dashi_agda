module DASHI.Physics.DarkSector.GaugeSingletPortal where

open import DASHI.Core.Prelude

------------------------------------------------------------------------
-- A portal is represented by an interaction operator with invariant visible
-- and dark factors.  It is not identified with an arbitrary observation map.

data GaugeRepresentation : Set where
  singletRepresentation : GaugeRepresentation
  nonSingletRepresentation : GaugeRepresentation

record PortalOperator : Set where
  constructor portalOperator
  field
    visibleFactor : GaugeRepresentation
    darkFactor : GaugeRepresentation
    couplingStrength : Nat
    symmetryPermitsLinearDarkFactor : Bool

open PortalOperator public

portalAllowed : PortalOperator → Bool
portalAllowed
  (portalOperator singletRepresentation singletRepresentation coupling linear) =
  true
portalAllowed
  (portalOperator singletRepresentation nonSingletRepresentation coupling linear) =
  false
portalAllowed
  (portalOperator nonSingletRepresentation singletRepresentation coupling linear) =
  false
portalAllowed
  (portalOperator nonSingletRepresentation nonSingletRepresentation coupling linear) =
  false

canonicalQuadraticHiggsPortal : PortalOperator
canonicalQuadraticHiggsPortal =
  portalOperator
    singletRepresentation
    singletRepresentation
    2
    false

canonicalLinearHiggsPortal : PortalOperator
canonicalLinearHiggsPortal =
  portalOperator
    singletRepresentation
    singletRepresentation
    1
    true

forbiddenNonSingletPortal : PortalOperator
forbiddenNonSingletPortal =
  portalOperator
    nonSingletRepresentation
    singletRepresentation
    2
    false

quadraticHiggsPortalIsAllowed :
  portalAllowed canonicalQuadraticHiggsPortal ≡ true
quadraticHiggsPortalIsAllowed = refl

linearHiggsPortalRequiresDeclaredPermission :
  symmetryPermitsLinearDarkFactor canonicalLinearHiggsPortal ≡ true
linearHiggsPortalRequiresDeclaredPermission = refl

nonSingletPortalIsRejected :
  portalAllowed forbiddenNonSingletPortal ≡ false
nonSingletPortalIsRejected = refl

------------------------------------------------------------------------
-- Projection and interaction are separate typed objects.

data ObservationProjection : Set where
  visibleProjection : ObservationProjection
  darkProjection : ObservationProjection

record GaugeSingletPortalBoundary : Set where
  constructor gaugeSingletPortalBoundary
  field
    arbitraryProjectionIsPortalInteraction : Bool
    arbitraryProjectionIsPortalInteractionIsFalse :
      arbitraryProjectionIsPortalInteraction ≡ false

    singletStatusAloneFixesPortalCoupling : Bool
    singletStatusAloneFixesPortalCouplingIsFalse :
      singletStatusAloneFixesPortalCoupling ≡ false

    quadraticPortalAutomaticallyDestabilisesDarkParticle : Bool
    quadraticPortalAutomaticallyDestabilisesDarkParticleIsFalse :
      quadraticPortalAutomaticallyDestabilisesDarkParticle ≡ false

open GaugeSingletPortalBoundary public

canonicalGaugeSingletPortalBoundary : GaugeSingletPortalBoundary
canonicalGaugeSingletPortalBoundary =
  gaugeSingletPortalBoundary false refl false refl false refl
