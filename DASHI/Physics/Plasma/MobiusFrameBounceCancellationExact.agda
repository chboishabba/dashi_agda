module DASHI.Physics.Plasma.MobiusFrameBounceCancellationExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

------------------------------------------------------------------------
-- MOBIUS-FRAME BOUNCE CANCELLATION
--
-- "Mobius" here refers to half-turn holonomy of a local transverse frame on an
-- orientable toroidal flux surface.  It does NOT make the flux surface itself a
-- non-orientable Mobius strip.
--
-- The constructive kernel is deliberately abstract: if conjugate bounce states
-- are related by an involution and their radial-drift impulses are additive
-- inverses, the paired radial impulse cancels exactly.
------------------------------------------------------------------------

record DriftAdditiveGroup : Set₁ where
  constructor drift-additive-group
  field
    Carrier : Set
    zero : Carrier
    neg : Carrier → Carrier
    _⊕_ : Carrier → Carrier → Carrier
    rightInverse : (x : Carrier) → x ⊕ neg x ≡ zero

open DriftAdditiveGroup public

record MobiusFrameBounceGeometry (group : DriftAdditiveGroup) : Set₁ where
  constructor mobius-frame-bounce-geometry
  field
    BounceState : Set
    bounce : BounceState → BounceState
    bounceInvolutive : (x : BounceState) → bounce (bounce x) ≡ x

    radialDriftImpulse : BounceState → Carrier group
    conjugateImpulseAntisymmetry :
      (x : BounceState) →
      radialDriftImpulse (bounce x) ≡ neg group (radialDriftImpulse x)

    orientableToroidalFluxSurfaceReceipt : Set
    halfTurnFrameHolonomyReceipt : Set
    sameTrappedOrbitReceipt : (x : BounceState) → Set
    geometryReference : String

open MobiusFrameBounceGeometry public

pairedBounceRadialImpulseCancels :
  ∀ {group : DriftAdditiveGroup} →
  (geometry : MobiusFrameBounceGeometry group) →
  (x : BounceState geometry) →
  _⊕_ group
    (radialDriftImpulse geometry x)
    (radialDriftImpulse geometry (bounce geometry x))
  ≡ zero group
pairedBounceRadialImpulseCancels {group} geometry x
  with conjugateImpulseAntisymmetry geometry x
... | refl = rightInverse group (radialDriftImpulse geometry x)

record MobiusFrameBounceBoundary : Set where
  constructor mobius-frame-bounce-boundary
  field
    literalMobiusFluxSurfaceRequired : Bool
    literalMobiusFluxSurfaceRequiredIsFalse :
      literalMobiusFluxSurfaceRequired ≡ false

    halfTurnFrameHolonomyAloneProvesDriftCancellation : Bool
    halfTurnFrameHolonomyAloneProvesDriftCancellationIsFalse :
      halfTurnFrameHolonomyAloneProvesDriftCancellation ≡ false

    antisymmetricConjugateImpulsePaysPairedCancellation : Bool
    antisymmetricConjugateImpulsePaysPairedCancellationIsTrue :
      antisymmetricConjugateImpulsePaysPairedCancellation ≡ true

    pairedCancellationAloneProvesFiniteBetaEquilibrium : Bool
    pairedCancellationAloneProvesFiniteBetaEquilibriumIsFalse :
      pairedCancellationAloneProvesFiniteBetaEquilibrium ≡ false

canonicalMobiusFrameBounceBoundary : MobiusFrameBounceBoundary
canonicalMobiusFrameBounceBoundary =
  mobius-frame-bounce-boundary
    false refl
    false refl
    true refl
    false refl
