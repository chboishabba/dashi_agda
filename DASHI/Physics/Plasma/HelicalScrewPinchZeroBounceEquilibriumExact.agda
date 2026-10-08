module DASHI.Physics.Plasma.HelicalScrewPinchZeroBounceEquilibriumExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

import DASHI.Physics.Plasma.ZeroBouncePopulationExact as ZeroBounce

------------------------------------------------------------------------
-- HELICAL SCREW-PINCH ZERO-BOUNCE EQUILIBRIUM SEED
--
-- Ideal periodic-cylinder seed:
--   B = B_theta e_theta + B_z e_z,
-- with constant B_theta and B_z on the declared annulus.
-- Then |B| is constant along field lines, so the adiabatic mirror force is
-- zero.  Ampere plus radial MHD balance gives
--   J_z = B_theta / (mu0 r)
--   dp/dr = - B_theta^2 / (mu0 r)
-- and therefore J x B = grad p in the radial direction.
--
-- This is an exact equilibrium-shaped seed on a periodic cylinder, not yet an
-- embedded finite-aspect-ratio torus.
------------------------------------------------------------------------

record HelicalScrewPinchZeroBounceSeed
    (population : ZeroBounce.DeclaredParticlePopulation) : Set₁ where
  constructor helical-screw-pinch-zero-bounce-seed
  field
    periodicCylinderReceipt : Set
    constantAzimuthalFieldReceipt : Set
    constantAxialFieldReceipt : Set
    divergenceFreeFieldReceipt : Set
    constantMagneticMagnitudeReceipt : Set
    zeroParallelMagneticMagnitudeGradientReceipt : Set
    zeroMagneticMirrorForceReceipt : Set
    zeroBounce : ZeroBounce.ZeroBounceReceipt population

    ampereCurrentReceipt : Set
    radialPressureGradientReceipt : Set
    radialLorentzForceReceipt : Set
    mhdForceBalanceReceipt : Set
    nestedCylindricalFluxSurfaceReceipt : Set

    fieldLineHelicityReceipt : Set
    finiteBetaReceipt : Set
    seedReference : String

open HelicalScrewPinchZeroBounceSeed public

record HelicalScrewPinchBoundary : Set where
  constructor helical-screw-pinch-boundary
  field
    zeroMirrorCompatibleWithNontrivialMHDForceBalance : Bool
    zeroMirrorCompatibleWithNontrivialMHDForceBalanceIsTrue :
      zeroMirrorCompatibleWithNontrivialMHDForceBalance ≡ true

    periodicCylinderAlreadyEqualsEmbeddedToroidalReactor : Bool
    periodicCylinderAlreadyEqualsEmbeddedToroidalReactorIsFalse :
      periodicCylinderAlreadyEqualsEmbeddedToroidalReactor ≡ false

    toroidalBendingMayReintroduceMagnitudeVariation : Bool
    toroidalBendingMayReintroduceMagnitudeVariationIsTrue :
      toroidalBendingMayReintroduceMagnitudeVariation ≡ true

    curvatureAndFiniteOrbitWidthRemainOpen : Bool
    curvatureAndFiniteOrbitWidthRemainOpenIsTrue :
      curvatureAndFiniteOrbitWidthRemainOpen ≡ true

canonicalHelicalScrewPinchBoundary : HelicalScrewPinchBoundary
canonicalHelicalScrewPinchBoundary =
  helical-screw-pinch-boundary
    true refl
    false refl
    true refl
    true refl
