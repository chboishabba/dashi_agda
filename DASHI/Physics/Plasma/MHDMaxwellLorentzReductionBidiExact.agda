module DASHI.Physics.Plasma.MHDMaxwellLorentzReductionBidiExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

import DASHI.Physics.Laws.PhysicalLawAtlas as Atlas
import DASHI.Physics.Electromagnetism.U1ElectromagneticApplicationExact as EM

------------------------------------------------------------------------
-- LAW-STACK BIDI
--
-- Magnetized-plasma modelling uses several non-identical layers:
--   Maxwell/U(1) field evolution + Lorentz coupling
--   -> fluid closure / MHD effective law
--   -> non-ideal generalized-Ohm terms where frozen-in evolution breaks
--   -> kinetic/two-fluid producers when the MHD closure is insufficient.
------------------------------------------------------------------------

record MagnetizedPlasmaLawStack : Set₁ where
  constructor magnetized-plasma-law-stack
  field
    electromagneticReduction : EM.U1ApplicationReduction

    maxwellLaw : Atlas.CanonicalPhysicalLaw
    maxwellLawIsHomogeneousMaxwell :
      maxwellLaw ≡ Atlas.homogeneousMaxwellLaw

    forceLaw : Atlas.CanonicalPhysicalLaw
    forceLawIsLorentz : forceLaw ≡ Atlas.lorentzForceLaw

    fluidLaw : Atlas.CanonicalPhysicalLaw
    fluidLawIsMHD : fluidLaw ≡ Atlas.magnetohydrodynamicLaw

    generalizedOhmReference : String
    kineticClosureReference : String
    validityRegimeReference : String

open MagnetizedPlasmaLawStack public

record LawStackBoundary : Set where
  constructor law-stack-boundary
  field
    maxwellLawIsMHD : Bool
    maxwellLawIsMHDIsFalse : maxwellLawIsMHD ≡ false

    lorentzForceLawIsMHD : Bool
    lorentzForceLawIsMHDIsFalse : lorentzForceLawIsMHD ≡ false

    idealMHDContainsAllCollisionlessReconnectionMicrophysics : Bool
    idealMHDContainsAllCollisionlessReconnectionMicrophysicsIsFalse :
      idealMHDContainsAllCollisionlessReconnectionMicrophysics ≡ false

    mhdIsEffectivePlasmaLawInAtlas : Bool
    mhdIsEffectivePlasmaLawInAtlasIsTrue :
      mhdIsEffectivePlasmaLawInAtlas ≡ true

    kineticClosureCanBeRequiredBeyondMHD : Bool
    kineticClosureCanBeRequiredBeyondMHDIsTrue :
      kineticClosureCanBeRequiredBeyondMHD ≡ true

canonicalLawStackBoundary : LawStackBoundary
canonicalLawStackBoundary =
  law-stack-boundary false refl false refl false refl true refl true refl

------------------------------------------------------------------------
-- BIDI acquisition rule: a fluid/MHD receipt may discharge the effective
-- continuum layer, but cannot fill a kinetic or generalized-Ohm producer.
------------------------------------------------------------------------

record LawStackBidiObligations : Set where
  constructor law-stack-bidi-obligations
  field
    mhdReceiptDischargesMHDLayer : Bool
    mhdReceiptDischargesMHDLayerIsTrue :
      mhdReceiptDischargesMHDLayer ≡ true

    mhdReceiptDischargesKineticLayer : Bool
    mhdReceiptDischargesKineticLayerIsFalse :
      mhdReceiptDischargesKineticLayer ≡ false

    maxwellReceiptDischargesFusionReactionRate : Bool
    maxwellReceiptDischargesFusionReactionRateIsFalse :
      maxwellReceiptDischargesFusionReactionRate ≡ false

canonicalLawStackBidiObligations : LawStackBidiObligations
canonicalLawStackBidiObligations =
  law-stack-bidi-obligations true refl false refl false refl
