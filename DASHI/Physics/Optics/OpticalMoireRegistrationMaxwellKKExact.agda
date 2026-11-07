module DASHI.Physics.Optics.OpticalMoireRegistrationMaxwellKKExact where

-- Optical moire specializes the existing typed relative-registration carrier.
-- The Jones/Stokes/Maxwell maps below are selected physical inputs, not
-- automatically identified with either a graphene band or a KK reduction.

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool)
import DASHI.Moonshine.TwistronicsRelativeRegistrationComparatorExact as Twist

record OpticalSource (Jones Registration Stokes : Set) : Set₁ where
  constructor optical-source
  field
    jonesOverlay : Twist.OverlayState Jones Registration → Jones
    stokesObserver : Jones → Stokes
open OpticalSource public

opticalObserver :
  {Jones Registration Stokes : Set} →
  OpticalSource Jones Registration Stokes →
  Twist.RelativeRegistrationSystem Jones Registration Stokes
opticalObserver source =
  Twist.relative-registration-system
    (λ state → stokesObserver source (jonesOverlay source state))

opticalChangePreservesFirst :
  {Jones Registration : Set} →
  (state : Twist.OverlayState Jones Registration) →
  (rotation : Registration) →
  Twist.leftMicroscopic (Twist.changeRegistration state rotation)
    ≡ Twist.leftMicroscopic state
opticalChangePreservesFirst =
  Twist.changeRegistrationPreservesLeft

opticalChangePreservesSecond :
  {Jones Registration : Set} →
  (state : Twist.OverlayState Jones Registration) →
  (rotation : Registration) →
  Twist.rightMicroscopic (Twist.changeRegistration state rotation)
    ≡ Twist.rightMicroscopic state
opticalChangePreservesSecond =
  Twist.changeRegistrationPreservesRight

-- A physically evidenced change of optical Stokes observation at fixed
-- constituent Jones fields certifies strict refinement. No postulate.
opticalRegistrationStrictlyRefines :
  {Jones Registration Stokes : Set} →
  (source : OpticalSource Jones Registration Stokes) →
  Twist.RegistrationSensitiveWitness (opticalObserver source) →
  Twist.RelativeRegistrationSystem Jones Registration Stokes →
  Set
opticalRegistrationStrictlyRefines source witness _ =
  Twist.relativeRegistrationCanChangeEffectiveObservation
    (opticalObserver source) witness

opticalRegistrationSensitivityCertified :
  {Jones Registration Stokes : Set} →
  (source : OpticalSource Jones Registration Stokes) →
  (witness : Twist.RegistrationSensitiveWitness (opticalObserver source)) →
  opticalRegistrationStrictlyRefines source witness (opticalObserver source)
opticalRegistrationSensitivityCertified source witness =
  Twist.relativeRegistrationCanChangeEffectiveObservation
    (opticalObserver source) witness

-- The electromagnetic and KK channels are separate selected consumers.
-- They cannot be discharged merely by a moire-registration theorem.
record SameSourcePhysicalOptics
    (Jones Registration Stokes MaxwellField KKMetric : Set) : Set₁ where
  field
    optical : OpticalSource Jones Registration Stokes
    maxwellReconstruction : Jones → MaxwellField
    kkReducedMetric : KKMetric
    maxwellPhysicalCalibration : MaxwellField → Set
    stokesPhysicalCalibration : Stokes → Set
    metricIsMeasuredObserverMetric : KKMetric → Set
    sourceMatchesEMAndKK : MaxwellField → KKMetric → Set

-- No inhabited SameSourcePhysicalOptics instance is asserted here.
