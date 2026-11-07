module DASHI.Physics.Optics.OpticalMoireRegistrationMaxwellKKExact where

-- Optical moire specializes the existing typed relative-registration carrier.
-- The Jones/Stokes/Maxwell maps below are selected physical inputs, not
-- automatically identified with either a graphene band or a KK reduction.

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool)
import DASHI.Moonshine.TwistronicsRelativeRegistrationComparatorExact as Twist
import DASHI.Core.AttributedSourceCore as Attribution
import DASHI.Core.ConsumerGuidedReopenableRefinementExact as Refine

-- External research: Dev and Shen, Light: Science & Applications 15, 396
-- (2026). Source equation, experimental data, and physical claims remain
-- theirs. No attribution imports theorem authority into this module.
devShen2026 : Attribution.AttributedSource
devShen2026 =
  Attribution.mkDOISource
    "Vasu Dev and Yijie Shen"
    "Freespace twistronics: moiré structured light for optical supertopologies"
    "Light: Science & Applications 15, article 396"
    "2026"
    "10.1038/s41377-026-02533-w"
    "https://doi.org/10.1038/s41377-026-02533-w"
    Attribution.academicArticleSource
    "Original Gaussian-ring Fourier-source Eq(1), optical moiré supertopologies, measurements and propagation; DASHI only specializes a pre-existing relative-registration abstraction"
    Attribution.publicAttribution

opticalMoireSourceAtlas : Attribution.AttributedSourceAtlas
opticalMoireSourceAtlas =
  Attribution.mkSourceAtlas
    "Dev-Shen 2026 optical moiré source atlas"
    "DASHI.Physics.Optics.OpticalMoireRegistrationMaxwellKKExact"
    (devShen2026 ∷ [])
    "Citations are non-promoting; exact source Eq(1) and synthetic numerical replay are separate from acquisition of measured datasets"


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

-- Reuse the *actual strict-refinement certificate*, not merely its
-- proposition. It is conditional on a registration-sensitive witness.
opticalRegistrationStrictCertificate :
  {Jones Registration Stokes : Set} →
  (source : OpticalSource Jones Registration Stokes) →
  (witness : Twist.RegistrationSensitiveWitness (opticalObserver source)) →
  Refine.StrictProjectionRefinement
    Twist.forgetRegistration Twist.retainRegistration
opticalRegistrationStrictCertificate source witness =
  Twist.registrationStrictlyRefinesMicroscopicPair
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
