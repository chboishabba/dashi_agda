module DASHI.Core.ApplicationCapabilityDominantChartCompressionExact where

open import DASHI.Core.Prelude

import DASHI.Core.DominantChartEpistemicCompressionExact as Compression
import DASHI.Core.IntersectionalNonFactorability as INF
import DASHI.Core.ApplicationTransformationCapabilityBidiExact as Application

------------------------------------------------------------------------
-- SCIENTIFIC CONTROL: SAME PUBLIC SURFACE != SAME OPERATIONAL CAPABILITY
--
-- Synthetic finite witness.  It does not assert secrecy, uniqueness or event
-- causation for any named person/programme; it only instantiates the generic
-- observer-adequacy theorem already stated by the application-capability owner.
------------------------------------------------------------------------

data ApplicationState : Set where
  publicOnlyState : ApplicationState
  calibratedApplicationState : ApplicationState

data PublicScienceSurface : Set where
  samePublishedPhysics : PublicScienceSurface

data OperationalCapabilityState : Set where
  unreconstructedCapability : OperationalCapabilityState
  reconstructedCapability : OperationalCapabilityState

publicScienceObserver : ApplicationState → PublicScienceSurface
publicScienceObserver _ = samePublishedPhysics

operationalCapability : ApplicationState → OperationalCapabilityState
operationalCapability publicOnlyState = unreconstructedCapability
operationalCapability calibratedApplicationState = reconstructedCapability

capabilityDiffers :
  operationalCapability publicOnlyState
  ≡ operationalCapability calibratedApplicationState → ⊥
capabilityDiffers ()

publicScienceCapabilityWitness :
  INF.NonFactorabilityWitness publicScienceObserver operationalCapability
publicScienceCapabilityWitness =
  INF.nonFactorabilityWitness
    publicOnlyState calibratedApplicationState refl capabilityDiffers

publicScienceCompression :
  Compression.ProjectionInadequacyReceipt
    publicScienceObserver operationalCapability
publicScienceCompression =
  Compression.projection-inadequacy-receipt
    Compression.administrativeClassificationCompression
    "public governing-science / published-architecture surface"
    "validated calibrated operational-capability consumer"
    "same public governing science can coexist with absent or reconstructed application capability"
    publicScienceCapabilityWitness
    true refl
    false refl
    false refl
    false refl

publicScienceCannotCarryOperationalCapability :
  INF.FactorsThrough publicScienceObserver operationalCapability → ⊥
publicScienceCannotCarryOperationalCapability =
  Compression.projectionCannotFactorTarget publicScienceCompression

publicScienceRelabellingCannotCreateCapability :
  ∀ {Recharted : Set} →
  (rechart : PublicScienceSurface → Recharted) →
  INF.FactorsThrough
    (λ state → rechart (publicScienceObserver state))
    operationalCapability → ⊥
publicScienceRelabellingCannotCreateCapability =
  Compression.projectionCannotBeRepairedByPostcomposition publicScienceCompression

applicationBoundaryStillBlocksPublicPhysicsPromotion :
  Application.publicPhysicsImpliesPublicCapability
    Application.canonicalApplicationTransformationBoundary ≡ false
applicationBoundaryStillBlocksPublicPhysicsPromotion = refl

applicationBoundaryStillBlocksEquationIdentityPromotion :
  Application.sameEquationsImpliesSameCapability
    Application.canonicalApplicationTransformationBoundary ≡ false
applicationBoundaryStillBlocksEquationIdentityPromotion = refl

record ApplicationCompressionBoundary : Set where
  constructor application-compression-boundary
  field
    projectionFailureProvesUniqueHumanHolder : Bool
    projectionFailureProvesUniqueHumanHolderIsFalse :
      projectionFailureProvesUniqueHumanHolder ≡ false
    projectionFailureProvesTargetingOrEventCausation : Bool
    projectionFailureProvesTargetingOrEventCausationIsFalse :
      projectionFailureProvesTargetingOrEventCausation ≡ false
    repairRequiresApplicationSpecificInformation : Bool
    repairRequiresApplicationSpecificInformationIsTrue :
      repairRequiresApplicationSpecificInformation ≡ true

canonicalApplicationCompressionBoundary : ApplicationCompressionBoundary
canonicalApplicationCompressionBoundary =
  application-compression-boundary false refl false refl true refl
