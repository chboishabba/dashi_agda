module DASHI.Physics.Foundations.RFMutualCouplingManifoldExact where

open import DASHI.Core.Prelude

import DASHI.Core.SnowballAttributionProvenanceInvariantExact as Snowball
import DASHI.Physics.Foundations.RFMutualCouplingSourceAtlasExact as Sources
import DASHI.Physics.Foundations.RFComplexSmithPhasedArrayGoniometerExact as ComplexRF
import DASHI.Physics.Foundations.RFArrayManifoldPhasorCrossPollinationExact as Manifold
import DASHI.Physics.Foundations.PhasedArrayDirectionFindingExact as Array

------------------------------------------------------------------------
-- PORT-COUPLING OBSERVATION
--
-- S-parameter coupling belongs to the RF-port observation lane.  The finite
-- constructors below retain the distinction between self-reflection and
-- inter-element coupling without pretending to reproduce a full network.
------------------------------------------------------------------------

data CouplingObservationCoordinate : Set where
  selfReflectionCoordinate : CouplingObservationCoordinate
  interElementCouplingCoordinate : CouplingObservationCoordinate
  activeReflectionCoordinate : CouplingObservationCoordinate

selfReflectionIsNotMutualCoupling :
  selfReflectionCoordinate ≡ interElementCouplingCoordinate → ⊥
selfReflectionIsNotMutualCoupling ()

record MutualCouplingObservationReceipt : Set where
  constructor mutual-coupling-observation-receipt
  field
    nalumakkalSourceRetained :
      Snowball.SourceRoleSnowballReceipt Sources.nalumakkalActiveArrayPrimary

    wangSourceRetained :
      Snowball.SourceRoleSnowballReceipt Sources.wangMutualCouplingPrimary

    smithCoordinateReceiptRetained :
      ComplexRF.SmithChartCoordinateReceipt

    selfAndMutualTermsRemainDistinct :
      selfReflectionCoordinate ≡ interElementCouplingCoordinate → ⊥

    couplingCanModifyActiveReflection : Bool
    couplingCanModifyActiveReflectionIsTrue :
      couplingCanModifyActiveReflection ≡ true

    couplingObservationIsBearing : Bool
    couplingObservationIsBearingIsFalse :
      couplingObservationIsBearing ≡ false

open MutualCouplingObservationReceipt public

canonicalMutualCouplingObservationReceipt :
  MutualCouplingObservationReceipt
canonicalMutualCouplingObservationReceipt =
  mutual-coupling-observation-receipt
    (Snowball.canonicalSourceRoleSnowballReceipt Sources.nalumakkalActiveArrayPrimary)
    (Snowball.canonicalSourceRoleSnowballReceipt Sources.wangMutualCouplingPrimary)
    ComplexRF.canonicalSmithChartCoordinateReceipt
    selfReflectionIsNotMutualCoupling
    true refl
    false refl

------------------------------------------------------------------------
-- ACTIVE / EMBEDDED ELEMENT RESPONSE
--
-- The source literature motivates a corrected element response in the array
-- environment.  DASHI records only the information-role distinction.
------------------------------------------------------------------------

data ElementResponseModel : Set where
  isolatedElementResponse : ElementResponseModel
  activeArrayElementResponse : ElementResponseModel
  embeddedElementResponse : ElementResponseModel

isolatedIsNotEmbedded :
  isolatedElementResponse ≡ embeddedElementResponse → ⊥
isolatedIsNotEmbedded ()

record ActiveElementResponseReceipt : Set where
  constructor active-element-response-receipt
  field
    mathworksEmbeddedReferenceRetained :
      Snowball.SourceRoleSnowballReceipt Sources.mathworksEmbeddedElementReference

    isolatedAndEmbeddedResponsesRemainDistinct :
      isolatedElementResponse ≡ embeddedElementResponse → ⊥

    embeddedResponseRetainsCouplingEffect : Bool
    embeddedResponseRetainsCouplingEffectIsTrue :
      embeddedResponseRetainsCouplingEffect ≡ true

    activeResponseCanDependOnPortCoupling : Bool
    activeResponseCanDependOnPortCouplingIsTrue :
      activeResponseCanDependOnPortCoupling ≡ true

    correctedElementResponseEqualsExactHardware : Bool
    correctedElementResponseEqualsExactHardwareIsFalse :
      correctedElementResponseEqualsExactHardware ≡ false

open ActiveElementResponseReceipt public

canonicalActiveElementResponseReceipt : ActiveElementResponseReceipt
canonicalActiveElementResponseReceipt =
  active-element-response-receipt
    (Snowball.canonicalSourceRoleSnowballReceipt Sources.mathworksEmbeddedElementReference)
    isolatedIsNotEmbedded
    true refl
    true refl
    false refl

------------------------------------------------------------------------
-- COUPLING-CORRECTED MANIFOLD
--
-- Port-level coupling can motivate refinement of the effective element/array
-- response, which in turn may refine the manifold consumed by beamforming or
-- direction-finding.  It does not itself produce an angular answer.
------------------------------------------------------------------------

data ManifoldCorrectionCoordinate : Set where
  idealizedManifoldCoordinate : ManifoldCorrectionCoordinate
  couplingCorrectionCoordinate : ManifoldCorrectionCoordinate
  embeddedPatternCorrectionCoordinate : ManifoldCorrectionCoordinate

idealizedIsNotCouplingCorrected :
  idealizedManifoldCoordinate ≡ couplingCorrectionCoordinate → ⊥
idealizedIsNotCouplingCorrected ()

record CouplingCorrectedManifoldReceipt : Set where
  constructor coupling-corrected-manifold-receipt
  field
    arrayManifoldReceiptRetained : Manifold.ArrayManifoldReceipt

    couplingObservationRetained : MutualCouplingObservationReceipt

    activeElementResponseRetained : ActiveElementResponseReceipt

    manifoldCorrectionCoordinateDistinct :
      idealizedManifoldCoordinate ≡ couplingCorrectionCoordinate → ⊥

    mutualCouplingMayRequireManifoldRefinement : Bool
    mutualCouplingMayRequireManifoldRefinementIsTrue :
      mutualCouplingMayRequireManifoldRefinement ≡ true

    correctedManifoldMayFeedAngularConsumer : Bool
    correctedManifoldMayFeedAngularConsumerIsTrue :
      correctedManifoldMayFeedAngularConsumer ≡ true

    couplingCorrectionAutomaticallyImprovesEveryConsumer : Bool
    couplingCorrectionAutomaticallyImprovesEveryConsumerIsFalse :
      couplingCorrectionAutomaticallyImprovesEveryConsumer ≡ false

open CouplingCorrectedManifoldReceipt public

canonicalCouplingCorrectedManifoldReceipt :
  CouplingCorrectedManifoldReceipt
canonicalCouplingCorrectedManifoldReceipt =
  coupling-corrected-manifold-receipt
    Manifold.canonicalArrayManifoldReceipt
    canonicalMutualCouplingObservationReceipt
    canonicalActiveElementResponseReceipt
    idealizedIsNotCouplingCorrected
    true refl
    true refl
    false refl

------------------------------------------------------------------------
-- FIREWALL
------------------------------------------------------------------------

record MutualCouplingFirewall : Set where
  constructor mutual-coupling-firewall
  field
    sParameterCouplingEqualsBearing : Bool
    sParameterCouplingEqualsBearingIsFalse :
      sParameterCouplingEqualsBearing ≡ false

    activeReflectionEqualsArrayManifold : Bool
    activeReflectionEqualsArrayManifoldIsFalse :
      activeReflectionEqualsArrayManifold ≡ false

    embeddedPatternEqualsEmitterIdentity : Bool
    embeddedPatternEqualsEmitterIdentityIsFalse :
      embeddedPatternEqualsEmitterIdentity ≡ false

    couplingCorrectionDeterminesExactEmitterWorld : Bool
    couplingCorrectionDeterminesExactEmitterWorldIsFalse :
      couplingCorrectionDeterminesExactEmitterWorld ≡ false

    couplingEvidenceIdentifiesExactArrayHardware : Bool
    couplingEvidenceIdentifiesExactArrayHardwareIsFalse :
      couplingEvidenceIdentifiesExactArrayHardware ≡ false

    couplingCapabilityCreatesOperationalAuthority : Bool
    couplingCapabilityCreatesOperationalAuthorityIsFalse :
      couplingCapabilityCreatesOperationalAuthority ≡ false

open MutualCouplingFirewall public

canonicalMutualCouplingFirewall : MutualCouplingFirewall
canonicalMutualCouplingFirewall =
  mutual-coupling-firewall
    false refl
    false refl
    false refl
    false refl
    false refl
    false refl

------------------------------------------------------------------------
-- EXISTING ANGULAR NON-INJECTIVITY REMAINS TERMINAL.
------------------------------------------------------------------------

arrayBearingStillDoesNotDetermineExactEmitterWorld :
  ¬ Array.ArrayBearingDeterminesExactEmitterWorld
arrayBearingStillDoesNotDetermineExactEmitterWorld =
  Array.arrayBearingDoesNotDetermineExactEmitterWorld
