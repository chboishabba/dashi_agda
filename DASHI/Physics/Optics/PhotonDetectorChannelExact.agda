module DASHI.Physics.Optics.PhotonDetectorChannelExact where

-- Detector channel boundary for a physically instantiated optical encoder.
-- Ordering is explicit:
--   expected optical signal -> photon/electron statistics -> full-well/clamp
--   -> ADC quantisation -> recorded observation.
-- The type layer does not assume Gaussianity, independence, or unsaturated
-- operation; concrete stochastic laws remain producer obligations.

open import Agda.Primitive using (Set; Set₁)
open import Relation.Binary.PropositionalEquality using (_≡_)

record PhotonDetectorChannel
    (Scene ExpectedCounts Charge PixelData Recorded : Set) : Set₁ where
  field
    opticalExpectation : Scene → ExpectedCounts
    expectedCounts : Scene → ExpectedCounts
    expectationWeld : (x : Scene) → expectedCounts x ≡ opticalExpectation x

    photonSample : ExpectedCounts → Charge
    readDarkTransform : Charge → Charge
    fullWell : Charge → PixelData
    quantise : PixelData → Recorded

    recordedObservation : Scene → Recorded
    recordedObservationWeld :
      (x : Scene) →
      recordedObservation x ≡
      quantise (fullWell (readDarkTransform (photonSample (expectedCounts x))))

    -- Concrete physical/statistical authority fields.  These are deliberately
    -- separate so Poisson, QE/gain, read noise and ADC claims cannot be
    -- inferred merely from the existence of a processing chain.
    photonLawAuthority : Set
    photonLawReceipt : photonLawAuthority
    readDarkAuthority : Set
    readDarkReceipt : readDarkAuthority
    fullWellAuthority : Set
    fullWellReceipt : fullWellAuthority
    adcAuthority : Set
    adcReceipt : adcAuthority

open PhotonDetectorChannel public

record CensoredSaturationLikelihood
    {Scene ExpectedCounts Charge PixelData Recorded : Set}
    (D : PhotonDetectorChannel Scene ExpectedCounts Charge PixelData Recorded) : Set₁ where
  field
    Likelihood : Scene → Recorded → Set
    saturationHandledAsCensoredObservation : Set
    saturationReceipt : saturationHandledAsCensoredObservation

open CensoredSaturationLikelihood public
