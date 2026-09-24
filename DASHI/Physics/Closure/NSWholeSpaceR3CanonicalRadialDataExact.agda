module DASHI.Physics.Closure.NSWholeSpaceR3CanonicalRadialDataExact where

------------------------------------------------------------------------
-- A / CANONICAL RADIAL DATA FROM THE PHYSICAL OUTPUT FREQUENCY
--
-- The radial low-frequency compilers use
--
--   q = radiusSquared.
--
-- The physical Fourier stack already owns the literal quantity
--
--   |xi|^2 = frequencyNormSquared xi.
--
-- There is no reason to leave their identification as an external same-object
-- authority.  Given positive viscosity and a punctured output frequency, build
-- PositiveViscosityRadiusSquare definitionally with
--
--   radiusSquared = |xi|^2.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)

import Real as BishopReal
import RealProperties as BishopP

import DASHI.Physics.Closure.NSTriadKNEuclideanSignedFrequencyCarrierRealizationExact as Euclidean
import DASHI.Physics.Closure.NSTriadKNEuclideanViscousHeatRateExact as Heat
import DASHI.Physics.Closure.NSWholeSpaceR3RadialOriginCancellationExact as Radial

canonicalRadialData :
  Heat.PositiveViscosity →
  Heat.PuncturedEuclideanFrequency →
  Radial.PositiveViscosityRadiusSquare
canonicalRadialData fluid point =
  Radial.positive-viscosity-radius-square
    (Heat.viscosity fluid)
    (Heat.frequencyNormSquared (Heat.frequency point))
    (Heat.viscosityPositive fluid)
    (Heat.normSquaredPositive point)

canonicalRadialViscosityExact :
  (fluid : Heat.PositiveViscosity) →
  (point : Heat.PuncturedEuclideanFrequency) →
  Radial.viscosity (canonicalRadialData fluid point)
  ≡
  Heat.viscosity fluid
canonicalRadialViscosityExact fluid point = refl

canonicalRadialQExact :
  (fluid : Heat.PositiveViscosity) →
  (point : Heat.PuncturedEuclideanFrequency) →
  Radial.radiusSquared (canonicalRadialData fluid point)
  ≡
  Heat.frequencyNormSquared (Heat.frequency point)
canonicalRadialQExact fluid point = refl

canonicalRadialQEquivalent :
  (fluid : Heat.PositiveViscosity) →
  (point : Heat.PuncturedEuclideanFrequency) →
  BishopReal._≃_
    (Radial.radiusSquared (canonicalRadialData fluid point))
    (Heat.frequencyNormSquared (Heat.frequency point))
canonicalRadialQEquivalent fluid point =
  BishopP.≃-refl
    (Heat.frequencyNormSquared (Heat.frequency point))

canonicalRadialHeatRateExact :
  (fluid : Heat.PositiveViscosity) →
  (point : Heat.PuncturedEuclideanFrequency) →
  Radial.heatRate (canonicalRadialData fluid point)
  ≡
  Heat.viscousHeatRate fluid (Heat.frequency point)
canonicalRadialHeatRateExact fluid point = refl

canonicalRadialDataClosed : Bool
canonicalRadialDataClosed = true

radialQSameObjectAuthorityRequired : Bool
radialQSameObjectAuthorityRequired = false

originIncludedInReciprocalDomain : Bool
originIncludedInReciprocalDomain = false

clayPromotion : Bool
clayPromotion = false

canonicalRadialDataClosedIsTrue :
  canonicalRadialDataClosed ≡ true
canonicalRadialDataClosedIsTrue = refl

radialQSameObjectAuthorityRequiredIsFalse :
  radialQSameObjectAuthorityRequired ≡ false
radialQSameObjectAuthorityRequiredIsFalse = refl

clayPromotionIsFalse : clayPromotion ≡ false
