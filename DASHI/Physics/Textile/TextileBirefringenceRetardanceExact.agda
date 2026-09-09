module DASHI.Physics.Textile.TextileBirefringenceRetardanceExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

import DASHI.Physics.Textile.TextilePolarisationTransportExact as Polarisation
import DASHI.Physics.Textile.TextileOpticalTransportBridgeExact as Optical
import DASHI.Topology.TextileStitchHyperfabricExact as Stitch

------------------------------------------------------------------------
-- PROVENANCE / SCOPE
--
-- Kent B. Rochford, "Polarization and Polarimetry", NIST (2001), includes
-- birefringence, diattenuation, retardance, and Jones/Mueller methods.
-- B. D. Guenther, Modern Optics, chapter "Anisotropy" (2015), describes
-- birefringent media as having refractive index dependent on propagation
-- direction and requiring tensor optical response.
--
-- This module records a conditional retardance realization.  It does not
-- assert that an arbitrary textile fiber is birefringent or uniaxial.
------------------------------------------------------------------------

nistPolarimetryTitle : String
nistPolarimetryTitle = "Polarization and Polarimetry"

anisotropyReferenceDOI : String
anisotropyReferenceDOI = "10.1093/acprof:oso/9780198738770.003.0013"

record TextileBirefringenceCalibration (Scalar : Set) : Set₁ where
  constructor textile-birefringence-calibration
  field
    ordinaryRefractiveIndex : Scalar
    extraordinaryRefractiveIndex : Scalar
    opticalPathLength : Scalar
    wavelength : Scalar
    birefringence : Scalar
    retardanceLength : Scalar
    retardancePhase : Scalar

    subtract : Scalar → Scalar → Scalar
    multiply : Scalar → Scalar → Scalar
    divide : Scalar → Scalar → Scalar

    birefringenceLaw :
      birefringence
      ≡ subtract extraordinaryRefractiveIndex ordinaryRefractiveIndex

    retardanceLengthLaw :
      retardanceLength
      ≡ multiply birefringence opticalPathLength

    retardancePhaseLaw :
      retardancePhase
      ≡ divide retardanceLength wavelength

open TextileBirefringenceCalibration public

record BirefringentTextilePolarisationRealisation
    {OpticalState Illumination OpticalObserver Radiance Scalar : Set}
    {topology : Stitch.StitchState}
    (model : Optical.TextileOpticalModel
      OpticalState Illumination OpticalObserver Radiance topology)
    (algebra : Polarisation.StokesMuellerAlgebra Scalar) : Set₁ where
  constructor birefringent-textile-polarisation-realisation
  field
    calibration : TextileBirefringenceCalibration Scalar
    polarisationReceipt :
      Polarisation.TextilePolarisationReceipt model algebra
    calibratedMuellerResponse : Polarisation.MuellerMatrix Scalar
    responseMatchesPolarisationReceipt :
      calibratedMuellerResponse
      ≡ Polarisation.textileMuellerResponse polarisationReceipt

open BirefringentTextilePolarisationRealisation public

------------------------------------------------------------------------
-- Non-promotion boundaries.
------------------------------------------------------------------------

data EveryTextileFiberIsBirefringent : Set where

everyTextileFiberIsNotDeclaredBirefringent :
  EveryTextileFiberIsBirefringent → ⊥
everyTextileFiberIsNotDeclaredBirefringent ()

data BirefringenceAloneDeterminesIridescentAppearance : Set where

birefringenceAloneDoesNotDetermineIridescentAppearance :
  BirefringenceAloneDeterminesIridescentAppearance → ⊥
birefringenceAloneDoesNotDetermineIridescentAppearance ()

data RetardanceScalarDeterminesFullPolarisationField : Set where

retardanceScalarDoesNotDetermineFullPolarisationField :
  RetardanceScalarDeterminesFullPolarisationField → ⊥
retardanceScalarDoesNotDetermineFullPolarisationField ()
