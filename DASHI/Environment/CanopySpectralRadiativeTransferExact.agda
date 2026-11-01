module DASHI.Environment.CanopySpectralRadiativeTransferExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

import DASHI.Environment.PhotosyntheticLightTransportCrossPollinationExact as Photo

------------------------------------------------------------------------
-- CANOPY SPECTRAL RADIATIVE-TRANSFER INTERFACE
--
-- McCree's action-spectrum work motivates retaining wavelength-resolved
-- incident/absorbed photon fields; de Pury & Farquhar motivate retaining the
-- distinction between sunlit and shaded canopy fractions rather than reducing
-- a canopy to one homogeneous big leaf.
--
-- This owner does NOT define another photosynthetic photon/interception model.
-- It is a canopy-level producer that must compile into the canonical
-- PhotosyntheticLightTransportCrossPollinationExact owner.
------------------------------------------------------------------------

mccreeActionSpectrumDOI : String
mccreeActionSpectrumDOI = "10.1016/0002-1571(71)90022-7"

dePuryFarquharCanopyDOI : String
dePuryFarquharCanopyDOI = "10.1111/j.1365-3040.1997.00094.x"

data CanopyLeafClass : Set where
  sunlitLeaf : CanopyLeafClass
  shadedLeaf : CanopyLeafClass
  applicationSpecificLeafClass : CanopyLeafClass

record SpectralCanopyRadiationModel
    (Wavelength Direction CanopyPoint PhotonFlux : Set) : Set₁ where
  constructor spectral-canopy-radiation-model
  field
    incidentPhotonField : Wavelength → Direction → CanopyPoint → PhotonFlux
    absorbedPhotonField : Wavelength → Direction → CanopyPoint → PhotonFlux
    leafClassAt : CanopyPoint → CanopyLeafClass
    leafAreaGeometryReference : String
    leafAngleDistributionReference : String
    directDiffusePartitionReference : String
    scatteringAndAbsorptionReference : String
    boundaryIlluminationReference : String
    solverNameOrMethod : String
    solverVersionOrCommit : String
    numericalArtifactDigest : String

open SpectralCanopyRadiationModel public

record CanopyToPhotosyntheticPhotonFieldWeld
    {Wavelength Direction CanopyPoint PhotonFlux : Set}
    (canopy : SpectralCanopyRadiationModel
      Wavelength Direction CanopyPoint PhotonFlux)
    (field : Photo.PhotosyntheticPhotonField CanopyPoint Wavelength PhotonFlux)
    (interception : Photo.LeafLightInterceptionReceipt field) : Set₁ where
  constructor canopy-to-photosynthetic-photon-field-weld
  field
    directionalReductionReference : String
    canopyIncidentToPhotonFieldReference : String
    canopyAbsorbedToPhotonFieldReference : String
    canopyPointIsLeafPointReference : String
    sunlitShadedClassificationReference : String
    sameGeometryReference : String
    sameTimeSupportReference : String
    sameSpectralCalibrationReference : String
    numericalCanopyResidualReference : String

open CanopyToPhotosyntheticPhotonFieldWeld public

record CanopyRadiativeTransferBoundary : Set where
  constructor canopy-radiative-transfer-boundary
  field
    wavelengthIntegratedPARDeterminesSpectrum : Bool
    wavelengthIntegratedPARDeterminesSpectrumIsFalse :
      wavelengthIntegratedPARDeterminesSpectrum ≡ false
    canopyMeanIrradianceDeterminesEveryLeaf : Bool
    canopyMeanIrradianceDeterminesEveryLeafIsFalse :
      canopyMeanIrradianceDeterminesEveryLeaf ≡ false
    radiativeTransferAloneDeterminesAssimilation : Bool
    radiativeTransferAloneDeterminesAssimilationIsFalse :
      radiativeTransferAloneDeterminesAssimilation ≡ false
    sunlitAndShadedStatesRemainDistinct : Bool
    sunlitAndShadedStatesRemainDistinctIsTrue :
      sunlitAndShadedStatesRemainDistinct ≡ true
    canopyProducerMustCompileIntoCanonicalPhotosyntheticOwner : Bool
    canopyProducerMustCompileIntoCanonicalPhotosyntheticOwnerIsTrue :
      canopyProducerMustCompileIntoCanonicalPhotosyntheticOwner ≡ true

canonicalCanopyRadiativeTransferBoundary : CanopyRadiativeTransferBoundary
canonicalCanopyRadiativeTransferBoundary =
  canopy-radiative-transfer-boundary false refl false refl false refl true refl true refl
