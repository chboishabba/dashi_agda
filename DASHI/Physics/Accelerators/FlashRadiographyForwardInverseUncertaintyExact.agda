module DASHI.Physics.Accelerators.FlashRadiographyForwardInverseUncertaintyExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

-- Generic high-energy / flash-radiography forward-model and inversion owner.
-- Sources:
-- "A stochastic approach to quantifying the blur with uncertainty estimation for high-energy X-ray imaging systems",
-- Inverse Problems in Science and Engineering (2015), DOI 10.1080/17415977.2015.1046859.
-- Walker, Friou, Ginsburger, "High-energy X-ray spectrum reconstruction: solving the inverse problem from optimized multi-material transmission measurements",
-- Frontiers in Physics 11 (2023) 1257548, DOI 10.3389/fphy.2023.1257548.
-- Wei et al., "Uncertainty Quantification of Density Reconstruction Using MCMC Method in High-Energy X-ray Radiography",
-- Commun. Comput. Phys. 27 (2020) 1485-1504, DOI 10.4208/cicp.OA-2019-0060.
-- Li et al., "Uncertainty Quantification Enforced Flash Radiography Reconstruction by Two-Level Efficient MCMC",
-- IEEE Trans. Image Process. 30 (2021) 7184-7199, DOI 10.1109/TIP.2021.3101929.

data ForwardCoordinate : Set where
  sourceSpectrum : ForwardCoordinate
  focalSpotDistribution : ForwardCoordinate
  sourceBlur : ForwardCoordinate
  detectorPointSpread : ForwardCoordinate
  detectorResponse : ForwardCoordinate
  projectionGeometry : ForwardCoordinate
  attenuationCoefficients : ForwardCoordinate
  objectDensity : ForwardCoordinate
  scatterField : ForwardCoordinate
  photonNoise : ForwardCoordinate

data InverseCoordinate : Set where
  regularisation : InverseCoordinate
  priorModel : InverseCoordinate
  likelihoodModel : InverseCoordinate
  densityReconstruction : InverseCoordinate
  spectrumReconstruction : InverseCoordinate
  blurReconstruction : InverseCoordinate
  posteriorUncertainty : InverseCoordinate
  sensitivityAnalysis : InverseCoordinate

record RadiographyForwardInverseModel : Set where
  constructor radiography-forward-inverse-model
  field
    forwardCoordinates : List ForwardCoordinate
    inverseCoordinates : List InverseCoordinate
    sourceReference : String
    boundedReading : String

open RadiographyForwardInverseModel public

canonicalForwardInverseModel : RadiographyForwardInverseModel
canonicalForwardInverseModel = radiography-forward-inverse-model
  (sourceSpectrum ∷ focalSpotDistribution ∷ sourceBlur ∷ detectorPointSpread ∷ detectorResponse ∷ projectionGeometry ∷ attenuationCoefficients ∷ objectDensity ∷ scatterField ∷ photonNoise ∷ [])
  (regularisation ∷ priorModel ∷ likelihoodModel ∷ densityReconstruction ∷ spectrumReconstruction ∷ blurReconstruction ∷ posteriorUncertainty ∷ sensitivityAnalysis ∷ [])
  "DOI 10.1080/17415977.2015.1046859; DOI 10.3389/fphy.2023.1257548; DOI 10.4208/cicp.OA-2019-0060; DOI 10.1109/TIP.2021.3101929"
  "Measured radiographs are outputs of a coupled source/object/detector forward model; inversion for spectrum, blur or density is ill-posed and requires calibration, priors/regularisation and uncertainty analysis."

record InverseProblemBoundary : Set where
  constructor inverse-problem-boundary
  field
    radiographUniquelyDeterminesDensityWithoutCalibration : Bool
    radiographUniquelyDeterminesDensityWithoutCalibrationIsFalse : radiographUniquelyDeterminesDensityWithoutCalibration ≡ false
    knownGeometryEliminatesSourceAndDetectorBlur : Bool
    knownGeometryEliminatesSourceAndDetectorBlurIsFalse : knownGeometryEliminatesSourceAndDetectorBlur ≡ false
    pointEstimateImpliesKnownUncertainty : Bool
    pointEstimateImpliesKnownUncertaintyIsFalse : pointEstimateImpliesKnownUncertainty ≡ false
    uncertaintyQuantificationCanChangeInterpretiveConfidence : Bool
    uncertaintyQuantificationCanChangeInterpretiveConfidenceIsTrue : uncertaintyQuantificationCanChangeInterpretiveConfidence ≡ true

open InverseProblemBoundary public

canonicalInverseProblemBoundary : InverseProblemBoundary
canonicalInverseProblemBoundary = inverse-problem-boundary false refl false refl false refl true refl

data RadiographyReverseTarget : Set where
  acquireSourceSpectrumCalibration : RadiographyReverseTarget
  acquireFocalSpotMap : RadiographyReverseTarget
  acquireDetectorPSF : RadiographyReverseTarget
  acquireDetectorResponseCurve : RadiographyReverseTarget
  acquireScatterModel : RadiographyReverseTarget
  acquireExactGeometry : RadiographyReverseTarget
  acquireAttenuationModel : RadiographyReverseTarget
  acquireNoiseModel : RadiographyReverseTarget
  acquireRegularisationOrPrior : RadiographyReverseTarget
  acquirePosteriorUncertainty : RadiographyReverseTarget
  acquireValidationPhantomOrGroundTruth : RadiographyReverseTarget
