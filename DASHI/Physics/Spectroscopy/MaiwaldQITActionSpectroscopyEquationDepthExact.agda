module DASHI.Physics.Spectroscopy.MaiwaldQITActionSpectroscopyEquationDepthExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

-- Maiwald's JPL QIT work uses a Paul quadrupole ion trap; the source-shaped
-- operating principle is Mathieu stability in charge-to-mass coordinates.
-- The action-spectroscopy project is kept distinct: irradiation frequency is
-- mapped to photodissociation yield, not directly to absorption by definition.

data QITCoordinate : Set where
  rfAmplitude
  dcAmplitude
  driveFrequency
  trapRadius
  ionCharge
  ionMass
  mathieuA
  mathieuQ
  secularMotion
  micromotion
  : QITCoordinate

record MathieuOperatingPoint : Set where
  constructor mathieu-operating-point
  field
    aReading : String
    qReading : String
    dimensionlessTime : String
    radialEquation : String
    axialEquation : String
    interpretation : String
    sourceReference : String

open MathieuOperatingPoint public

canonicalMathieuOperatingPoint : MathieuOperatingPoint
canonicalMathieuOperatingPoint = mathieu-operating-point
  "a proportional to charge*V_DC /(mass*Omega^2*r0^2)"
  "q proportional to charge*V_AC /(mass*Omega^2*r0^2)"
  "tau = Omega t / 2"
  "d2r/dtau2 = -(a - 2 q cos(2 tau)) r"
  "d2z/dtau2 = 2(a - 2 q cos(2 tau)) z"
  "stable/unstable Mathieu trajectories provide mass-selective confinement/ejection in a Paul trap"
  "JPL ion-trap technical literature; QIT operating principle used by JPL planetary mass-spectrometer programme"

record HypervelocitySamplingChain : Set where
  constructor hypervelocity-sampling-chain
  field
    particleDiameter : String
    demonstratedVelocity : String
    targetUpgradeVelocity : String
    impactProcesses : String
    measuredSignal : String
    sourceReference : String

open HypervelocitySamplingChain public

maiwaldIceParticleSampling : HypervelocitySamplingChain
maiwaldIceParticleSampling = hypervelocity-sampling-chain
  "about 1.3 micrometre ice grains in the reported experiment"
  "up to 1000 m/s"
  "upgrade toward 5000 m/s to approach Enceladus fly-through conditions"
  "molecular fragmentation, impact ionisation and post-impact chemistry may alter original material"
  "brief increases in detected water-molecule abundance after impact"
  "Belousov et al. JASMS 2021, DOI 10.1021/jasms.0c00442; Frank Maiwald coauthor"

record ActionSpectrumResponse : Set where
  constructor action-spectrum-response
  field
    controlledInput : String
    latentAbsorption : String
    measuredOutput : String
    responseFactors : String
    identityInference : String
    sourceReference : String

open ActionSpectrumResponse public

maiwaldMessengerActionResponse : ActionSpectrumResponse
maiwaldMessengerActionResponse = action-spectrum-response
  "irradiation frequency / photon energy"
  "molecular vibrational/electronic excitation of messenger-tagged ion"
  "messenger-loss or photofragment yield"
  "absorption strength, dissociation probability, tag binding, laser intensity and trap/detection efficiency"
  "compare frequency-dependent action yield against structural-isomer/reference spectra"
  "JPL SURP 2023, Unambiguous Detection of Biosignatures by Action Spectroscopy"

record MaiwaldEquationDepthBoundary : Set where
  constructor maiwald-equation-depth-boundary
  field
    stablePaulTrapTrajectoryIdentifiesUniqueMolecule : Bool
    stablePaulTrapTrajectoryIdentifiesUniqueMoleculeIsFalse : stablePaulTrapTrajectoryIdentifiesUniqueMolecule ≡ false
    massToChargePeakEqualsStructuralIdentity : Bool
    massToChargePeakEqualsStructuralIdentityIsFalse : massToChargePeakEqualsStructuralIdentity ≡ false
    hypervelocityImpactPreservesOriginalMoleculeExactly : Bool
    hypervelocityImpactPreservesOriginalMoleculeExactlyIsFalse : hypervelocityImpactPreservesOriginalMoleculeExactly ≡ false
    actionYieldIsDirectAbsorptionByDefinition : Bool
    actionYieldIsDirectAbsorptionByDefinitionIsFalse : actionYieldIsDirectAbsorptionByDefinition ≡ false
    QITAndActionSpectroscopyMayProvideComplementaryChannels : Bool
    QITAndActionSpectroscopyMayProvideComplementaryChannelsIsTrue : QITAndActionSpectroscopyMayProvideComplementaryChannels ≡ true

canonicalMaiwaldEquationDepthBoundary : MaiwaldEquationDepthBoundary
canonicalMaiwaldEquationDepthBoundary = maiwald-equation-depth-boundary false refl false refl false refl false refl true refl

data MaiwaldReverseTarget : Set where
  acquireTrapGeometry
  acquireRFDCOperatingPoint
  acquireMathieuStabilityRegion
  acquireMassCalibration
  acquireImpactFragmentationModel
  acquireLaserCalibration
  acquireTagDissociationResponse
  acquireReferenceActionSpectrum
  acquireOrthogonalMassChannel
  : MaiwaldReverseTarget
