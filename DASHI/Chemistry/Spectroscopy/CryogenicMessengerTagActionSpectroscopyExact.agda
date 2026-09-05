module DASHI.Chemistry.Spectroscopy.CryogenicMessengerTagActionSpectroscopyExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

------------------------------------------------------------------------
-- GENERIC CRYOGENIC ION ACTION SPECTROSCOPY
------------------------------------------------------------------------

data ActionSpectroscopyStage : Set where
  ionGeneration
  massSelection
  cryogenicCooling
  messengerAttachment
  infraredExcitation
  tagPredissociation
  fragmentDetection
  actionSpectrum
  structuralAssignment
  : ActionSpectroscopyStage

record MessengerTagProtocol : Set where
  constructor messenger-tag-protocol
  field
    ionSource : String
    cooling : String
    tag : String
    selection : String
    excitation : String
    readout : String
    spectrumConstruction : String

open MessengerTagProtocol public

canonicalMessengerTagProtocol : MessengerTagProtocol
canonicalMessengerTagProtocol = messenger-tag-protocol
  "electrospray or another ion source creates gas-phase ions"
  "cryogenic trapping narrows conformational/thermal distributions"
  "weakly bound inert messenger such as H2, N2, Ne or related tag attaches to the cold ion"
  "mass spectrometry isolates the tagged precursor"
  "tunable IR photon is scanned across vibrational resonances"
  "resonant absorption ejects the weak messenger; depletion/fragment counts provide the action signal"
  "fragment or depletion yield versus photon frequency approximates the vibrational spectrum under the protocol"

record StructureAssignmentChain : Set where
  constructor structure-assignment-chain
  field
    measuredSpectrum : String
    candidateStructures : String
    quantumChemistry : String
    frequencyScaling : String
    comparison : String
    residualAmbiguity : String

open StructureAssignmentChain public

canonicalStructureAssignmentChain : StructureAssignmentChain
canonicalStructureAssignmentChain = structure-assignment-chain
  "cryogenic action spectrum of a mass-selected ion"
  "constitutional isomers, tautomers, protonation states and conformers consistent with composition/mass"
  "calculate harmonic/anharmonic vibrational spectra and relative structures at stated electronic-structure level"
  "computed frequencies/intensities may require method-specific scaling and treatment of anharmonicity/tag perturbation"
  "assign structure from pattern agreement across multiple diagnostic bands rather than one peak"
  "near-degenerate conformers, tag-induced shifts, incomplete conformer sampling and computational error can preserve ambiguity"

record ActionSpectroscopyBoundary : Set where
  constructor action-spectroscopy-boundary
  field
    sameMassMeansSameStructure : Bool
    sameMassMeansSameStructureIsFalse : sameMassMeansSameStructure ≡ false
    oneMatchingBandIdentifiesStructure : Bool
    oneMatchingBandIdentifiesStructureIsFalse : oneMatchingBandIdentifiesStructure ≡ false
    tagIsAlwaysNonPerturbative : Bool
    tagIsAlwaysNonPerturbativeIsFalse : tagIsAlwaysNonPerturbative ≡ false
    cleanLabSpectrumMeansUniquePlanetaryBiosignature : Bool
    cleanLabSpectrumMeansUniquePlanetaryBiosignatureIsFalse : cleanLabSpectrumMeansUniquePlanetaryBiosignature ≡ false
    DFTMatchMeansExperimentalGroundTruth : Bool
    DFTMatchMeansExperimentalGroundTruthIsFalse : DFTMatchMeansExperimentalGroundTruth ≡ false

canonicalActionSpectroscopyBoundary : ActionSpectroscopyBoundary
canonicalActionSpectroscopyBoundary = action-spectroscopy-boundary
  false refl
  false refl
  false refl
  false refl
  false refl

data ActionSpectroscopyReverseTarget : Set where
  needTagPerturbationStudy
  needConformerCoverage
  needComputedMethodUncertainty
  needIsomerMixtureTests
  needSensitivitySpecificity
  needMatrixInterferenceTests
  : ActionSpectroscopyReverseTarget
