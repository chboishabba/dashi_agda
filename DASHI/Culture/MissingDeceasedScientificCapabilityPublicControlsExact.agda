module DASHI.Culture.MissingDeceasedScientificCapabilityPublicControlsExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

import DASHI.Core.ScientificCapabilityCarrierBidiExact as C

------------------------------------------------------------------------
-- PUBLIC-SCIENCE NEGATIVE CONTROLS
--
-- Technically rich work can be strongly reconstructive and still be largely
-- public.  These controls help separate scientific importance from the narrower
-- hypothesis of concentrated non-public capability.
------------------------------------------------------------------------

-- Carl J. Grillmair: stellar-stream matched filtering and orbit inference.
grillmairMatchedFilterCarrier : C.ScientificCapabilityCarrier
grillmairMatchedFilterCarrier = C.scientific-capability-carrier
  "stellar-stream detection and orbit inference"
  "colour-magnitude matched-filter + foreground model + distance-modulus scan"
  C.sourceCodeOrAlgorithm
  C.carrierPublic
  "DASHI.Physics.Astrophysics.GrillmairMatchedFilterOrbitDepthExact"
  "Grillmair 2017 ApJ 847:119, DOI 10.3847/1538-4357/aa8872"
  "The published method exposes the detection logic, distance scan and orbit-inference structure; this is scientifically reconstructive but not evidence of a bounded technical carrier."

grillmairOrbitCarrier : C.ScientificCapabilityCarrier
grillmairOrbitCarrier = C.scientific-capability-carrier
  "stellar-stream orbit inference"
  "stream track + assumed Galactic potential + kinematic confirmation"
  C.inverseModel
  C.carrierPublic
  "DASHI.Physics.Astrophysics.GrillmairMatchedFilterOrbitDepthExact"
  "Grillmair 2017"
  "Orbit inference is model dependent and publicly described; radial velocity/proper motion remain confirmation channels rather than hidden capability."

-- Michael David Hicks: comet/asteroid physical-characterisation inverse problem.
hicksPhotometryCarrier : C.ScientificCapabilityCarrier
hicksPhotometryCarrier = C.scientific-capability-carrier
  "small-body photometric/spectral characterisation"
  "photometry + viewing geometry + scattering/thermal/shape forward model"
  C.inverseModel
  C.carrierPublic
  "DASHI.Physics.Planetary.HicksSmallBodyPhotometryBidiExact"
  "representative published comet/asteroid physical-characterisation work"
  "The scientific carrier is a multimodal inverse problem; the public science does not support a unique/non-public capability hypothesis by itself."

-- Jason R. Thomas: high-content signalling screens and target deconvolution.
thomasTargetDeconvolutionCarrier : C.ScientificCapabilityCarrier
thomasTargetDeconvolutionCarrier = C.scientific-capability-carrier
  "cell-signalling target deconvolution"
  "phenotypic translocation screen + mini-SAR + chemical proteomics + genetic validation"
  C.integrationProcedure
  C.carrierPublic
  "DASHI.Biology.JasonThomasSTINGFerritinophagyMechanismDepthExact"
  "Koch et al. ACS Chem Biol 2018, DOI 10.1021/acschembio.7b01060"
  "The workflow is reconstructive and scientifically valuable, but the publication itself exposes the central assay/deconvolution logic and also documents residual target ambiguity."

thomasFerritinophagyCarrier : C.ScientificCapabilityCarrier
thomasFerritinophagyCarrier = C.scientific-capability-carrier
  "ferritinophagy / iron-homeostasis mechanism"
  "VPS34 perturbation -> NCOA4 cargo recognition -> ferritin lysosomal turnover -> iron availability"
  C.governingModel
  C.carrierPublic
  "DASHI.Biology.JasonThomasSTINGFerritinophagyMechanismDepthExact"
  "Dowdle et al. Nature Cell Biology 2014, DOI 10.1038/ncb3053"
  "The mechanistic chain is publicly reported; this is a useful control against equating biomedical importance with hidden technical possession."

------------------------------------------------------------------------
-- Reconstructive controls.
------------------------------------------------------------------------

grillmairReconstructive : C.ReconstructiveCarrierReceipt grillmairMatchedFilterCarrier
grillmairReconstructive = C.reconstructive-carrier-receipt
  C.enablesExtension
  "published matched-filter/distance-scan/orbit pipeline supports independent reimplementation and extension"
  "Reconstructive public science is not evidence of non-publicness."

hicksReconstructive : C.ReconstructiveCarrierReceipt hicksPhotometryCarrier
hicksReconstructive = C.reconstructive-carrier-receipt
  C.enablesExtension
  "published inverse-problem structure supports independent physical-characterisation analyses"
  "A public inverse model can be scientifically deep without being a strategic secret."

thomasReconstructive : C.ReconstructiveCarrierReceipt thomasTargetDeconvolutionCarrier
thomasReconstructive = C.reconstructive-carrier-receipt
  C.reproducesExperiment
  "public assay and target-deconvolution workflow supports laboratory replication subject to reagent/cell-system details"
  "Replication difficulty and biological uncertainty must not be conflated with secrecy."

record CurrentPublicScienceControlAssessment : Set where
  constructor current-public-science-control-assessment
  field
    reconstructivePublicScienceExists : Bool
    reconstructivePublicScienceExistsIsTrue :
      reconstructivePublicScienceExists ≡ true
    technicalImportanceImpliesNonPublicness : Bool
    technicalImportanceImpliesNonPublicnessIsFalse :
      technicalImportanceImpliesNonPublicness ≡ false
    technicalImportanceImpliesTargeting : Bool
    technicalImportanceImpliesTargetingIsFalse :
      technicalImportanceImpliesTargeting ≡ false
    publicControlsNeededForCriticalKnowledgeHypothesis : Bool
    publicControlsNeededForCriticalKnowledgeHypothesisIsTrue :
      publicControlsNeededForCriticalKnowledgeHypothesis ≡ true

canonicalCurrentPublicScienceControlAssessment : CurrentPublicScienceControlAssessment
canonicalCurrentPublicScienceControlAssessment =
  current-public-science-control-assessment
    true refl
    false refl
    false refl
    true refl
