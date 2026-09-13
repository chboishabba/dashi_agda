module DASHI.Culture.MissingDeceasedTwentyScientistScienceCapabilityBidiExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)
open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Core.ScientificCapabilityCarrierBidiExact as C
import DASHI.Core.ApplicationTransformationCapabilityBidiExact as T
import DASHI.Core.CapabilitySynthesisHypergraphExact as H
import DASHI.Core.QueryFactorisationSufficiency as Q
import DASHI.Culture.MissingDeceasedTwentyScientistRound6ScienceSuccessionExact as R6

------------------------------------------------------------------------
-- TWENTY-SCIENTIST SCIENCE CAPABILITY BIDI
--
-- This is a thin adapter over existing DASHI machinery.  Each fibre binds a
-- paid/bounded science object to (a) its intended application, (b) one possible
-- extension whose evidentiary strength is typed, and (c) reverse obligations
-- needed to reconstruct or operationalise that application.
--
-- It does NOT assert that the twenty people collaborated, shared a programme,
-- possessed every listed carrier, were selected because of the science, or that
-- any event was caused by a capability represented here.
------------------------------------------------------------------------

data ApplicationClaimStrength : Set where
  sourceBackedIntended : ApplicationClaimStrength
  documentedEngineeringInterface : ApplicationClaimStrength
  crossDomainCandidate : ApplicationClaimStrength
  speculativeOnly : ApplicationClaimStrength

record ApplicationUse : Set where
  constructor application-use
  field
    applicationLabel : String
    claimStrength : ApplicationClaimStrength
    transformation : T.ApplicationTransformation
    evidenceReference : String
    applicationBoundary : String

open ApplicationUse public

record BidiReverseObligation : Set where
  constructor bidi-reverse-obligation
  field
    transformationTargets : List T.TransformationReverseTarget
    criticalityTargets : List C.ScientificCriticalityTarget
    scienceProofLeaf : String
    custodyLeaf : String

open BidiReverseObligation public

record ScientistTechnologyFibre : Set where
  constructor scientist-technology-fibre
  field
    person : String
    scienceKernel : String
    scienceObject : String
    stableIdentifier : String
    carrier : C.ScientificCapabilityCarrier
    intendedApplication : ApplicationUse
    possibleApplication : ApplicationUse
    reverseObligation : BidiReverseObligation
    scienceOwnerReference : String
    attributionBoundary : String

open ScientistTechnologyFibre public

mkCarrier :
  String → String → C.CapabilityCarrierKind → C.CarrierEpistemicState →
  String → String → String → C.ScientificCapabilityCarrier
mkCarrier domain name kind state mechanism source bounded =
  C.scientific-capability-carrier domain name kind state mechanism source bounded

mkTransformation :
  String → List T.TransformationCoordinate → List T.TransformationCoordinate →
  String → String → T.ApplicationTransformation
mkTransformation domain public capability source bounded =
  T.application-transformation domain public capability source bounded

mkUse :
  String → ApplicationClaimStrength → T.ApplicationTransformation →
  String → String → ApplicationUse
mkUse = application-use

mkReverse :
  List T.TransformationReverseTarget → List C.ScientificCriticalityTarget →
  String → String → BidiReverseObligation
mkReverse = bidi-reverse-obligation

------------------------------------------------------------------------
-- United States fibres (11)
------------------------------------------------------------------------

nunoLoureiroFibre : ScientistTechnologyFibre
nunoLoureiroFibre = scientist-technology-fibre
  "Nuno F. G. Loureiro"
  "KREHM/KRMHD Fourier-Hermite plasma dynamics, reconnection, plasmoid instability and kinetic-Alfven turbulence"
  "Viriato/KREHM implementation and Hermite-moment plasma equations"
  "arXiv:1505.02649"
  (mkCarrier "plasma physics" "Viriato/KREHM model and implementation" C.sourceCodeOrAlgorithm C.carrierPublic
    "Fourier-Hermite reduced kinetic plasma model and numerical implementation"
    "arXiv:1505.02649; repo Loureiro Viriato/Hermite owners"
    "Public equations/code architecture are reconstructive, while run-specific closures, validation and simulation state remain application coordinates.")
  (mkUse "simulate magnetic reconnection, plasmoid formation and magnetised turbulence" sourceBackedIntended
    (mkTransformation "reduced kinetic plasma simulation"
      (T.governingPhysics ∷ T.closureOrRegularisation ∷ T.sourceOrAlgorithmImplementation ∷ [])
      (T.operatingWindow ∷ T.validationCorpus ∷ T.integrationWorkflow ∷ [])
      "Viriato/KREHM publication lineage"
      "Intended use is numerical plasma modelling in the ordered KREHM/KRMHD regimes.")
    "Viriato/KREHM publication lineage" "Does not imply a particular fusion or propulsion application.")
  (mkUse "magnetised-plasma design, diagnostics and space-plasma simulation component" crossDomainCandidate
    (mkTransformation "integrated magnetised-plasma modelling"
      (T.governingPhysics ∷ T.sourceOrAlgorithmImplementation ∷ [])
      (T.applicationGeometry ∷ T.operatingWindow ∷ T.validationCorpus ∷ [])
      "existing DASHI fusion/plasma capability synthesis"
      "A technically compatible modelling role; historical deployment requires independent same-object evidence.")
    "DASHI capability-synthesis interface" "Technical compatibility is not historical programme membership.")
  (mkReverse
    (T.acquireClosureOrRegularisation ∷ T.acquireOperatingWindow ∷ T.acquireValidationCorpus ∷ T.acquireIntegrationWorkflow ∷ T.acquireSuccessorHandover ∷ [])
    (C.carrierReplacementDifficulty ∷ C.personCarrierPossession ∷ [])
    "weld exact KREHM/KRMHD equations, Hermite closures, discretisation and finite benchmarks to executable owners"
    "named Viriato/KREHM repository maintainer, grant reassignment and simulation-state custodian")
  "DASHI.Physics.Plasma.LoureiroViriatoPlasmoidBidiExact; LoureiroKREHMHermiteEquationDepthExact"
  "Science carrier is public; person-specific post-loss repository/state possession is separately unpaid."

joshuaLeBlancFibre : ScientistTechnologyFibre
joshuaLeBlancFibre = scientist-technology-fibre
  "Joshua Kyle LeBlanc"
  "space-fission instrumentation and controls technology maturation, sensing, qualification and integration"
  "NASA 40 kW FSP I&C technology path / NPIC&HMIT technology gaps"
  "NTRS 20250008475; DOI 10.13182/NPICHMIT25-46370"
  (mkCarrier "space fission I&C" "qualification/calibration/failure-state carrier" C.qualificationEvidence C.carrierPartial
    "sensor/control qualification, drift/failure maps and integration state"
    "NTRS 20250008475; DOI 10.13182/NPICHMIT25-46370"
    "Programme and TechMat role are public; exact calibration/failure envelopes and handover remain partial.")
  (mkUse "qualify and integrate instrumentation/control for fission surface power" sourceBackedIntended
    (mkTransformation "fission surface power I&C"
      (T.governingPhysics ∷ T.sourceOrAlgorithmImplementation ∷ [])
      (T.calibrationState ∷ T.operatingWindow ∷ T.failureHistory ∷ T.qualificationEvidence ∷ T.validationCorpus ∷ T.integrationWorkflow ∷ [])
      "NASA FSP I&C technology maturation"
      "The intended application is reliable sensing/control in space-fission power systems.")
    "NASA FSP programme" "Named role does not imply sole ownership of qualification state.")
  (mkUse "radiation/temperature-tolerant autonomous controls for other long-duration high-power systems" documentedEngineeringInterface
    (mkTransformation "harsh-environment autonomous control"
      (T.sourceOrAlgorithmImplementation ∷ T.uncertaintyModel ∷ [])
      (T.calibrationState ∷ T.failureHistory ∷ T.qualificationEvidence ∷ T.integrationWorkflow ∷ [])
      "general I&C engineering interface"
      "Transfer requires requalification for the new plant, sensors and environment.")
    "engineering-interface candidate" "Same I&C principles do not create a qualified application.")
  (mkReverse
    (T.acquireCalibrationState ∷ T.acquireOperatingWindow ∷ T.acquireFailureHistory ∷ T.acquireQualificationEvidence ∷ T.acquireValidationCorpus ∷ T.acquireSuccessorHandover ∷ [])
    (C.carrierIntegrationBreadth ∷ C.personCarrierPossession ∷ [])
    "recover exact FICS gap matrix, sensor requirements, qualification envelopes and failure/calibration evidence"
    "first dated SNP I&C TechMat roster revision plus named successor and data handover")
  "DASHI.Physics.Nuclear.LeBlancFissionSurfacePowerICBidiExact; LeBlancFSPICQualificationDepthExact"
  "A post-loss stale role manifestation is not a succession receipt."

frankMaiwaldFibre : ScientistTechnologyFibre
frankMaiwaldFibre = scientist-technology-fibre
  "Frank W. Maiwald"
  "cryogenic messenger-tag action spectroscopy and quadrupole-ion-trap mass spectrometry"
  "Cryogenic Ion Vibrational Spectroscopy of Protonated Valine: Messenger Tag Effects"
  "DOI 10.1021/acs.jpca.4c03552; PMID 39150465"
  (mkCarrier "molecular spectroscopy" "trap/tag calibration and action-spectrum data" C.calibrationData C.carrierPartial
    "cryogenic trapped-ion preparation, messenger tagging, laser response and fragmentation spectrum"
    "DOI 10.1021/acs.jpca.4c03552; JPL SURP SP23012p"
    "Protocol and publication are public; raw/reduced spectra, calibration state and notebook custody remain partial.")
  (mkUse "molecular/isomer discrimination by tagged-ion action spectroscopy" sourceBackedIntended
    (mkTransformation "cryogenic ion action spectroscopy"
      (T.governingPhysics ∷ T.applicationGeometry ∷ T.sourceOrAlgorithmImplementation ∷ [])
      (T.calibrationState ∷ T.operatingWindow ∷ T.validationCorpus ∷ T.uncertaintyModel ∷ [])
      "JPL action-spectroscopy project and DOI publication"
      "Intended use is molecular identification, not crystallographic lattice imaging.")
    "DOI 10.1021/acs.jpca.4c03552" "Molecular spectroscopy cannot establish provenance of an unknown sample by itself.")
  (mkUse "planetary/laboratory trace molecular diagnostics" documentedEngineeringInterface
    (mkTransformation "planetary molecular diagnostics"
      (T.governingPhysics ∷ T.sourceOrAlgorithmImplementation ∷ [])
      (T.applicationGeometry ∷ T.calibrationState ∷ T.qualificationEvidence ∷ T.integrationWorkflow ∷ [])
      "JPL planetary-instrument science interface"
      "A plausible instrument extension requiring new qualification and sample-handling evidence.")
    "JPL spectroscopy/instrument interface" "Compatibility does not identify a particular flown or classified instrument.")
  (mkReverse
    (T.acquireApplicationGeometry ∷ T.acquireCalibrationState ∷ T.acquireOperatingWindow ∷ T.acquireValidationCorpus ∷ T.acquireUncertaintyModel ∷ T.acquireSuccessorHandover ∷ [])
    (C.carrierReplacementDifficulty ∷ C.personCarrierPossession ∷ [])
    "formalise ion/tag/trap/laser/fragmentation action-response relation against source-exact spectra"
    "raw/reduced spectra, calibration files, notebooks and 2023-to-2024 handover")
  "DASHI.Physics.Spectroscopy.MaiwaldActionSpectroscopyBidiExact; MaiwaldQITActionSpectroscopyEquationDepthExact"
  "Project continuity and later PI identity do not automatically transfer raw-data custody."

monicaRezaFibre : ScientistTechnologyFibre
monicaRezaFibre = scientist-technology-fibre
  "Monica Jacinto / Monica Reza"
  "burn-resistant high-strength Ni-Co-Cr-Al-Ti oxygen-service alloy, gamma/gamma-prime microstructure and process control"
  "Jacinto/Hardwick alloy family and later MONDALOY oxygen-turbopump applications"
  "US20030053926A1; US20100266442A1; US20190032604A1"
  (mkCarrier "extreme-environment materials" "oxygen-service alloy process window" C.processWindow C.carrierPartial
    "composition, melt/remelt, heat/process state and oxygen burn/strength tradeoff"
    "US20030053926A1; US20100266442A1; US20190032604A1"
    "Composition and examples are public; validated manufacturing/qualification windows remain application-specific.")
  (mkUse "survive high-pressure oxygen combustion while retaining structural strength" sourceBackedIntended
    (mkTransformation "oxygen-rich turbomachinery material"
      (T.governingPhysics ∷ T.constitutiveConfiguration ∷ [])
      (T.operatingWindow ∷ T.failureHistory ∷ T.qualificationEvidence ∷ T.validationCorpus ∷ T.tacitExecutionKnowledge ∷ [])
      "Jacinto/Hardwick patents and turbopump descendant"
      "Intended application is oxygen-service materials engineering.")
    "patent family" "Gamma/gamma-prime microstructure is not a mechanical metamaterial and does not imply exotic provenance.")
  (mkUse "extreme oxidizer and high-temperature structural/liner components" documentedEngineeringInterface
    (mkTransformation "extreme oxidising-environment material system"
      (T.constitutiveConfiguration ∷ T.applicationGeometry ∷ [])
      (T.operatingWindow ∷ T.failureHistory ∷ T.qualificationEvidence ∷ T.integrationWorkflow ∷ [])
      "materials-survivability engineering interface"
      "Transfer to another environment requires source-exact chemistry, stress, temperature and qualification envelopes.")
    "DASHI material-survivability cross-pollination" "Oxygen-rich rocket service is not fusion service without a new material/environment witness.")
  (mkReverse
    (T.acquireConstitutiveConfiguration ∷ T.acquireOperatingWindow ∷ T.acquireFailureHistory ∷ T.acquireQualificationEvidence ∷ T.acquireTacitExecutionKnowledge ∷ T.acquireSuccessorHandover ∷ [])
    (C.carrierReplacementDifficulty ∷ C.personCarrierPossession ∷ [])
    "formalise composition/process/heat-treatment to tensile/burn-pressure tradeoff and distinguish bulk/coating/enamel descendants"
    "assignment chain Boeing/UTC to Rocketdyne/Aerojet plus event-time process-window custodian")
  "DASHI.Physics.Materials.RezaBurnResistantAlloyBidiExact; RezaGammaPrimeBurnStrengthTradeoffDepthExact"
  "Corporate assignment genealogy does not prove one uninterrupted programme or person-specific 2025 possession."

carlGrillmairFibre : ScientistTechnologyFibre
carlGrillmairFibre = scientist-technology-fibre
  "Carl J. Grillmair"
  "matched-filter stellar-stream detection, orbit inference and Galactic-potential constraints"
  "Caltech/IPAC stellar-stream publication corpus"
  "DOI 10.3847/1538-4357/aa8872"
  (mkCarrier "astrophysical inference" "stellar-stream matched-filter/orbit algorithm" C.sourceCodeOrAlgorithm C.carrierPublic
    "colour-magnitude matched filtering, distance scans and orbit/potential inference"
    "DOI 10.3847/1538-4357/aa8872; Caltech/IPAC corpus"
    "Published methods are public; exact maps/catalogues and unfinished reductions can remain data-state carriers.")
  (mkUse "detect stellar debris streams and constrain Galactic structure" sourceBackedIntended
    (mkTransformation "stellar-stream survey inference"
      (T.governingPhysics ∷ T.sourceOrAlgorithmImplementation ∷ [])
      (T.calibrationState ∷ T.validationCorpus ∷ T.uncertaintyModel ∷ [])
      "Grillmair stellar-stream corpus"
      "Intended application is astronomical structure inference.")
    "Caltech/IPAC science corpus" "Separate exoplanet spectroscopy work remains a distinct fibre.")
  (mkUse "large-survey weak-signal structure/anomaly detection" crossDomainCandidate
    (mkTransformation "weak-signal survey inference"
      (T.sourceOrAlgorithmImplementation ∷ T.uncertaintyModel ∷ [])
      (T.validationCorpus ∷ T.integrationWorkflow ∷ [])
      "algorithmic analogy only"
      "Matched-filter ideas can transfer mathematically, but new noise/source models are required.")
    "cross-domain algorithm candidate" "Algorithm resemblance is not same data, mission or programme.")
  (mkReverse
    (T.acquireCalibrationState ∷ T.acquireValidationCorpus ∷ T.acquireUncertaintyModel ∷ T.acquireSuccessorHandover ∷ [])
    (C.carrierReplacementDifficulty ∷ C.personCarrierPossession ∷ [])
    "close finite colour-magnitude matched-filter weights and orbit inference on one source-exact stream"
    "named custodian for stream maps, catalogues, orbit fits or unfinished manuscripts")
  "DASHI.Physics.Astrophysics.GrillmairStellarStreamBidiExact; GrillmairMatchedFilterOrbitDepthExact"
  "Charged local-crime evidence remains an independent event fibre and is not displaced by technical depth."

michaelHicksFibre : ScientistTechnologyFibre
michaelHicksFibre = scientist-technology-fibre
  "Michael David Hicks"
  "asteroid/comet photometry and spectrophotometry with rotational, phase and physical-property inference"
  "JPL/TMO small-body observing corpus"
  "exact DOI set retained in Hicks specific-work owner"
  (mkCarrier "planetary astronomy" "small-body calibrated photometry/spectrophotometry" C.rawExperimentalData C.carrierPartial
    "observation geometry, photometric/spectral calibration and physical-property inference"
    "repo Hicks science owners; JPL/TMO corpus"
    "Methods are public; source-exact observing/reduction datasets and unfinished state remain partial.")
  (mkUse "characterise asteroid/comet rotation, phase, colour and composition" sourceBackedIntended
    (mkTransformation "small-body physical characterisation"
      (T.governingPhysics ∷ T.applicationGeometry ∷ [])
      (T.calibrationState ∷ T.validationCorpus ∷ T.uncertaintyModel ∷ [])
      "Hicks small-body publications"
      "Intended application is observational planetary science.")
    "Hicks publication corpus" "Does not imply propulsion or programme sensitivity.")
  (mkUse "planetary-defense target characterisation and mission planning input" documentedEngineeringInterface
    (mkTransformation "NEO target characterisation"
      (T.applicationGeometry ∷ T.calibrationState ∷ [])
      (T.validationCorpus ∷ T.uncertaintyModel ∷ T.integrationWorkflow ∷ [])
      "planetary-defense/NEO science interface"
      "Photometric characterisation can inform target models; mission decisions require independent dynamics and engineering.")
    "planetary science interface" "Scientific target characterisation is not an interceptor design or historical mission assignment.")
  (mkReverse
    (T.acquireCalibrationState ∷ T.acquireValidationCorpus ∷ T.acquireUncertaintyModel ∷ T.acquireSuccessorHandover ∷ [])
    (C.personCarrierPossession ∷ C.carrierReplacementDifficulty ∷ [])
    "formalise one lightcurve/spectrum with uncertainty to rotation/shape/composition inference"
    "primary 2022 JPL separation plus unfinished observing/reduction/data handover")
  "DASHI.Physics.Planetary.HicksSmallBodyPhotometryBidiExact; HicksCometAsteroidSpecificWorksBidiExact"
  "His JPL role ended before death; technical-removal claims require a separate active-work receipt."

williamNeilMcCaslandFibre : ScientistTechnologyFibre
williamNeilMcCaslandFibre = scientist-technology-fibre
  "William Neil McCasland"
  "fault-tolerant sensor/actuator placement for flexible structures using controllability/observability Gramians"
  "Sensor and Actuator Selection for Fault-Tolerant Control of Flexible Structures"
  "NASA A89-54007; ACC 1989"
  (mkCarrier "structural control" "fault-tolerant Gramian placement algorithm" C.sourceCodeOrAlgorithm C.carrierPublic
    "sensor/actuator selection under failure families with Gramian performance measures"
    "NASA A89-54007; ACC 1989"
    "Published control theory is public; application geometry and failure-family configuration are separate capability coordinates.")
  (mkUse "place sensors/actuators for robust control of flexible structures" sourceBackedIntended
    (mkTransformation "fault-tolerant flexible-structure control"
      (T.governingPhysics ∷ T.sourceOrAlgorithmImplementation ∷ [])
      (T.applicationGeometry ∷ T.failureHistory ∷ T.uncertaintyModel ∷ T.validationCorpus ∷ [])
      "McCasland control paper"
      "Intended application is resilient flexible-structure control.")
    "ACC/NASA bibliography" "Later AFRL roles are a distinct programme fibre.")
  (mkUse "resilient control placement for large flexible spacecraft or observatories" documentedEngineeringInterface
    (mkTransformation "large flexible platform control"
      (T.governingPhysics ∷ T.sourceOrAlgorithmImplementation ∷ [])
      (T.applicationGeometry ∷ T.failureHistory ∷ T.qualificationEvidence ∷ T.validationCorpus ∷ [])
      "flexible-spacecraft engineering interface"
      "Algorithm transfer requires a new plant model and failure family.")
    "documented structural-control interface" "Compatibility is not an event-time DBE/AFRL programme receipt.")
  (mkReverse
    (T.acquireApplicationGeometry ∷ T.acquireFailureHistory ∷ T.acquireValidationCorpus ∷ T.acquireUncertaintyModel ∷ T.acquireSuccessorHandover ∷ [])
    (C.carrierIntegrationBreadth ∷ C.personCarrierPossession ∷ [])
    "reconstruct Gramian indices, placement optimisation and failure-family objective on a finite beam model"
    "dated DBE Consulting role and exact 2025-2026 client/programme/tasking carrier")
  "DASHI.Control.McCaslandFaultTolerantFlexibleStructureControlBidiExact; McCaslandGramianPlacementAlgorithmDepthExact"
  "Historical programme leadership cannot be inferred from an older control-theory paper."

anthonyChavezFibre : ScientistTechnologyFibre
anthonyChavezFibre = scientist-technology-fibre
  "Anthony Chavez"
  "LANL engineering carrier: DARHT engineering and completed Scorpius accelerator design work"
  "LANL Summer 2025 Anthony Chavez engineering profile"
  "LANL Summer 2025 profile"
  (mkCarrier "pulsed accelerator engineering" "Scorpius/DARHT design and diagnostics carrier" C.designGeometry C.carrierPartial
    "pulsed accelerator component design, radiographic diagnostics and commissioning configuration"
    "LANL Summer 2025 engineering profile; repo Scorpius owner"
    "Engineering profile is strong; inheritance by the missing-person identity is gated on same-person evidence.")
  (mkUse "design and commission pulsed accelerator/radiographic systems" sourceBackedIntended
    (mkTransformation "pulsed accelerator diagnostics"
      (T.governingPhysics ∷ T.applicationGeometry ∷ [])
      (T.calibrationState ∷ T.failureHistory ∷ T.qualificationEvidence ∷ T.integrationWorkflow ∷ [])
      "LANL Scorpius/DARHT engineering surface"
      "Intended use is accelerator/radiography engineering.")
    "LANL engineering profile" "The missing-person carrier cannot inherit this work until identity is welded.")
  (mkUse "high-energy test and radiographic diagnostics ecosystem" documentedEngineeringInterface
    (mkTransformation "high-energy diagnostic test facility"
      (T.governingPhysics ∷ T.applicationGeometry ∷ [])
      (T.calibrationState ∷ T.qualificationEvidence ∷ T.validationCorpus ∷ T.integrationWorkflow ∷ [])
      "existing DASHI high-energy diagnostics synthesis"
      "Scorpius/DARHT can participate in a test ecosystem without implying a shared roster programme.")
    "DASHI capability synthesis" "System integration does not establish person identity or event causation.")
  (mkReverse
    (T.acquirePersonRoleWeld ∷ T.acquireApplicationGeometry ∷ T.acquireCalibrationState ∷ T.acquireQualificationEvidence ∷ T.acquireSuccessorHandover ∷ [])
    (C.personCarrierPossession ∷ C.carrierIntegrationBreadth ∷ [])
    "deepen exact Scorpius subsystem/design responsibility after identity weld"
    "primary same-person receipt joining missing-person Anthony Chavez to LANL engineering profile")
  "DASHI.Physics.Accelerator.AnthonyChavezScorpiusBidiExact"
  "Same name/place/topic is insufficient to merge missing-person, LANL-profile and publication identities."

jasonThomasFibre : ScientistTechnologyFibre
jasonThomasFibre = scientist-technology-fibre
  "Jason R. Thomas"
  "STING signalling and VPS34/NCOA4 ferritin degradation/ferritinophagy chemical biology"
  "Thomas signalling corpus and VPS34/NCOA4 mechanism lineage"
  "DOI 10.1038/ncb3053"
  (mkCarrier "chemical biology" "assay/target-deconvolution validation corpus" C.rawExperimentalData C.carrierPartial
    "phenotypic screening, perturbation, proteomics/target identification and orthogonal validation"
    "DOI 10.1038/ncb3053 science lineage; repo Thomas owners"
    "Published mechanism lineage is public; exact Thomas-authored assay/data custody remains source-specific.")
  (mkUse "identify signalling/autophagy mechanisms and chemical perturbation targets" sourceBackedIntended
    (mkTransformation "chemical-biology target deconvolution"
      (T.governingPhysics ∷ T.sourceOrAlgorithmImplementation ∷ [])
      (T.calibrationState ∷ T.validationCorpus ∷ T.uncertaintyModel ∷ [])
      "Thomas science corpus"
      "Intended use is mechanistic chemical biology and target validation.")
    "Thomas science corpus" "Mechanistic importance does not imply event motive.")
  (mkUse "biomarker/target-discovery and controlled therapeutic research workflow" documentedEngineeringInterface
    (mkTransformation "translational molecular assay workflow"
      (T.sourceOrAlgorithmImplementation ∷ T.validationCorpus ∷ [])
      (T.calibrationState ∷ T.uncertaintyModel ∷ T.qualificationEvidence ∷ T.integrationWorkflow ∷ [])
      "chemical-biology translation interface"
      "Translational use requires disease-specific validation and qualification.")
    "biomedical research interface" "No clinical efficacy or deployment is inferred.")
  (mkReverse
    (T.acquireCalibrationState ∷ T.acquireValidationCorpus ∷ T.acquireUncertaintyModel ∷ T.acquireSuccessorHandover ∷ [])
    (C.personCarrierPossession ∷ C.carrierReplacementDifficulty ∷ [])
    "recover exact Thomas-authored assay objects and formalise perturbation-to-target-to-ferritin-turnover readout"
    "final ME cause/manner plus exact lab/project/data succession")
  "DASHI.Biology.JasonThomasSignallingBidiExact; JasonThomasSTINGFerritinophagyMechanismDepthExact"
  "Public no-foul-play/event evidence remains separate from science significance."

amyEskridgeFibre : ScientistTechnologyFibre
amyEskridgeFibre = scientist-technology-fibre
  "Amy Eskridge"
  "engineered-gravity mechanism programme: electrogravitics and field-propulsion mechanism discrimination"
  "Amy programme/presentation carriers; exact Amy-authored technical object unresolved"
  "Amy same-object STI identifier unresolved"
  (mkCarrier "engineered-gravity mechanism investigation" "Amy technical-object acquisition carrier" C.governingModel C.carrierUnknown
    "mechanism discrimination among claimed electrogravitic/field-propulsion effects"
    "repo Amy memorial/programme attribution owners"
    "Programme interest is source-backed more strongly than a conventional Amy-authored scientific publication object.")
  (mkUse "compare and experimentally discriminate claimed engineered-gravity mechanisms" sourceBackedIntended
    (mkTransformation "engineered-gravity mechanism test programme"
      (T.governingPhysics ∷ T.applicationGeometry ∷ [])
      (T.calibrationState ∷ T.operatingWindow ∷ T.validationCorpus ∷ T.uncertaintyModel ∷ [])
      "Amy programme sources; public POAMS only as comparator"
      "Intended programme-level role is mechanism discrimination; exact apparatus object remains unpaid.")
    "Amy first-person/programme sources" "NTRS 20205010911 is not Amy authorship.")
  (mkUse "high-sensitivity null/comparator testbed for anomalous-force claims" speculativeOnly
    (mkTransformation "anomalous-force null testbed"
      (T.governingPhysics ∷ T.applicationGeometry ∷ [])
      (T.calibrationState ∷ T.validationCorpus ∷ T.uncertaintyModel ∷ T.failureHistory ∷ [])
      "cross-mechanism comparator design"
      "This is a test/discrimination application, not an accepted propulsion capability.")
    "speculative mechanism-comparison coordinate" "No historical deployment, performance or propulsion effect is asserted.")
  (mkReverse
    (T.acquirePersonRoleWeld ∷ T.acquireApplicationGeometry ∷ T.acquireCalibrationState ∷ T.acquireValidationCorpus ∷ T.acquireUncertaintyModel ∷ T.acquireEventLink ∷ [])
    (C.personCarrierPossession ∷ C.carrierNonPublicness ∷ C.eventCausalLink ∷ [])
    "recover an Amy-authored/recorded technical object with equations/apparatus before mechanism welding"
    "Amy-linked NF-1676/EDAA/STRIVES object plus Institute derivative/handover identity")
  "DASHI.Culture.AmyEskridgeGravityMechanismCrossPollinationExact"
  "Mechanism adjacency cannot manufacture Amy authorship, a validated effect, shared programme or event cause."

ningLiFibre : ScientistTechnologyFibre
ningLiFibre = scientist-technology-fibre
  "Ning Li"
  "superconducting gravitoelectric/gravitomagnetic theory plus static and rotating/AC-field YBCO gravity tests"
  "Li/Torr theory and 1997/1998 YBCO experimental lineage"
  "10.1103/PhysRevD.43.457; 10.1103/PhysRevB.46.5489; 10.1016/S0921-4534(97)01462-7"
  (mkCarrier "superconductor/gravity test physics" "YBCO null/constraint apparatus state" C.hardwareConfiguration C.carrierPartial
    "static and rotating/AC-field YBCO gravimeter experiments with magnetic/thermal controls"
    "1997 Physica C; NTRS 19990019627"
    "Published tests constrain tested configurations; later AC Gravity apparatus continuity is unproved.")
  (mkUse "test superconducting-gravity predictions and place experimental bounds" sourceBackedIntended
    (mkTransformation "YBCO gravity-effect experiment"
      (T.governingPhysics ∷ T.applicationGeometry ∷ [])
      (T.calibrationState ∷ T.operatingWindow ∷ T.validationCorpus ∷ T.uncertaintyModel ∷ [])
      "Li/Torr and NASA/MSFC experimental lineage"
      "Intended use is hypothesis testing; published measurements do not pay a positive antigravity effect.")
    "Physica C / NTRS experimental lineage" "Multiple manifestations of one experiment are not independent replications.")
  (mkUse "precision null-test platform for weak force/gravimeter systematics" documentedEngineeringInterface
    (mkTransformation "precision anomalous-force null testing"
      (T.governingPhysics ∷ T.applicationGeometry ∷ [])
      (T.calibrationState ∷ T.failureHistory ∷ T.validationCorpus ∷ T.uncertaintyModel ∷ [])
      "precision-measurement engineering interface"
      "A useful extension is improved null testing and confounder discrimination, not assumed propulsion.")
    "experimental-method interface" "No positive field-generation application is inferred.")
  (mkReverse
    (T.acquireApplicationGeometry ∷ T.acquireCalibrationState ∷ T.acquireOperatingWindow ∷ T.acquireFailureHistory ∷ T.acquireValidationCorpus ∷ T.acquireUncertaintyModel ∷ T.acquireSuccessorHandover ∷ [])
    (C.carrierReplacementDifficulty ∷ C.personCarrierPossession ∷ [])
    "reconstruct static versus AC/rotating apparatus and controls before any later-apparatus comparison"
    "original FY2001 DoD row, Army SOW, closeout/result and apparatus continuity from NCC8-124")
  "DASHI.Physics.ExoticGravity.NingLiYBCOGravityConstraintBidiExact; NingLiYBCORotatingFieldConstraintExact"
  "Theory, null/constraint experiments and Army programme claims remain distinct source objects."

------------------------------------------------------------------------
-- Chinese fibres (9)
------------------------------------------------------------------------

chenShumingFibre : ScientistTechnologyFibre
chenShumingFibre = scientist-technology-fibre
  "Chen Shuming"
  "hardware/processor verification and indigenous military DSP/flight-control chip development"
  "Simulation-Based Hardware Verification with a Graph-Based Specification"
  "DOI 10.1155/2018/6398616"
  (mkCarrier "hardware verification" "graph-based specification and simulation verification method" C.sourceCodeOrAlgorithm C.carrierPublic
    "graph-structured hardware specification with simulation-based verification"
    "DOI 10.1155/2018/6398616; NUDT Galaxy/Feiteng history"
    "The paper is a public verification object; mapping to exact processors requires a same-project receipt.")
  (mkUse "verify complex digital hardware/processor designs" sourceBackedIntended
    (mkTransformation "simulation-based hardware verification"
      (T.sourceOrAlgorithmImplementation ∷ T.validationCorpus ∷ [])
      (T.failureHistory ∷ T.uncertaintyModel ∷ T.integrationWorkflow ∷ [])
      "DOI 10.1155/2018/6398616"
      "Intended use is hardware verification and validation.")
    "DOI 10.1155/2018/6398616" "Does not by itself identify a deployed military processor.")
  (mkUse "assurance/verification for custom processors in safety-critical autonomous systems" documentedEngineeringInterface
    (mkTransformation "safety-critical processor verification"
      (T.sourceOrAlgorithmImplementation ∷ T.validationCorpus ∷ [])
      (T.failureHistory ∷ T.qualificationEvidence ∷ T.integrationWorkflow ∷ [])
      "hardware-assurance engineering interface"
      "Transfer requires source-exact processor specifications and qualification criteria.")
    "verification engineering interface" "Possible use does not establish historical deployment.")
  (mkReverse
    (T.acquireFailureHistory ∷ T.acquireValidationCorpus ∷ T.acquireQualificationEvidence ∷ T.acquireIntegrationWorkflow ∷ T.acquireSuccessorHandover ∷ [])
    (C.personCarrierPossession ∷ C.carrierIntegrationBreadth ∷ [])
    "formalise graph-based hardware specification and simulation-coverage relation"
    "primary event identity and redistribution of Chen-specific processor/verification responsibility")
  "DASHI.Culture.ChineseStrategicScientistRosterSnowballExact"
  "Processor programme identity must be welded independently from a general verification publication."

fengYangheFibre : ScientistTechnologyFibre
fengYangheFibre = scientist-technology-fibre
  "Feng Yanghe"
  "military wargame decision agents plus multi-group-graph Bayesian classification and noisy-label classification"
  "War Skull II institutional surface and NUDT Press statistical-learning monographs"
  "ISBN 978-7-5673-0533-5; ISBN 978-7-5673-0611-0"
  (mkCarrier "statistical learning / decision AI" "Bayesian/noisy-label classification algorithms" C.sourceCodeOrAlgorithm C.carrierPublic
    "multi-group-graph Bayesian classification and robustness to noisy labels"
    "NUDT Press ISBNs; NUDT War Skull II institutional article"
    "Published methods and War Skull engineering are separately paid objects until a software/document weld is found.")
  (mkUse "robust classification and opponent-adaptive wargame decision support" sourceBackedIntended
    (mkTransformation "robust classification / decision support"
      (T.sourceOrAlgorithmImplementation ∷ T.uncertaintyModel ∷ [])
      (T.validationCorpus ∷ T.integrationWorkflow ∷ [])
      "NUDT statistical-learning and War Skull sources"
      "The statistical and wargame objects remain separately source-bound.")
    "NUDT sources" "Authorship of methods does not prove they are the exact War Skull implementation.")
  (mkUse "decision support under noisy/partial labels in non-military operations" crossDomainCandidate
    (mkTransformation "noise-robust decision support"
      (T.sourceOrAlgorithmImplementation ∷ T.uncertaintyModel ∷ [])
      (T.validationCorpus ∷ T.integrationWorkflow ∷ [])
      "cross-domain statistical-learning interface"
      "The algorithms can be evaluated in other classification domains with new data and loss functions.")
    "algorithmic extension candidate" "Cross-domain applicability is not historical deployment.")
  (mkReverse
    (T.acquireValidationCorpus ∷ T.acquireUncertaintyModel ∷ T.acquireIntegrationWorkflow ∷ T.acquireSuccessorHandover ∷ [])
    (C.personCarrierPossession ∷ C.carrierReplacementDifficulty ∷ [])
    "formalise Bayesian graph classification and noisy-label robustness separately; require same-object receipt before War Skull weld"
    "post-2023 War Skull technical lead/code custodian plus primary event carrier")
  "DASHI.GameTheory.FengYangheMilitaryAIGameStatisticsBidiExact"
  "Real algorithms do not create a shared classified programme with other roster science."

zhouGuangyuanFibre : ScientistTechnologyFibre
zhouGuangyuanFibre = scientist-technology-fibre
  "Zhou Guangyuan"
  "low-shrinkage high-temperature polyimide aerogels using benzhydrylidenefluorene diamines"
  "Chemical Engineering Journal article 147642"
  "DOI 10.1016/j.cej.2023.147642"
  (mkCarrier "polymer/materials science" "polyimide-aerogel synthesis/process window" C.processWindow C.carrierPartial
    "monomer/synthesis controls producing low shrinkage, high porosity and thermal insulation"
    "DOI 10.1016/j.cej.2023.147642; DICP DNL2200"
    "Published properties are public; scale-up/process/patent/enterprise-transfer windows remain partially mapped.")
  (mkUse "high-temperature thermal insulation using low-shrinkage polyimide aerogels" sourceBackedIntended
    (mkTransformation "polyimide aerogel thermal insulation"
      (T.governingPhysics ∷ T.constitutiveConfiguration ∷ [])
      (T.operatingWindow ∷ T.validationCorpus ∷ T.uncertaintyModel ∷ T.tacitExecutionKnowledge ∷ [])
      "DOI 10.1016/j.cej.2023.147642"
      "Intended use is high-temperature insulation with measured structure-property tradeoffs.")
    "CEJ/DICP" "Aerogel performance is a measured material property, not a generic 'supermaterial' label.")
  (mkUse "lightweight thermal protection for aerospace/energy instrumentation" documentedEngineeringInterface
    (mkTransformation "lightweight extreme-temperature insulation"
      (T.constitutiveConfiguration ∷ T.applicationGeometry ∷ [])
      (T.operatingWindow ∷ T.qualificationEvidence ∷ T.validationCorpus ∷ [])
      "thermal-insulation engineering interface"
      "New geometry, atmosphere and cycling require application-specific qualification.")
    "materials application interface" "Compatibility does not prove a particular aerospace programme.")
  (mkReverse
    (T.acquireConstitutiveConfiguration ∷ T.acquireOperatingWindow ∷ T.acquireQualificationEvidence ∷ T.acquireValidationCorpus ∷ T.acquireTacitExecutionKnowledge ∷ T.acquireSuccessorHandover ∷ [])
    (C.carrierReplacementDifficulty ∷ C.personCarrierPossession ∷ [])
    "formalise synthesis to shrinkage/porosity to thermal-conductivity/temperature response in SI units"
    "map Hu Yanming/Wang Rui successor groups to exact patents, process windows and enterprise transfers")
  "DASHI.Culture.ChineseStrategicScientistRosterSnowballExact"
  "Named post-loss centre leadership does not automatically transfer every patent/process object."

liuDonghaoFibre : ScientistTechnologyFibre
liuDonghaoFibre = scientist-technology-fibre
  "Liu Donghao"
  "DSMM/data-security maturity governance across collection, transmission, storage, processing, exchange and destruction"
  "GB/T 37988-2019 context and institutional DSMM implementation work"
  "GB/T 37988-2019"
  (mkCarrier "data-security governance" "DSMM assessment/integration workflow" C.integrationProcedure C.carrierPartial
    "data-lifecycle security maturity assessment and organisational implementation"
    "GB/T 37988-2019 context; institutional lecture surface"
    "The governance/maturity kernel is bounded; exact Liu-authored standard clauses/methods remain to be welded.")
  (mkUse "assess and improve organisational data-security maturity" sourceBackedIntended
    (mkTransformation "data-security maturity governance"
      (T.sourceOrAlgorithmImplementation ∷ T.integrationWorkflow ∷ [])
      (T.validationCorpus ∷ T.uncertaintyModel ∷ T.tacitExecutionKnowledge ∷ [])
      "DSMM institutional context"
      "Intended use is governance/maturity assessment rather than a claim of cryptographic invention.")
    "institutional DSMM work" "Generic cybersecurity capability is not inherited without source-specific work.")
  (mkUse "governance layer for multi-institution scientific data and engineering pipelines" documentedEngineeringInterface
    (mkTransformation "research-data security governance"
      (T.integrationWorkflow ∷ T.uncertaintyModel ∷ [])
      (T.validationCorpus ∷ T.tacitExecutionKnowledge ∷ [])
      "data-governance engineering interface"
      "The lifecycle model can structure governance of research/engineering data with domain-specific controls.")
    "governance interface" "Governance compatibility does not prove access to another scientist's data.")
  (mkReverse
    (T.acquireValidationCorpus ∷ T.acquireUncertaintyModel ∷ T.acquireIntegrationWorkflow ∷ T.acquireTacitExecutionKnowledge ∷ T.acquireSuccessorHandover ∷ [])
    (C.personCarrierPossession ∷ C.carrierIntegrationBreadth ∷ [])
    "recover exact Liu-authored standards contributions, maturity rules, papers and patents"
    "date Liu-to-Liao governance transition and first post-loss DSMM/project custody")
  "DASHI.Culture.ChineseStrategicScientistRosterSnowballExact"
  "Data-security governance does not imply possession of classified scientific data."

zhangXiaoxinFibre : ScientistTechnologyFibre
zhangXiaoxinFibre = scientist-technology-fibre
  "Zhang Xiaoxin"
  "space-weather prediction and Fengyun monitoring: CME-driven geomagnetic-storm modelling plus payload/ground-system leadership"
  "A New Method for Predicting Non-Recurrent Geomagnetic Storms"
  "DOI 10.1029/2023SW003522; ORCID 0000-0002-7759-7402"
  (mkCarrier "space-weather prediction" "CEEMDAN-CWT forecasting algorithm/data pipeline" C.sourceCodeOrAlgorithm C.carrierPublic
    "spectral whitening, decomposition/wavelet features and geomagnetic-storm prediction"
    "DOI 10.1029/2023SW003522"
    "Forecast algorithm is public; operational payload calibration and ground-system state are a separate carrier.")
  (mkUse "forecast non-recurrent geomagnetic storms and support space-weather monitoring" sourceBackedIntended
    (mkTransformation "space-weather forecast pipeline"
      (T.governingPhysics ∷ T.sourceOrAlgorithmImplementation ∷ T.uncertaintyModel ∷ [])
      (T.validationCorpus ∷ T.integrationWorkflow ∷ [])
      "DOI 10.1029/2023SW003522"
      "Intended use is forecast/monitoring; payload hardware remains separate.")
    "Space Weather paper / NSMC programme" "Publication after death may be pre-death work and is not a role-continuity receipt.")
  (mkUse "spacecraft operations and mission-risk forecast input" documentedEngineeringInterface
    (mkTransformation "space-environment risk forecast"
      (T.governingPhysics ∷ T.sourceOrAlgorithmImplementation ∷ T.uncertaintyModel ∷ [])
      (T.validationCorpus ∷ T.integrationWorkflow ∷ [])
      "space-weather operations interface"
      "Forecast products can inform mission operations with independent operational thresholds.")
    "space-weather engineering interface" "Forecast use does not imply command authority or a shared programme.")
  (mkReverse
    (T.acquireValidationCorpus ∷ T.acquireUncertaintyModel ∷ T.acquireIntegrationWorkflow ∷ T.acquireSuccessorHandover ∷ [])
    (C.personCarrierPossession ∷ C.carrierIntegrationBreadth ∷ [])
    "formalise spectral-whitening plus CEEMDAN-CWT pipeline, validation and metrics separately from payload calibration"
    "dated NSMC/Fengyun successor and committee reconstitution plus 2025 manuscript chronology")
  "DASHI.Culture.ChineseStrategicScientistRosterSnowballExact"
  "Current stale committee pages do not establish active post-loss role state."

zhangDaibingFibre : ScientistTechnologyFibre
zhangDaibingFibre = scientist-technology-fibre
  "Zhang Daibing"
  "UAV autonomous landing, path following, localisation, formation and unmanned-system control"
  "NUDT/BUAA/Robot UAV-control publication corpus"
  "DOI 10.11887/j.cn.201801023; DOI 10.13700/j.bh.1001-5965.2016.0679; DOI 10.13973/j.cnki.robot.2017.0160"
  (mkCarrier "autonomous systems control" "UAV guidance/localisation/control algorithms" C.sourceCodeOrAlgorithm C.carrierPublic
    "autonomous landing, path following, multisensor localisation and formation control"
    "three DOI-level UAV publications"
    "Algorithms are public; exact commercial/NUDT code and field configuration remain distinct carriers.")
  (mkUse "autonomous UAV landing, localisation, path following and formation" sourceBackedIntended
    (mkTransformation "UAV autonomous control"
      (T.governingPhysics ∷ T.sourceOrAlgorithmImplementation ∷ T.uncertaintyModel ∷ [])
      (T.applicationGeometry ∷ T.validationCorpus ∷ T.failureHistory ∷ [])
      "Zhang Daibing publication corpus"
      "Intended use is unmanned-aircraft control and autonomy.")
    "DOI publication corpus" "Published control laws do not establish any particular military deployment.")
  (mkUse "autonomous inspection/science drones in hazardous or remote environments" crossDomainCandidate
    (mkTransformation "autonomous science/inspection mobility"
      (T.sourceOrAlgorithmImplementation ∷ T.uncertaintyModel ∷ [])
      (T.applicationGeometry ∷ T.validationCorpus ∷ T.failureHistory ∷ T.integrationWorkflow ∷ [])
      "autonomy engineering interface"
      "Control primitives can be adapted to benign inspection/science missions after revalidation.")
    "cross-domain autonomy candidate" "Possible benign reuse is not historical use.")
  (mkReverse
    (T.acquireApplicationGeometry ∷ T.acquireFailureHistory ∷ T.acquireValidationCorpus ∷ T.acquireUncertaintyModel ∷ T.acquireSuccessorHandover ∷ [])
    (C.personCarrierPossession ∷ C.carrierReplacementDifficulty ∷ [])
    "formalise one source-exact guidance/localisation/control law and its test error/robustness envelope"
    "primary Yunzhihang governance record and named NUDT/company project custodian")
  "DASHI.Culture.ChineseStrategicScientistRosterSnowballExact"
  "Control science can be reused across mission types; that does not establish a shared programme."

liMinyongFibre : ScientistTechnologyFibre
liMinyongFibre = scientist-technology-fibre
  "Li Minyong"
  "photopharmacology and fluorescent molecular probes for target visualisation"
  "azobenzene in-vivo photopharmacology review and alpha1-adrenergic receptor probe patents"
  "DOI 10.1002/med.22120; CN201110101082.5; CN201110100874.0"
  (mkCarrier "medicinal chemistry / molecular imaging" "photoswitch/probe design and response carrier" C.constitutiveParameters C.carrierPublic
    "photoswitch state, target binding, fluorescence/physiological readout and reversibility"
    "DOI 10.1002/med.22120; fluorescent-probe patents"
    "Publication/patent science is public; exact lab/project continuation and compound-development state remain separate.")
  (mkUse "light-controlled pharmacology and disease-target molecular visualisation" sourceBackedIntended
    (mkTransformation "photopharmacology / molecular probe workflow"
      (T.governingPhysics ∷ T.constitutiveConfiguration ∷ [])
      (T.operatingWindow ∷ T.validationCorpus ∷ T.uncertaintyModel ∷ [])
      "Li Minyong publication/patent corpus"
      "Intended use is controlled molecular perturbation and visualisation.")
    "DOI/patent corpus" "Review authorship and patent objects do not themselves prove clinical efficacy.")
  (mkUse "targeted diagnostics and externally controlled biomedical research assays" documentedEngineeringInterface
    (mkTransformation "controlled molecular diagnostic assay"
      (T.constitutiveConfiguration ∷ T.sourceOrAlgorithmImplementation ∷ [])
      (T.operatingWindow ∷ T.validationCorpus ∷ T.qualificationEvidence ∷ [])
      "biomedical assay interface"
      "New targets and biological contexts require independent validation.")
    "biomedical engineering interface" "Possible application does not imply a deployed therapy.")
  (mkReverse
    (T.acquireConstitutiveConfiguration ∷ T.acquireOperatingWindow ∷ T.acquireValidationCorpus ∷ T.acquireQualificationEvidence ∷ T.acquireSuccessorHandover ∷ [])
    (C.personCarrierPossession ∷ C.carrierReplacementDifficulty ∷ [])
    "select one photoswitch/probe and formalise wavelength/state, binding, readout and reversibility"
    "named post-loss lab/project/patent/student custodian and Hainan transition")
  "DASHI.Culture.ChineseStrategicScientistRosterSnowballExact"
  "Molecular-control capability is not a generic bioengineering super-capability without target-specific evidence."

fangDainingFibre : ScientistTechnologyFibre
fangDainingFibre = scientist-technology-fibre
  "Fang Daining"
  "multifield mechanics and elastic-metamaterial inverse design for prescribed eigenmodes/dispersion"
  "Force-field-induced energy-based design method for arbitrary prescribed modes in elastic metamaterials"
  "DOI 10.1016/j.jmps.2025.106144"
  (mkCarrier "mechanics / metamaterial design" "inverse-design energy map and geometry" C.inverseModel C.carrierPublic
    "force-field-induced energy mapping to prescribed modes and dispersion, including negative-group-velocity validation"
    "DOI 10.1016/j.jmps.2025.106144"
    "Published inverse-design method is public; project/code/experimental-state custody remains separate.")
  (mkUse "inverse-design elastic metamaterials with prescribed mode/dispersion behaviour" sourceBackedIntended
    (mkTransformation "elastic metamaterial inverse design"
      (T.governingPhysics ∷ T.sourceOrAlgorithmImplementation ∷ T.constitutiveConfiguration ∷ [])
      (T.applicationGeometry ∷ T.validationCorpus ∷ T.uncertaintyModel ∷ [])
      "DOI 10.1016/j.jmps.2025.106144"
      "Intended use is structural/wave inverse design.")
    "JMPS 2025" "Mechanical metamaterial architecture is distinct from Reza gamma-prime alloy microstructure.")
  (mkUse "adaptive vibration/wave-control structures and resilient sensing platforms" crossDomainCandidate
    (mkTransformation "adaptive structural wave control"
      (T.governingPhysics ∷ T.sourceOrAlgorithmImplementation ∷ T.constitutiveConfiguration ∷ [])
      (T.applicationGeometry ∷ T.validationCorpus ∷ T.qualificationEvidence ∷ [])
      "metamaterial engineering interface"
      "Transfer to a system requires source-exact geometry, loads and qualification.")
    "cross-domain structural design candidate" "Possible use does not imply a historical aerospace or classified programme.")
  (mkReverse
    (T.acquireApplicationGeometry ∷ T.acquireConstitutiveConfiguration ∷ T.acquireValidationCorpus ∷ T.acquireUncertaintyModel ∷ T.acquireSuccessorHandover ∷ [])
    (C.carrierIntegrationBreadth ∷ C.personCarrierPossession ∷ [])
    "formalise energy map to eigenmode/dispersion constraints and negative-group-velocity finite witness"
    "post-loss BIT project-level handover for advanced-structure/metamaterial/extreme-environment work")
  "DASHI.Physics.Materials.FangDainingActiveMechanicalMetamaterialBidiExact"
  "Institutional continuity does not pay project-level code/IP custody."

yanHongFibre : ScientistTechnologyFibre
yanHongFibre = scientist-technology-fibre
  "Yan Hong"
  "supersonic/hypersonic inlet shock-boundary-layer control using thermal excitation; plasma-flow-control programme is a separate fibre"
  "Control of shock/boundary layer interaction in supersonic inlet using thermal excitation"
  "DOI 10.7638/kqdlxxb-2013.0102"
  (mkCarrier "high-speed aerodynamics" "thermal-excitation inlet-flow control configuration" C.hardwareConfiguration C.carrierPublic
    "thermal excitation applied to supersonic inlet shock/boundary-layer interaction"
    "DOI 10.7638/kqdlxxb-2013.0102"
    "Source-exact thermal-control work is public; later plasma-flow-control work remains separately source-welded.")
  (mkUse "control shock/boundary-layer interaction and separation in a supersonic inlet" sourceBackedIntended
    (mkTransformation "supersonic inlet thermal flow control"
      (T.governingPhysics ∷ T.applicationGeometry ∷ [])
      (T.operatingWindow ∷ T.validationCorpus ∷ T.uncertaintyModel ∷ [])
      "DOI 10.7638/kqdlxxb-2013.0102"
      "Intended use is high-speed inlet flow control.")
    "source-exact journal object" "Thermal excitation does not automatically weld to later plasma actuators.")
  (mkUse "high-speed-flow experimental control/diagnostics testbed" documentedEngineeringInterface
    (mkTransformation "high-speed flow-control testbed"
      (T.governingPhysics ∷ T.applicationGeometry ∷ [])
      (T.operatingWindow ∷ T.validationCorpus ∷ T.uncertaintyModel ∷ T.integrationWorkflow ∷ [])
      "aerodynamics engineering interface"
      "A benign experimental/test application; new vehicle geometry and conditions require independent validation.")
    "high-speed-flow engineering interface" "Possible use does not identify a weapons programme.")
  (mkReverse
    (T.acquireApplicationGeometry ∷ T.acquireOperatingWindow ∷ T.acquireValidationCorpus ∷ T.acquireUncertaintyModel ∷ T.acquireSuccessorHandover ∷ [])
    (C.personCarrierPossession ∷ C.carrierReplacementDifficulty ∷ [])
    "formalise thermal-excitation location/power to shock/separation response on the source-exact inlet"
    "dated NPU committee/project roster naming successor for inlet/plasma/numerical-wind-tunnel work")
  "DASHI.Physics.Aerospace.YanHongHypersonicFlowControlBidiExact"
  "Thermal and plasma flow-control fibres remain separate until exact source identity welds them."

------------------------------------------------------------------------
-- Exact 20-fibre roster.
------------------------------------------------------------------------

twentyScientistScienceFibres : List ScientistTechnologyFibre
twentyScientistScienceFibres =
  nunoLoureiroFibre ∷ joshuaLeBlancFibre ∷ frankMaiwaldFibre ∷ monicaRezaFibre ∷
  carlGrillmairFibre ∷ michaelHicksFibre ∷ williamNeilMcCaslandFibre ∷
  anthonyChavezFibre ∷ jasonThomasFibre ∷ amyEskridgeFibre ∷ ningLiFibre ∷
  chenShumingFibre ∷ fengYangheFibre ∷ zhouGuangyuanFibre ∷ liuDonghaoFibre ∷
  zhangXiaoxinFibre ∷ zhangDaibingFibre ∷ liMinyongFibre ∷ fangDainingFibre ∷
  yanHongFibre ∷ []

twentyScientistScienceFibreCount : Nat
twentyScientistScienceFibreCount = 20

------------------------------------------------------------------------
-- Application projection and factorisation.
--
-- The projection deliberately retains only the two declared application labels.
-- These queries factor through that projection.  Historical deployment,
-- provenance, programme membership and event cause are different queries and
-- receive no constructor from this surface.
------------------------------------------------------------------------

record ApplicationProjection : Set where
  constructor application-projection
  field
    projectedIntended : String
    projectedPossible : String

open ApplicationProjection public

data FibreApplicationQuery : Set where
  intendedApplicationQuery possibleApplicationQuery : FibreApplicationQuery

fibreApplicationQuestions : Q.InquiryQuestionFamily ScientistTechnologyFibre FibreApplicationQuery
fibreApplicationQuestions = Q.inquiryQuestionFamily (λ query → String) ask
  where
    ask : (query : FibreApplicationQuery) → ScientistTechnologyFibre → String
    ask intendedApplicationQuery fibre = applicationLabel (intendedApplication fibre)
    ask possibleApplicationQuery fibre = applicationLabel (possibleApplication fibre)

projectApplications : ScientistTechnologyFibre → ApplicationProjection
projectApplications fibre = application-projection
  (applicationLabel (intendedApplication fibre))
  (applicationLabel (possibleApplication fibre))

intendedApplicationFactors :
  Q.FactorsThrough fibreApplicationQuestions projectApplications intendedApplicationQuery
intendedApplicationFactors = Q.factorsThrough projectedIntended proof
  where
    proof : (fibre : ScientistTechnologyFibre) →
      Q.ask fibreApplicationQuestions intendedApplicationQuery fibre ≡
      projectedIntended (projectApplications fibre)
    proof fibre = refl

possibleApplicationFactors :
  Q.FactorsThrough fibreApplicationQuestions projectApplications possibleApplicationQuery
possibleApplicationFactors = Q.factorsThrough projectedPossible proof
  where
    proof : (fibre : ScientistTechnologyFibre) →
      Q.ask fibreApplicationQuestions possibleApplicationQuery fibre ≡
      projectedPossible (projectApplications fibre)
    proof fibre = refl

------------------------------------------------------------------------
-- Integrated system-level use surface.
------------------------------------------------------------------------

data IntegratedSubsystemRole : Set where
  plasmaModeling powerAndControls molecularDiagnostics extremeMaterials
  astronomicalInference planetaryCharacterisation structuralResilience
  acceleratorDiagnostics chemicalBiology mechanismDiscrimination
  hardwareVerification robustDecisionAI thermalMaterials dataSecurityGovernance
  spaceWeatherForecasting autonomousMobility photochemicalSensing
  metamaterialDesign highSpeedFlowControl : IntegratedSubsystemRole

record IntegratedFibreUse : Set where
  constructor integrated-fibre-use
  field
    usedPerson : String
    role : IntegratedSubsystemRole
    boundedUse : String

open IntegratedFibreUse public

record IntegratedScienceCapabilityBidi : Set where
  constructor integrated-science-capability-bidi
  field
    systemName : String
    fibres : List ScientistTechnologyFibre
    roleUses : List IntegratedFibreUse
    synthesis : H.CapabilitySynthesis
    systemReverseTargets : List T.TransformationReverseTarget
    intendedSystemUse : String
    possibleSystemUse : String
    systemBoundary : String

open IntegratedScienceCapabilityBidi public

integratedRoleUses : List IntegratedFibreUse
integratedRoleUses =
  integrated-fibre-use "Nuno F. G. Loureiro" plasmaModeling "magnetised-plasma modelling and numerical inference" ∷
  integrated-fibre-use "Joshua Kyle LeBlanc" powerAndControls "harsh-environment sensing, qualification and control" ∷
  integrated-fibre-use "Frank W. Maiwald" molecularDiagnostics "molecular/isomer sensing and calibrated spectroscopy" ∷
  integrated-fibre-use "Monica Jacinto / Monica Reza" extremeMaterials "oxygen-rich high-strength material/process survivability" ∷
  integrated-fibre-use "Carl J. Grillmair" astronomicalInference "weak-signal survey/matched-filter astronomical inference" ∷
  integrated-fibre-use "Michael David Hicks" planetaryCharacterisation "small-body photometric/spectral characterisation" ∷
  integrated-fibre-use "William Neil McCasland" structuralResilience "fault-tolerant sensor/actuator placement for flexible structures" ∷
  integrated-fibre-use "Anthony Chavez" acceleratorDiagnostics "pulsed-accelerator/radiographic engineering, identity-gated" ∷
  integrated-fibre-use "Jason R. Thomas" chemicalBiology "mechanistic assays and target-deconvolution workflow" ∷
  integrated-fibre-use "Amy Eskridge" mechanismDiscrimination "claimed-field mechanism comparison/test obligations, attribution-gated" ∷
  integrated-fibre-use "Ning Li" mechanismDiscrimination "precision superconducting-gravity null/constraint testing" ∷
  integrated-fibre-use "Chen Shuming" hardwareVerification "simulation-based digital-hardware verification" ∷
  integrated-fibre-use "Feng Yanghe" robustDecisionAI "noise-robust classification and decision-agent research" ∷
  integrated-fibre-use "Zhou Guangyuan" thermalMaterials "lightweight high-temperature polymer insulation" ∷
  integrated-fibre-use "Liu Donghao" dataSecurityGovernance "data-lifecycle security maturity and integration governance" ∷
  integrated-fibre-use "Zhang Xiaoxin" spaceWeatherForecasting "space-environment forecasting and monitoring input" ∷
  integrated-fibre-use "Zhang Daibing" autonomousMobility "autonomous landing/localisation/path-following control" ∷
  integrated-fibre-use "Li Minyong" photochemicalSensing "photoswitch/probe molecular sensing and control" ∷
  integrated-fibre-use "Fang Daining" metamaterialDesign "inverse-designed structural/wave behaviour" ∷
  integrated-fibre-use "Yan Hong" highSpeedFlowControl "high-speed inlet shock/boundary-layer control" ∷ []

integratedSynthesis : H.CapabilitySynthesis
integratedSynthesis = H.capability-synthesis
  H.multiMissionStrategicSpaceArchitecture
  (H.highEnergyPlasmaPhysics ∷ H.fissionPowerAndPropulsion ∷
   H.extremeEnvironmentMaterials ∷ H.acceleratorRadiographyDiagnostics ∷
   H.spacecraftSystemsEngineering ∷ H.navigationGuidanceAndTracking ∷
   H.planetaryDefenseAndNEOScience ∷ H.planetaryMassSpectrometryAndBiosignatures ∷
   H.astronomicalRemoteSensing ∷ H.chemicalBiologyAndLifeScience ∷ [])
  H.crossDomainEngineeringInference
  "existing DASHI capability-synthesis interfaces plus twenty source-bound science fibres"
  "A systems-engineering design space can combine modelling, power/control, sensing, materials, autonomy, environmental prediction and life-science diagnostics. This does not assert a historical programme or collaboration among the roster."

integratedTwentyScientistCapability : IntegratedScienceCapabilityBidi
integratedTwentyScientistCapability = integrated-science-capability-bidi
  "twenty-scientist multi-domain research and engineering capability surface"
  twentyScientistScienceFibres
  integratedRoleUses
  integratedSynthesis
  (T.acquireApplicationGeometry ∷ T.acquireCalibrationState ∷
   T.acquireConstitutiveConfiguration ∷ T.acquireClosureOrRegularisation ∷
   T.acquireOperatingWindow ∷ T.acquireFailureHistory ∷
   T.acquireQualificationEvidence ∷ T.acquireValidationCorpus ∷
   T.acquireUncertaintyModel ∷ T.acquireIntegrationWorkflow ∷
   T.acquireTacitExecutionKnowledge ∷ T.acquirePersonRoleWeld ∷
   T.acquireSuccessorHandover ∷ [])
  "compose independently source-backed modelling, control, sensing, materials, autonomy, security and scientific-inference fibres into a research/test platform while preserving each fibre's validation domain"
  "evaluate benign cross-domain applications such as long-duration science platforms, resilient autonomous laboratories, high-energy diagnostics ecosystems and multi-modal environmental/biological sensing, subject to fresh application-specific validation"
  "This is a capability-design object. It is not evidence that one historical system, programme, customer or selector assembled these people or their work."

allTwentyFibresAreRepresented : Bool
allTwentyFibresAreRepresented = true

------------------------------------------------------------------------
-- Promotion boundaries.
------------------------------------------------------------------------

possibleApplicationImpliesHistoricalDeployment : Bool
possibleApplicationImpliesHistoricalDeployment = false

technicalCompatibilityImpliesSameProgramme : Bool
technicalCompatibilityImpliesSameProgramme = false

integratedCapabilityImpliesRosterCollaboration : Bool
integratedCapabilityImpliesRosterCollaboration = false

scienceCarrierImpliesPersonPossession : Bool
scienceCarrierImpliesPersonPossession = false

institutionContinuityImpliesExactCapabilityTransfer : Bool
institutionContinuityImpliesExactCapabilityTransfer = false

applicationCandidateImpliesEventCause : Bool
applicationCandidateImpliesEventCause = false

allTwentyFibresPresentImpliesOneHistoricalSystem : Bool
allTwentyFibresPresentImpliesOneHistoricalSystem = false

intendedPossibleAreDifferentClaimKinds : Bool
intendedPossibleAreDifferentClaimKinds = true
