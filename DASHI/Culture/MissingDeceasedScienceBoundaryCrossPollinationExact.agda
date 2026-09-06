module DASHI.Culture.MissingDeceasedScienceBoundaryCrossPollinationExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

import DASHI.Core.LayeredKnowledgeReleaseBidiExact as L
import DASHI.Core.KnowledgeBoundaryKindBidiExact as K
import DASHI.Core.ScientificMechanismEvidenceBidiExact as S

import DASHI.Physics.POAMSScientificMechanismBoundaryExact as P
import DASHI.Physics.RezaBurnResistantAlloyScienceExact as R
import DASHI.Physics.LeBlancFissionInstrumentationControlScienceExact as F
import DASHI.Physics.Plasma.LoureiroViriatoNumericsScienceExact as V
import DASHI.Physics.ScorpiusRadiographicAcceleratorScienceExact as C
import DASHI.Physics.MaiwaldActionSpectroscopyScienceExact as M

------------------------------------------------------------------------
-- SCIENCE x KNOWLEDGE-BOUNDARY HYPERVOXELS
--
-- Each public/private coordinate must name the scientific carrier that actually
-- occupies that layer.  Public status does not propagate between related but
-- non-identical scientific objects.
------------------------------------------------------------------------

record ScienceBoundaryVoxel : Set where
  constructor science-boundary-voxel
  field
    caseName : String
    scientificCarrier : String
    scientificEvidenceKind : S.ScientificEvidenceKind
    releaseLayer : L.ReleaseLayer
    boundaryKind : K.BoundaryKind
    sourceReference : String
    boundedReading : String

open ScienceBoundaryVoxel public

poamsPublicModelVoxel : ScienceBoundaryVoxel
poamsPublicModelVoxel = science-boundary-voxel
  "POAMS"
  "reformulated spin-coupled-force model and preliminary experiment reported in NASA/TM-20205010911"
  S.mathematicalReformulation
  L.publicTechnicalReport
  K.contractualProprietaryBoundary
  "NASA/TM-20205010911 / SAA8-1519855"
  "The public layer contains a model, derivation and preliminary measurements; it does not establish that all V5 data, hardware or later Institute-derived results are public."

rezaPatentScienceVoxel : ScienceBoundaryVoxel
rezaPatentScienceVoxel = science-boundary-voxel
  "Jacinto-Hardwick alloy patent"
  "alloy composition windows, qualitative element roles, fabrication sequence and example performance claims"
  S.constitutiveOrEngineeringMechanism
  L.publicTechnicalReport
  K.ordinaryPatentConfidentiality
  "US20030053926A1 / US09/954,835"
  "Patent publication exposes composition/mechanism/process description, but not necessarily complete heat-treatment, microstructure, raw test data or tacit manufacturing know-how."

leblancPublicICVoxel : ScienceBoundaryVoxel
leblancPublicICVoxel = science-boundary-voxel
  "NASA FSP/SNP I&C"
  "technology-maturation architecture, FICS database concept, working groups and growth path"
  S.constitutiveOrEngineeringMechanism
  L.publicTechnicalReport
  K.internalInstitutionalBoundary
  "NASA NTRS 20250008475"
  "The public artifact exposes programme architecture and maturation logic, not the complete contents/access controls of the live FICS/CINDI database or all component qualification data."

viriatoPublicNumericsVoxel : ScienceBoundaryVoxel
viriatoPublicNumericsVoxel = science-boundary-voxel
  "Viriato"
  "KREHM/KRMHD models, operator splitting, parallel/perpendicular schemes, Hermite velocity representation and benchmarks"
  S.numericalMethod
  L.publicTechnicalReport
  K.unresolvedBoundaryKind
  "Loureiro et al. CPC 206 (2016) 45-63; arXiv:1505.02649"
  "The paper deeply externalises numerical architecture; public source-code release and any prior bounded state of the same code artifact remain unresolved."

scorpiusPublicArchitectureVoxel : ScienceBoundaryVoxel
scorpiusPublicArchitectureVoxel = science-boundary-voxel
  "DARHT / Scorpius"
  "linear-induction accelerator and electron-beam-to-bremsstrahlung radiography architecture"
  S.constitutiveOrEngineeringMechanism
  L.publicTechnicalReport
  K.classifiedNationalSecurityBoundary
  "LANL/NNSA public DARHT and Scorpius sources"
  "Public accelerator physics must not inherit the status of experiment-specific classified weapons-design, plutonium-state or inverse-model data."

maiwaldPublicActionSpectroscopyVoxel : ScienceBoundaryVoxel
maiwaldPublicActionSpectroscopyVoxel = science-boundary-voxel
  "Maiwald cryogenic ion action spectroscopy"
  "ESI, cryogenic messenger tagging, mass selection, IR photodissociation, fragment detection and isomer discrimination"
  S.experimentalObservation
  L.publicTechnicalReport
  K.internalInstitutionalBoundary
  "JPL FY23 SURP poster SP23012p"
  "The public poster exposes an unusually deep experimental chain, but it does not by itself establish public release of every apparatus design file, raw dataset or mission-qualified implementation."

record ScienceBoundaryFirewall : Set where
  constructor science-boundary-firewall
  field
    publicMechanismDescriptionMeansRawDataPublic : Bool
    publicMechanismDescriptionMeansRawDataPublicIsFalse :
      publicMechanismDescriptionMeansRawDataPublic ≡ false
    publicNumericalArchitectureMeansSourceCodePublic : Bool
    publicNumericalArchitectureMeansSourceCodePublicIsFalse :
      publicNumericalArchitectureMeansSourceCodePublic ≡ false
    publicPatentMeansTacitManufacturingKnowHowPublic : Bool
    publicPatentMeansTacitManufacturingKnowHowPublicIsFalse :
      publicPatentMeansTacitManufacturingKnowHowPublic ≡ false
    publicAcceleratorArchitectureMeansExperimentSpecificClassifiedDataPublic : Bool
    publicAcceleratorArchitectureMeansExperimentSpecificClassifiedDataPublicIsFalse :
      publicAcceleratorArchitectureMeansExperimentSpecificClassifiedDataPublic ≡ false
    publicExperimentalPosterMeansMissionQualifiedInstrumentPubliclyReproducible : Bool
    publicExperimentalPosterMeansMissionQualifiedInstrumentPubliclyReproducibleIsFalse :
      publicExperimentalPosterMeansMissionQualifiedInstrumentPubliclyReproducible ≡ false

canonicalScienceBoundaryFirewall : ScienceBoundaryFirewall
canonicalScienceBoundaryFirewall = science-boundary-firewall
  false refl
  false refl
  false refl
  false refl
  false refl
