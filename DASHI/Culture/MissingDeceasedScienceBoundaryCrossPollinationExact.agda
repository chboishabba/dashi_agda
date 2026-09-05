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

record ScienceBoundaryVoxel : Set where
  constructor science-boundary-voxel
  field caseName : String; scientificCarrier : String; scientificEvidenceKind : S.ScientificEvidenceKind; releaseLayer : L.ReleaseLayer; boundaryKind : K.BoundaryKind; sourceReference : String; boundedReading : String
open ScienceBoundaryVoxel public
poamsPublicModelVoxel = science-boundary-voxel "POAMS" "reformulated spin-coupled-force model and preliminary experiment" S.mathematicalReformulation L.publicTechnicalReport K.contractualProprietaryBoundary "NASA/TM-20205010911 / SAA8-1519855" "Public model/report does not establish that all V5 data, hardware or Institute derivatives are public."
rezaPatentScienceVoxel = science-boundary-voxel "Jacinto-Hardwick alloy patent" "composition windows, qualitative element roles, fabrication sequence and example performance" S.constitutiveOrEngineeringMechanism L.publicTechnicalReport K.ordinaryPatentConfidentiality "US20030053926A1 / US09/954,835" "Patent publication exposes real design knowledge, not necessarily complete heat treatment, microstructure, raw data or tacit know-how."
leblancPublicICVoxel = science-boundary-voxel "NASA FSP/SNP I&C" "technology-maturation architecture, FICS database concept, working groups and growth path" S.constitutiveOrEngineeringMechanism L.publicTechnicalReport K.internalInstitutionalBoundary "NASA NTRS 20250008475" "Public architecture does not establish public database contents or all qualification/design artifacts."
viriatoPublicNumericsVoxel = science-boundary-voxel "Viriato" "KREHM/KRMHD models, algorithms, numerical architecture and benchmarks" S.numericalMethod L.publicTechnicalReport K.unresolvedBoundaryKind "Loureiro et al. CPC 206 (2016); arXiv:1505.02649" "Deep numerical externalisation does not itself establish public source-code release or a prior bounded state."
scorpiusPublicArchitectureVoxel = science-boundary-voxel "DARHT / Scorpius" "linear-induction accelerator and electron-beam-to-bremsstrahlung radiography architecture" S.constitutiveOrEngineeringMechanism L.publicTechnicalReport K.classifiedNationalSecurityBoundary "LANL/NNSA public sources" "Public accelerator physics must not inherit the status of experiment-specific classified weapons data."
maiwaldPublicActionSpectroscopyVoxel = science-boundary-voxel "Maiwald action spectroscopy" "ESI, cryogenic messenger tagging, mass selection, IR photodissociation, fragment detection and isomer discrimination" S.experimentalObservation L.publicTechnicalReport K.internalInstitutionalBoundary "JPL FY23 SURP poster SP23012p" "Public experimental chain does not itself establish release of every design file, raw dataset or mission-qualified implementation."
record ScienceBoundaryFirewall : Set where constructor science-boundary-firewall; field publicMechanismDescriptionMeansRawDataPublic : Bool; publicMechanismDescriptionMeansRawDataPublicIsFalse : publicMechanismDescriptionMeansRawDataPublic ≡ false; publicNumericalArchitectureMeansSourceCodePublic : Bool; publicNumericalArchitectureMeansSourceCodePublicIsFalse : publicNumericalArchitectureMeansSourceCodePublic ≡ false; publicPatentMeansTacitManufacturingKnowHowPublic : Bool; publicPatentMeansTacitManufacturingKnowHowPublicIsFalse : publicPatentMeansTacitManufacturingKnowHowPublic ≡ false; publicAcceleratorArchitectureMeansExperimentSpecificClassifiedDataPublic : Bool; publicAcceleratorArchitectureMeansExperimentSpecificClassifiedDataPublicIsFalse : publicAcceleratorArchitectureMeansExperimentSpecificClassifiedDataPublic ≡ false; publicExperimentalPosterMeansMissionQualifiedInstrumentPubliclyReproducible : Bool; publicExperimentalPosterMeansMissionQualifiedInstrumentPubliclyReproducibleIsFalse : publicExperimentalPosterMeansMissionQualifiedInstrumentPubliclyReproducible ≡ false
canonicalScienceBoundaryFirewall = science-boundary-firewall false refl false refl false refl false refl false refl
