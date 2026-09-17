module DASHI.Physics.Chemistry.AtomicPeriodicTable369AdenylateKinasePhysicalDynamicsBridgeExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Physics.Chemistry.AtomicPeriodicTable369ChemistryHyperfibreBridgeExact as Hyper
import DASHI.Physics.Chemistry.AtomicPeriodicTable369ProteinDNA3DAdapterExact as ThreeD
import DASHI.Physics.Chemistry.AtomicPeriodicTable369AdenylateKinaseChemicalSystemExact as Chemical
import DASHI.Physics.Chemistry.AtomicPeriodicTable369AdenylateKinaseSIQuantityBridgeExact as SIAdK
import DASHI.Physics.Chemistry.AtomicPeriodicTable369AdenylateKinaseCollectiveVariableDefinitionAcquisitionExact as CV
import DASHI.Physics.Chemistry.AtomicPeriodicTable369AdenylateKinaseBEMetaAcquisitionExact as BEMeta
import DASHI.Physics.Chemistry.AtomicPeriodicTable369AdenylateKinaseWeightedNDimStateGraphExact as Graph
import DASHI.Physics.Chemistry.AtomicPeriodicTable369AdenylateKinaseCalibrationAttributionEnvelopeExact as Attr
import DASHI.Physics.Units.SI as SI

------------------------------------------------------------------------
-- GEOMETRY ALL THE WAY DOWN: ADK PHYSICAL-DYNAMICS BRIDGE
--
--   atoms/elements
--     -> molecular species
--     -> 3-D molecular/protein geometry
--     -> atomistic/process model
--     -> (theta1, theta2, dLN)
--     -> AdK state/kernel.
--
-- Every arrow is proof-/source-relevant.  This file deliberately exposes the
-- forgotten lower carrier at each abstraction boundary instead of beginning at
-- the state graph.  It is an adapter over existing atomic chemistry, molecular
-- geometry, SI, source-acquired CV and AdK graph owners; it is not a replacement
-- molecular-mechanics ontology.
------------------------------------------------------------------------

atomicToSpeciesReceipt : Hyper.AtomicToSpeciesReceipt
atomicToSpeciesReceipt = Chemical.adenylateAtomicToSpeciesReceipt

speciesToMoleculeReceipt : Hyper.SpeciesToMoleculeReceipt
speciesToMoleculeReceipt = Chemical.adenylateSpeciesToMoleculeReceipt

molecularThreeDSurface : Set₁
molecularThreeDSurface = ThreeD.molecularStereoSurface

proteinConformationSurface : Set₁
proteinConformationSurface = ThreeD.proteinConformationSurface

stateKernelSurface : Set
stateKernelSurface = Graph.AdKLandscapeState

articleDOI = Attr.articleDOI
adkQID = Attr.adkQID
adkUniProt = Attr.adkUniProt
openPDB = Attr.openPDB
closedPDB = Attr.closedPDB

------------------------------------------------------------------------
-- Atomistic/process role.
--
-- Li-Liu-Ji source-pay explicit atomistic long-timescale MD and BE-META as
-- process/method roles.  This bridge does NOT invent a missing force-field,
-- charge, solvent, electrostatics, thermostat/barostat or constraint parameter.
------------------------------------------------------------------------

data AtomisticProcessKind : Set where
  explicitAtomisticMolecularDynamics : AtomisticProcessKind
  biasExchangeMetadynamics : AtomisticProcessKind

record AtomisticProcessReceipt : Set where
  constructor atomistic-process-receipt
  field
    processKind : AtomisticProcessKind
    sourceIdentity : String
    sourceLocator : String
    configurationCarrier : String
    threeDimensionalGeometryCarrier : String
    potentialRole : String
    dynamicsRole : String
    environmentRole : String
    forceFieldParameterizationPaid : Bool
    solventModelPaid : Bool
    electrostaticsAlgorithmPaid : Bool
    integrationTimestepPaid : Bool
    thermostatBarostatMechanicsPaid : Bool
    interpretation : String
open AtomisticProcessReceipt public

explicitMDReceipt : AtomisticProcessReceipt
explicitMDReceipt = atomistic-process-receipt
  explicitAtomisticMolecularDynamics
  "Li, Liu and Ji 2015; DOI 10.1016/j.bpj.2015.06.059"
  "article abstract/conclusions: explicit long-timescale molecular dynamics, atomistic transition pathways/intermediate states"
  "time-indexed atomistic coordinates of the selected AdK chemical system"
  "3-D atomic coordinates; molecular identity/geometry remains upstream of the CV projection"
  "physical molecular-mechanics potential role required, exact force-field parameterization not promoted in this bridge"
  "time evolution of the atomistic configuration"
  "temperature/pressure and ligand context retained separately"
  false false false false false
  "source pays the atomistic-MD process role; detailed mechanics remain residual until same-object methods/source acquisition is attached"

beMetaProcessReceipt : AtomisticProcessReceipt
beMetaProcessReceipt = atomistic-process-receipt
  biasExchangeMetadynamics
  "Li, Liu and Ji 2015; DOI 10.1016/j.bpj.2015.06.059"
  "Materials and Methods / BE-META protocol; canonical protocol owner retains CV walls, Gaussian bias and sampling cadence"
  "atomistic configurations sampled under bias-exchange metadynamics"
  "same 3-D molecular configuration carrier projected to theta1/theta2/dLN"
  "physical molecular potential plus an explicitly added sampling-bias potential"
  "biased sampling dynamics; not an assertion that the Gaussian bias is physical free energy"
  "canonical protocol retains 300 K and 1 bar as source coordinates"
  false false false false false
  "method/process receipt only; bias parameters, source free-energy reconstruction and physical potential remain distinct roles"

------------------------------------------------------------------------
-- Exact observable-definition weld from 3-D atomistic geometry to CV space.
------------------------------------------------------------------------

record AtomisticToCVDefinitionReceipt : Set where
  constructor atomistic-to-cv-definition-receipt
  field
    atomisticInputCarrier : String
    thetaOne : CV.CollectiveVariableDefinition
    thetaTwo : CV.CollectiveVariableDefinition
    dLn : CV.CollectiveVariableDefinition
    thetaOneGeometryReading : String
    thetaTwoGeometryReading : String
    dLnGeometryReading : String
    sourceIdentityRetained : Bool
    sourceLocatorRetained : Bool
    residueDomainSelectionsRetained : Bool
    centerOfMassConstructionRetained : Bool
    createsNamedStateNumerics : Bool
open AtomisticToCVDefinitionReceipt public

canonicalAtomisticToCVDefinitionReceipt : AtomisticToCVDefinitionReceipt
canonicalAtomisticToCVDefinitionReceipt = atomistic-to-cv-definition-receipt
  "same-object 3-D atomistic AdK configuration"
  CV.thetaOneDefinition
  CV.thetaTwoDefinition
  CV.dLnDefinition
  "three-point center-of-mass geometry over the source-listed LID/hinge/CORE backbone residue groups"
  "three-point center-of-mass geometry over the source-listed NMP/CORE/hinge backbone residue groups"
  "Euclidean distance between LID and NMP domain centers of mass"
  true true true true false

------------------------------------------------------------------------
-- Executable projection interface.
--
-- A concrete trajectory consumer may inhabit this only by supplying actual
-- same-object coordinate evaluators.  Merely importing the Figure-1 definitions
-- or PDB/DOI identifiers does not construct these functions.
------------------------------------------------------------------------

record AtomisticCVProjection (Configuration : Set) : Set where
  constructor atomistic-cv-projection
  field
    thetaOneDegrees : Configuration → Nat
    thetaTwoDegrees : Configuration → Nat
    dLn : Configuration → SI.Quantity SI.Length SIAdK.angstromScale
    sameObjectGeometryReceipt : Configuration → String
    sourceObservableIdentityReceipt : String
open AtomisticCVProjection public

record CVStateClassifier (Configuration : Set)
                         (projection : AtomisticCVProjection Configuration) : Set where
  constructor cv-state-classifier
  field
    classify : Configuration → Graph.AdKLandscapeState
    stateRegionDefinitionReference : String
    classificationMethodReference : String
    classificationIsSourcePaidForAllConfigurations : Bool
open CVStateClassifier public

------------------------------------------------------------------------
-- The complete explicit chain is a dependent receipt.  Lower layers remain
-- inspectable after an AdK state has been produced.
------------------------------------------------------------------------

record AdKGeometryAllTheWayDownChain : Set₁ where
  constructor adk-geometry-all-the-way-down-chain
  field
    Configuration : Set
    atomicSpeciesWeld : Hyper.AtomicToSpeciesReceipt
    molecularGeometryWeld : Hyper.SpeciesToMoleculeReceipt
    process : AtomisticProcessReceipt
    cvDefinitionWeld : AtomisticToCVDefinitionReceipt
    cvProjection : AtomisticCVProjection Configuration
    stateClassifier : CVStateClassifier Configuration cvProjection
    provenanceReference : String
    identifierBundleReference : String
    lowerCarrierRetainedAfterClassification : Bool
open AdKGeometryAllTheWayDownChain public

------------------------------------------------------------------------
-- BE-META bias/state/kernel authority boundary.
------------------------------------------------------------------------

beMetaProtocol : BEMeta.BEMetaProtocol
beMetaProtocol = BEMeta.canonicalBEMetaProtocol

biasRoleReading : String
biasRoleReading =
  "the BE-META Gaussian term is an added sampling potential used to explore CV space; it is not identified with the underlying physical potential or with the reconstructed physical free-energy surface"

stateKernelReading : String
stateKernelReading =
  "WeightedNDimStateGraphExact is a mesoscopic projection of source-bounded CV/free-energy/path observations; it does not reconstruct the unique atomistic trajectory, force field, chemical microstate or catalytic mechanism"

------------------------------------------------------------------------
-- WrongType / attribution firewalls.
------------------------------------------------------------------------

data BiasPotentialEqualsPhysicalFreeEnergy : Set where
data CVStateGraphRecoversCompleteAtomisticDynamics : Set where
data IdentifiersCreateAtomisticState : Set where
data UnsourcedForceFieldParametersCanBePromoted : Set where
data ProteinIdentityDeterminesCVState : Set where

data StateClassificationErasesLowerCarrier : Set where

biasPotentialDoesNotEqualPhysicalFreeEnergy : BiasPotentialEqualsPhysicalFreeEnergy → ⊥
biasPotentialDoesNotEqualPhysicalFreeEnergy ()

cvStateGraphDoesNotRecoverCompleteAtomisticDynamics : CVStateGraphRecoversCompleteAtomisticDynamics → ⊥
cvStateGraphDoesNotRecoverCompleteAtomisticDynamics ()

identifiersDoNotCreateAtomisticState : IdentifiersCreateAtomisticState → ⊥
identifiersDoNotCreateAtomisticState ()

unsourcedForceFieldParametersCannotBePromoted : UnsourcedForceFieldParametersCanBePromoted → ⊥
unsourcedForceFieldParametersCannotBePromoted ()

proteinIdentityDoesNotDetermineCVState : ProteinIdentityDeterminesCVState → ⊥
proteinIdentityDoesNotDetermineCVState ()

stateClassificationNeedNotEraseLowerCarrier : StateClassificationErasesLowerCarrier → ⊥
stateClassificationNeedNotEraseLowerCarrier ()

record AdKPhysicalDynamicsBridgeBoundary : Set where
  constructor adk-physical-dynamics-bridge-boundary
  field
    atomElementLayerRetained : Bool
    molecularSpeciesLayerRetained : Bool
    threeDimensionalGeometryLayerRetained : Bool
    atomisticProcessLayerRetained : Bool
    collectiveVariableMapRetained : Bool
    adkStateKernelLayerRetained : Bool
    lowerCarrierRemainsExplicit : Bool
    biasPotentialEqualsPhysicalFreeEnergy : Bool
    cvStateGraphRecoversCompleteAtomisticDynamics : Bool
    identifiersCreateAtomisticState : Bool
    unsourcedForceFieldParametersPromoted : Bool
    bareProteinIdentityDeterminesCVState : Bool
    fullConcreteAtomisticEvaluatorPaidHere : Bool
open AdKPhysicalDynamicsBridgeBoundary public

canonicalAdKPhysicalDynamicsBridgeBoundary : AdKPhysicalDynamicsBridgeBoundary
canonicalAdKPhysicalDynamicsBridgeBoundary =
  adk-physical-dynamics-bridge-boundary
    true true true true true true true
    false false false false false false
