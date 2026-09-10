module DASHI.Wikimedia.IbrahimSnowballPortableComputingSecondHopExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Wikimedia.ScientificReferenceEntityAtlasExact as Atlas
import DASHI.Wikimedia.SnowballExternalIdentityAvailabilityExact as Identity
import DASHI.Wikimedia.IbrahimSnowballPortableComputingQidsExact as First

------------------------------------------------------------------------
-- IBRAHIM SECOND-HOP PORTABLE-COMPUTING GRAPH
--
-- External graph identities are navigation coordinates only.  Primary
-- technical statements about Arm Neon/SVE, OpenMP target offload, and Google
-- TPU/MXU/systolic-array structure remain owned by their first-party sources.
------------------------------------------------------------------------

misdEntity : Atlas.ScientificReferenceEntity
misdEntity = Atlas.verified "MISD" Atlas.conceptEntity "Q1190992"
  "Wikidata identity checked 2026-09-10; part of Flynn's taxonomy"

mimdEntity : Atlas.ScientificReferenceEntity
mimdEntity = Atlas.verified "MIMD" Atlas.conceptEntity "Q1149237"
  "Wikidata identity checked 2026-09-10; part of Flynn's taxonomy"

matrixMultiplicationEntity : Atlas.ScientificReferenceEntity
matrixMultiplicationEntity = Atlas.verified "matrix multiplication" Atlas.conceptEntity "Q1049914"
  "Wikidata identity checked 2026-09-10"

sisdEntity : Atlas.ScientificReferenceEntity
sisdEntity = Atlas.unresolved "SISD" Atlas.conceptEntity
  "SISD concept externally observed but no exact trustworthy Wikidata QID safely promoted in this pass"

neonEntity : Atlas.ScientificReferenceEntity
neonEntity = Atlas.unresolved "Arm Neon / Advanced SIMD" Atlas.conceptEntity
  "primary Arm source inspected; no exact Wikidata QID safely promoted in this pass"

sveEntity : Atlas.ScientificReferenceEntity
sveEntity = Atlas.unresolved "Arm Scalable Vector Extension" Atlas.conceptEntity
  "primary Arm source inspected; no exact Wikidata QID safely promoted in this pass"

smeEntity : Atlas.ScientificReferenceEntity
smeEntity = Atlas.unresolved "Arm Scalable Matrix Extension" Atlas.conceptEntity
  "primary Arm source inspected; no exact Wikidata QID safely promoted in this pass"

openMPTargetEntity : Atlas.ScientificReferenceEntity
openMPTargetEntity = Atlas.unresolved "OpenMP target offload" Atlas.conceptEntity
  "primary OpenMP accelerator-model source inspected; no exact Wikidata QID safely promoted"

systolicArrayEntity : Atlas.ScientificReferenceEntity
systolicArrayEntity = Atlas.unresolved "systolic array" Atlas.conceptEntity
  "TPU Wikidata item records systolic-array parts, but no standalone exact QID safely promoted in this pass"

matrixMultiplyUnitEntity : Atlas.ScientificReferenceEntity
matrixMultiplyUnitEntity = Atlas.unresolved "matrix multiply unit (MXU)" Atlas.conceptEntity
  "Google primary TPU documentation inspected; no exact Wikidata QID safely promoted"

------------------------------------------------------------------------
-- Explicit QID demands for verified second-hop identities.
------------------------------------------------------------------------

misdQidDemand : Identity.ExternalIdentityDemand
misdQidDemand = Identity.mkOptionalIdentityDemand
  "Ibrahim portable-computing second hop" "MISD identity" "MISD"
  Identity.wikidataQid
  (Identity.verified "Q1190992" "Wikidata identity checked 2026-09-10")

mimdQidDemand : Identity.ExternalIdentityDemand
mimdQidDemand = Identity.mkOptionalIdentityDemand
  "Ibrahim portable-computing second hop" "MIMD identity" "MIMD"
  Identity.wikidataQid
  (Identity.verified "Q1149237" "Wikidata identity checked 2026-09-10")

matrixMultiplicationQidDemand : Identity.ExternalIdentityDemand
matrixMultiplicationQidDemand = Identity.mkOptionalIdentityDemand
  "Ibrahim portable-computing second hop" "matrix multiplication identity" "matrix multiplication"
  Identity.wikidataQid
  (Identity.verified "Q1049914" "Wikidata identity checked 2026-09-10")

------------------------------------------------------------------------
-- Primary-source technical receipts.  These carry technical statements;
-- Wikidata only carries identity/navigation.
------------------------------------------------------------------------

record PrimaryTechnicalReceipt : Set where
  constructor primary-technical-receipt
  field
    sourceOwner : String
    sourceTitle : String
    canonicalURL : String
    statementRole : String
    sourceInspected : Bool
    createsIndependentBenchmark : Bool
open PrimaryTechnicalReceipt public

armNeonReceipt : PrimaryTechnicalReceipt
armNeonReceipt = primary-technical-receipt
  "Arm" "Neon" "https://www.arm.com/technologies/neon"
  "Neon is Arm's packed Advanced SIMD extension; primary source for fixed-width Arm SIMD characteristics"
  true false

armSVEReceipt : PrimaryTechnicalReceipt
armSVEReceipt = primary-technical-receipt
  "Arm" "Introduction to SVE" "https://documentation-service.arm.com/static/67ab35a4091bfc3e0a9478b5"
  "SVE is a distinct scalable SIMD extension with implementation-selectable vector length and vector-length-agnostic programming"
  true false

armSMEReceipt : PrimaryTechnicalReceipt
armSMEReceipt = primary-technical-receipt
  "Arm" "A-profile architecture learning materials" "https://www.arm.com/architecture/learn-the-architecture/a-profile"
  "SME/SME2 are Arm matrix-processing architectural extensions; adjacency to SVE does not identify them"
  true false

openMPOffloadReceipt : PrimaryTechnicalReceipt
openMPOffloadReceipt = primary-technical-receipt
  "OpenMP Architecture Review Board" "OpenMP accelerator model" "https://www.openmp.org/wp-content/uploads/Acc-model-for-OpenMP-BOF-SC12-v2.pdf"
  "host-centric target/offload model maps code and data to target devices"
  true false

googleTPUReceipt : PrimaryTechnicalReceipt
googleTPUReceipt = primary-technical-receipt
  "Google Cloud" "TPU architecture" "https://docs.cloud.google.com/tpu/docs/system-architecture-tpu-vm"
  "TPU TensorCores contain MXU, vector, and scalar units; MXUs use systolic arrays"
  true false

------------------------------------------------------------------------
-- Navigation-only graph edges.
------------------------------------------------------------------------

data SecondHopNode : Set where
  flynnNode simdNode misdNode mimdNode sisdNode armNode neonNode sveNode smeNode
  heterogeneousNode openMPNode tpuNode aiAcceleratorNode systolicNode matrixMultiplyNode : SecondHopNode

data SecondHopRelation : Set where
  partOfNavigation subclassNavigation architectureExtensionNavigation
  offloadModelNavigation hasPartNavigation acceleratesNavigation : SecondHopRelation

record SecondHopEdge : Set where
  constructor second-hop-edge
  field
    from : SecondHopNode
    relation : SecondHopRelation
    to : SecondHopNode
    navigationOnly : Bool
    createsRuntimeIdentity : Bool
open SecondHopEdge public

simdFlynnEdge : SecondHopEdge
simdFlynnEdge = second-hop-edge simdNode partOfNavigation flynnNode true false

misdFlynnEdge : SecondHopEdge
misdFlynnEdge = second-hop-edge misdNode partOfNavigation flynnNode true false

mimdFlynnEdge : SecondHopEdge
mimdFlynnEdge = second-hop-edge mimdNode partOfNavigation flynnNode true false

neonArmEdge : SecondHopEdge
neonArmEdge = second-hop-edge neonNode architectureExtensionNavigation armNode true false

sveArmEdge : SecondHopEdge
sveArmEdge = second-hop-edge sveNode architectureExtensionNavigation armNode true false

smeArmEdge : SecondHopEdge
smeArmEdge = second-hop-edge smeNode architectureExtensionNavigation armNode true false

openMPHeterogeneousEdge : SecondHopEdge
openMPHeterogeneousEdge = second-hop-edge openMPNode offloadModelNavigation heterogeneousNode true false

tpuAcceleratorEdge : SecondHopEdge
tpuAcceleratorEdge = second-hop-edge tpuNode subclassNavigation aiAcceleratorNode true false

tpuSystolicEdge : SecondHopEdge
tpuSystolicEdge = second-hop-edge tpuNode hasPartNavigation systolicNode true false

systolicMatrixEdge : SecondHopEdge
systolicMatrixEdge = second-hop-edge systolicNode acceleratesNavigation matrixMultiplyNode true false

------------------------------------------------------------------------
-- WrongType firewalls.
------------------------------------------------------------------------

data FlynnClassIdentifiesMicroarchitecture : Set where
data SIMDIdentifiesNeonOrSVE : Set where
data NeonIdentifiesSVE : Set where
data SVEVectorLengthIsFixed : Set where
data OffloadModelIdentifiesTargetISA : Set where
data TPUClassIdentifiesMXUDimensions : Set where
data SystolicArrayIsTensorCoreIdentity : Set where
data MatrixMultiplyImpliesTPUExecution : Set where

flynnDoesNotIdentifyMicroarchitecture : FlynnClassIdentifiesMicroarchitecture → ⊥
flynnDoesNotIdentifyMicroarchitecture ()

simdDoesNotIdentifyArmExtension : SIMDIdentifiesNeonOrSVE → ⊥
simdDoesNotIdentifyArmExtension ()

neonDoesNotIdentifySVE : NeonIdentifiesSVE → ⊥
neonDoesNotIdentifySVE ()

sveDoesNotCreateFixedWidth : SVEVectorLengthIsFixed → ⊥
sveDoesNotCreateFixedWidth ()

offloadDoesNotIdentifyISA : OffloadModelIdentifiesTargetISA → ⊥
offloadDoesNotIdentifyISA ()

tpuClassDoesNotFixMXUShape : TPUClassIdentifiesMXUDimensions → ⊥
tpuClassDoesNotFixMXUShape ()

systolicDoesNotBecomeTensorCore : SystolicArrayIsTensorCoreIdentity → ⊥
systolicDoesNotBecomeTensorCore ()

matrixMultiplyDoesNotCreateTPURun : MatrixMultiplyImpliesTPUExecution → ⊥
matrixMultiplyDoesNotCreateTPURun ()

record PortableComputingSecondHopBoundary : Set where
  constructor portable-computing-second-hop-boundary
  field
    firstHopReused : Bool
    verifiedSecondHopQidsRetained : Bool
    unresolvedTechnicalIdentitiesRemainExplicit : Bool
    primarySourcesOwnTechnicalClaims : Bool
    graphEdgesRemainNavigationOnly : Bool
    flynnClassDeterminesBackend : Bool
    armVectorExtensionDeterminesPerformance : Bool
    acceleratorClassDeterminesPhysicalUnit : Bool
open PortableComputingSecondHopBoundary public

canonicalPortableComputingSecondHopBoundary : PortableComputingSecondHopBoundary
canonicalPortableComputingSecondHopBoundary =
  portable-computing-second-hop-boundary true true true true true false false false
