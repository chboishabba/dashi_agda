module DASHI.Wikimedia.IbrahimSnowballPortableComputingQidsExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Wikimedia.ScientificReferenceEntityAtlasExact as Atlas
import DASHI.Wikimedia.SnowballExternalIdentityAvailabilityExact as Identity

------------------------------------------------------------------------
-- IBRAHIM SNOWBALL: PORTABLE / PARALLEL COMPUTING IDENTITIES
--
-- QIDs are navigation and external-identity coordinates only.  They do not
-- establish implementation identity, backend semantics, ISA support, runtime
-- behaviour, performance, authorship, or historical source lineage.
--
-- Identity checks retained from the 2026-09-10 snowball pass:
--   SIMD                   Q339387
--   Flynn's taxonomy       Q5654169
--   GPU                    Q97268664
--   vector processor       Q919509
--   GPGPU                  Q971505
--   parallel computing     Q232661
--   concurrent computing   Q28914705
--   ARM architecture       Q16980
--   RISC                   Q189376
--   x86                    Q182933
--   x86-64                 Q272629
--   Vulkan                 Q19407678
--   WebGPU                 Q28957081
--   OpenCL                 Q681360
--   heterogeneous computing Q17111997
--   Tensor Processing Unit Q25106376
--   AI accelerator         Q24895600
--   CUDA                   Q477690
--   ROCm                   Q110612569
--   Rust                   Q575650
--
-- No exact SWAR, CubeCL, Burn, Metal, SPIR-V, or HIP QID is promoted here
-- unless independently resolved by a later acquisition pass.
------------------------------------------------------------------------

simdEntity : Atlas.ScientificReferenceEntity
simdEntity = Atlas.verified "SIMD" Atlas.conceptEntity "Q339387"
  "Wikidata identity checked 2026-09-10"

flynnTaxonomyEntity : Atlas.ScientificReferenceEntity
flynnTaxonomyEntity = Atlas.verified "Flynn's taxonomy" Atlas.conceptEntity "Q5654169"
  "Wikidata identity checked 2026-09-10"

gpuEntity : Atlas.ScientificReferenceEntity
gpuEntity = Atlas.verified "graphics processing unit" Atlas.conceptEntity "Q97268664"
  "Wikidata identity checked 2026-09-10"

vectorProcessorEntity : Atlas.ScientificReferenceEntity
vectorProcessorEntity = Atlas.verified "vector processor" Atlas.conceptEntity "Q919509"
  "Wikidata identity checked 2026-09-10"

gpgpuEntity : Atlas.ScientificReferenceEntity
gpgpuEntity = Atlas.verified "GPGPU" Atlas.conceptEntity "Q971505"
  "Wikidata identity checked 2026-09-10"

parallelComputingEntity : Atlas.ScientificReferenceEntity
parallelComputingEntity = Atlas.verified "parallel computing" Atlas.conceptEntity "Q232661"
  "Wikidata identity checked 2026-09-10"

concurrentComputingEntity : Atlas.ScientificReferenceEntity
concurrentComputingEntity = Atlas.verified "concurrent computing" Atlas.conceptEntity "Q28914705"
  "Wikidata identity checked 2026-09-10"

armEntity : Atlas.ScientificReferenceEntity
armEntity = Atlas.verified "ARM architecture" Atlas.conceptEntity "Q16980"
  "Wikidata identity checked 2026-09-10"

riscEntity : Atlas.ScientificReferenceEntity
riscEntity = Atlas.verified "RISC" Atlas.conceptEntity "Q189376"
  "Wikidata identity checked 2026-09-10"

x86Entity : Atlas.ScientificReferenceEntity
x86Entity = Atlas.verified "x86" Atlas.conceptEntity "Q182933"
  "Wikidata identity checked 2026-09-10"

x8664Entity : Atlas.ScientificReferenceEntity
x8664Entity = Atlas.verified "x86-64" Atlas.conceptEntity "Q272629"
  "Wikidata identity checked 2026-09-10"

vulkanEntity : Atlas.ScientificReferenceEntity
vulkanEntity = Atlas.verified "Vulkan" Atlas.conceptEntity "Q19407678"
  "Wikidata identity checked 2026-09-10"

webGPUEntity : Atlas.ScientificReferenceEntity
webGPUEntity = Atlas.verified "WebGPU" Atlas.conceptEntity "Q28957081"
  "Wikidata identity checked 2026-09-10"

openCLEntity : Atlas.ScientificReferenceEntity
openCLEntity = Atlas.verified "OpenCL" Atlas.conceptEntity "Q681360"
  "Wikidata identity checked 2026-09-10"

heterogeneousComputingEntity : Atlas.ScientificReferenceEntity
heterogeneousComputingEntity = Atlas.verified "heterogeneous computing" Atlas.conceptEntity "Q17111997"
  "Wikidata identity checked 2026-09-10"

tpuEntity : Atlas.ScientificReferenceEntity
tpuEntity = Atlas.verified "Tensor Processing Unit" Atlas.conceptEntity "Q25106376"
  "Wikidata identity checked 2026-09-10"

aiAcceleratorEntity : Atlas.ScientificReferenceEntity
aiAcceleratorEntity = Atlas.verified "AI accelerator" Atlas.conceptEntity "Q24895600"
  "Wikidata identity checked 2026-09-10"

cudaEntity : Atlas.ScientificReferenceEntity
cudaEntity = Atlas.verified "CUDA" Atlas.conceptEntity "Q477690"
  "Wikidata identity checked 2026-09-10; vendor technical claims remain NVIDIA-source owned"

rocmEntity : Atlas.ScientificReferenceEntity
rocmEntity = Atlas.verified "ROCm" Atlas.projectEntity "Q110612569"
  "Wikidata identity checked 2026-09-10; vendor technical claims remain AMD-source owned"

rustEntity : Atlas.ScientificReferenceEntity
rustEntity = Atlas.verified "Rust" Atlas.conceptEntity "Q575650"
  "Wikidata identity checked 2026-09-10"

swarEntity : Atlas.ScientificReferenceEntity
swarEntity = Atlas.unresolved "SWAR" Atlas.conceptEntity
  "no exact trustworthy SWAR Wikidata item resolved in the 2026-09-10 computing snowball"

cubeCLEntity : Atlas.ScientificReferenceEntity
cubeCLEntity = Atlas.unresolved "CubeCL" Atlas.projectEntity
  "no exact CubeCL Wikidata item resolved in the 2026-09-10 computing snowball"

burnEntity : Atlas.ScientificReferenceEntity
burnEntity = Atlas.unresolved "Burn" Atlas.projectEntity
  "no exact Burn framework Wikidata item resolved in the 2026-09-10 computing snowball"

metalEntity : Atlas.ScientificReferenceEntity
metalEntity = Atlas.unresolved "Metal compute/graphics API" Atlas.conceptEntity
  "no exact Metal API Wikidata mapping safely promoted in this pass"

spirvEntity : Atlas.ScientificReferenceEntity
spirvEntity = Atlas.unresolved "SPIR-V" Atlas.conceptEntity
  "no exact SPIR-V Wikidata mapping safely promoted in this pass"

hipEntity : Atlas.ScientificReferenceEntity
hipEntity = Atlas.unresolved "HIP programming model" Atlas.conceptEntity
  "no exact HIP Wikidata mapping safely promoted in this pass"

------------------------------------------------------------------------
-- Optional identity demands preserve the Ibrahim acquisition shape.
------------------------------------------------------------------------

simdQidDemand : Identity.ExternalIdentityDemand
simdQidDemand = Identity.mkOptionalIdentityDemand
  "Ibrahim portable-computing snowball" "SIMD identity" "SIMD"
  Identity.wikidataQid
  (Identity.verified "Q339387" "Wikidata identity checked 2026-09-10")

gpuQidDemand : Identity.ExternalIdentityDemand
gpuQidDemand = Identity.mkOptionalIdentityDemand
  "Ibrahim portable-computing snowball" "GPU identity" "graphics processing unit"
  Identity.wikidataQid
  (Identity.verified "Q97268664" "Wikidata identity checked 2026-09-10")

armQidDemand : Identity.ExternalIdentityDemand
armQidDemand = Identity.mkOptionalIdentityDemand
  "Ibrahim portable-computing snowball" "ARM architecture identity" "ARM architecture"
  Identity.wikidataQid
  (Identity.verified "Q16980" "Wikidata identity checked 2026-09-10")

swarQidDemand : Identity.ExternalIdentityDemand
swarQidDemand = Identity.mkOptionalIdentityDemand
  "Ibrahim portable-computing snowball" "SWAR identity" "SWAR"
  Identity.wikidataQid
  (Identity.unresolved "no exact SWAR Wikidata item safely resolved")

------------------------------------------------------------------------
-- Graph-navigation edges observed in Wikidata.  These are external graph
-- relations, not equations or implementation theorems.
------------------------------------------------------------------------

data ComputingGraphRelation : Set where
  classifiedWithin : ComputingGraphRelation
  subclassNavigation : ComputingGraphRelation
  usesNavigation : ComputingGraphRelation
  basedOnNavigation : ComputingGraphRelation
  fieldOfWorkNavigation : ComputingGraphRelation

data ComputingNode : Set where
  simdNode flynnNode gpuNode vectorProcessorNode gpgpuNode
  parallelNode concurrentNode armNode riscNode x86Node x8664Node
  vulkanNode webGPUNode openCLNode heterogeneousNode tpuNode aiAcceleratorNode
  cudaNode rocmNode rustNode : ComputingNode

record ComputingGraphEdge : Set where
  constructor computing-graph-edge
  field
    from : ComputingNode
    relation : ComputingGraphRelation
    to : ComputingNode
    navigationOnly : Bool
    createsTechnicalEquivalence : Bool
open ComputingGraphEdge public

simdToFlynn : ComputingGraphEdge
simdToFlynn = computing-graph-edge simdNode classifiedWithin flynnNode true false

gpuToVectorProcessor : ComputingGraphEdge
gpuToVectorProcessor = computing-graph-edge gpuNode subclassNavigation vectorProcessorNode true false

gpgpuToGPU : ComputingGraphEdge
gpgpuToGPU = computing-graph-edge gpgpuNode usesNavigation gpuNode true false

armToRISC : ComputingGraphEdge
armToRISC = computing-graph-edge armNode basedOnNavigation riscNode true false

x8664ToX86 : ComputingGraphEdge
x8664ToX86 = computing-graph-edge x8664Node subclassNavigation x86Node true false

openCLToHeterogeneous : ComputingGraphEdge
openCLToHeterogeneous = computing-graph-edge openCLNode subclassNavigation heterogeneousNode true false

webGPUToGPGPU : ComputingGraphEdge
webGPUToGPGPU = computing-graph-edge webGPUNode fieldOfWorkNavigation gpgpuNode true false

tpuToAIAccelerator : ComputingGraphEdge
tpuToAIAccelerator = computing-graph-edge tpuNode subclassNavigation aiAcceleratorNode true false

cudaToGPGPU : ComputingGraphEdge
cudaToGPGPU = computing-graph-edge cudaNode classifiedWithin gpgpuNode true false

------------------------------------------------------------------------
-- WrongType firewalls.
------------------------------------------------------------------------

data QidGraphEdgeCreatesImplementationTheorem : Set where
data SIMDIsVectorProcessorIdentity : Set where
data GPGPUIdentifiesCUDAOrROCm : Set where
data ARMIsRISCIdentity : Set where
data X8664IsX86BinaryIdentity : Set where
data PortableAPIsAreSameRuntime : Set where
data TPUOrAIAcceleratorImpliesTensorCoreUse : Set where
data QidFoundImpliesCodecImplementation : Set where
data MissingSWARQidImpliesSWARAbsent : Set where

qidEdgeDoesNotCreateImplementationTheorem : QidGraphEdgeCreatesImplementationTheorem → ⊥
qidEdgeDoesNotCreateImplementationTheorem ()

simdDoesNotBecomeVectorProcessorIdentity : SIMDIsVectorProcessorIdentity → ⊥
simdDoesNotBecomeVectorProcessorIdentity ()

gpgpuDoesNotIdentifyVendorBackend : GPGPUIdentifiesCUDAOrROCm → ⊥
gpgpuDoesNotIdentifyVendorBackend ()

armDoesNotBecomeRISCIdentity : ARMIsRISCIdentity → ⊥
armDoesNotBecomeRISCIdentity ()

x8664DoesNotCreateBinaryIdentity : X8664IsX86BinaryIdentity → ⊥
x8664DoesNotCreateBinaryIdentity ()

apiAdjacencyDoesNotCreateRuntimeIdentity : PortableAPIsAreSameRuntime → ⊥
apiAdjacencyDoesNotCreateRuntimeIdentity ()

acceleratorClassDoesNotPayTensorCoreUse : TPUOrAIAcceleratorImpliesTensorCoreUse → ⊥
acceleratorClassDoesNotPayTensorCoreUse ()

qidDoesNotCreateCodecImplementation : QidFoundImpliesCodecImplementation → ⊥
qidDoesNotCreateCodecImplementation ()

unresolvedSWARDoesNotMeanAbsent : MissingSWARQidImpliesSWARAbsent → ⊥
unresolvedSWARDoesNotMeanAbsent ()

record IbrahimPortableComputingQidBoundary : Set where
  constructor ibrahim-portable-computing-qid-boundary
  field
    verifiedIdentitiesRetained : Bool
    unresolvedIdentitiesRemainExplicit : Bool
    graphRelationsNavigationOnly : Bool
    qidsCreateTechnicalAuthority : Bool
    qidsCreateImplementationIdentity : Bool
    missingQidCreatesNegativeEvidence : Bool
    currentQidVocabularyClaimedComplete : Bool
open IbrahimPortableComputingQidBoundary public

canonicalIbrahimPortableComputingQidBoundary : IbrahimPortableComputingQidBoundary
canonicalIbrahimPortableComputingQidBoundary =
  ibrahim-portable-computing-qid-boundary true true true false false false false
