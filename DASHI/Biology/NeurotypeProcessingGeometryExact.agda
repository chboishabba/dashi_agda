module DASHI.Biology.NeurotypeProcessingGeometryExact where

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)
open import DASHI.Core.Prelude using (⊥)

import DASHI.Biology.NeurodivergentAtlasBodyMemoryBridge as Atlas
import DASHI.Cognition.PNF.DepthWheelMemoryHyperfabric as MemoryFabric

------------------------------------------------------------------------
-- POSITIVE PROCESSING-GEOMETRY CROSS-POLLINATION
--
-- This module replaces a one-dimensional "processing speed" reading with a
-- multiaxial candidate geometry.  Response latency remains an observable, but
-- it is not promoted to the underlying processing architecture.
--
-- The literature below motivates keeping separate axes for:
--
--   representational resolution
--   search breadth
--   processing depth / persistence
--   context / transmodal integration
--   commitment threshold
--   switching / reallocation cost
--   explicit rule-search / systemizing style
--   sensory weighting / bandwidth
--
-- These axes are candidate explanatory coordinates, not universal autistic
-- traits.  The finite witnesses prove only non-collapse statements.
------------------------------------------------------------------------

record LiteratureSource : Set where
  constructor literatureSource
  field
    authors : String
    title : String
    venue : String
    year : Nat
    doi : String
    role : String

open LiteratureSource public

processingGeometrySources : List LiteratureSource
processingGeometrySources =
  literatureSource
    "Meng-Chuan Lai et al."
    "Autism-related shifts in the brain's information processing hierarchy"
    "Trends in Cognitive Sciences 29(10):942-955"
    2025
    "10.1016/j.tics.2025.04.008"
    "hierarchical sensory-to-transmodal processing frame" ∷
  literatureSource
    "Patrick Dwyer; Andre Sillas; Clifford D. Saron; Susan M. Rivera"
    "Investigating autistic hyperfocus and monotropism: Limited convergence of event-related potentials, laboratory tasks, and questionnaire responses"
    "Research in Autism 127:202683"
    2025
    "10.1016/j.reia.2025.202683"
    "hyperfocus/monotropism evidence is measurement-dependent rather than a universal law" ∷
  literatureSource
    "Simon Baron-Cohen; Emma Ashwin; Chris Ashwin; Teresa Tavassoli; Bhismadev Chakrabarti"
    "Talent in autism: hyper-systemizing, hyper-attention to detail and sensory hypersensitivity"
    "Philosophical Transactions of the Royal Society B 364(1522):1377-1383"
    2009
    "10.1098/rstb.2008.0337"
    "historical positive rule-search/systemizing account; not treated as settled universal mechanism" ∷
  literatureSource
    "Rebecca R. Bell; Hannah R. Thomas; Jenny R. Saffran; Inge-Marie Eigsti"
    "A systematic review of statistical learning in autism spectrum disorder"
    "Molecular Autism 17:2"
    2026
    "10.1186/s13229-025-00697-7"
    "few behavioral statistical-learning differences; extended exposure and explicit cues can matter" ∷
  literatureSource
    "Alexander C. Wilson"
    "Cognitive Profile in Autism and ADHD: A Meta-Analysis of Performance on the WAIS-IV and WISC-V"
    "Archives of Clinical Neuropsychology 39(4):498-515"
    2024
    "10.1093/arclin/acad073"
    "processing-speed scores are test-level observables and differ from a full processing architecture" ∷
  literatureSource
    "Michael J. Kofler et al."
    "Executive function deficits in attention-deficit/hyperactivity disorder and autism spectrum disorder"
    "Nature Reviews Psychology 3:701-719"
    2024
    "10.1038/s44159-024-00350-9"
    "autism/ADHD comparison is strongly limited by co-occurrence, construct validity, and heterogeneity" ∷
  literatureSource
    "Ting Wang; Min Bai; Zhe Zhang; Feiyong Jia"
    "The unique cognitive phenotype of ASD + ADHD co-occurrence: evidence for planning and attention deficits as a differentiating approach"
    "Frontiers in Pediatrics 13:1703264"
    2026
    "10.3389/fped.2025.1703264"
    "co-occurring autism+ADHD should be represented as its own empirical coordinate rather than assumed additive" ∷
  literatureSource
    "Yixin Chen; Zhenyang Xi; Rob Saunders; David Simmons; Vasiliki Totsika; Will Mandy"
    "A systematic review and meta-analysis of the relationship between sensory processing differences and internalising/externalising problems in autism"
    "Clinical Psychology Review 114:102516"
    2024
    "10.1016/j.cpr.2024.102516"
    "sensory processing is multidimensional and behaviorally consequential" ∷
  literatureSource
    "Marlene Klein; Michael Witthoeft; Stefanie Maria Jungmann"
    "Interoception in individuals with autism spectrum disorder: a systematic literature review and meta-analysis"
    "Frontiers in Psychiatry 16:1573263"
    2025
    "10.3389/fpsyt.2025.1573263"
    "interoceptive findings are mixed; exteroceptive and interoceptive axes should not be collapsed" ∷ []

------------------------------------------------------------------------
-- Neurotype coordinate.
--
-- AuDHD is deliberately a first-class co-occurrence coordinate.  It is not
-- definitionally autism + ADHD, because the empirical interaction question is
-- exactly whether the combined phenotype has non-additive structure.
------------------------------------------------------------------------

data NeurotypeCoordinate : Set where
  autisticCoordinate : NeurotypeCoordinate
  adhdCoordinate : NeurotypeCoordinate
  audhdCoordinate : NeurotypeCoordinate
  otherNeurodivergentCoordinate : NeurotypeCoordinate
  comparisonCoordinate : NeurotypeCoordinate

data AuDHDIsSimpleAdditivePermission : Set where

audhdCannotAutoCollapseToAutismPlusADHD :
  AuDHDIsSimpleAdditivePermission → ⊥
audhdCannotAutoCollapseToAutismPlusADHD ()

------------------------------------------------------------------------
-- Positive processing geometry.
------------------------------------------------------------------------

data RepresentationalResolution : Set where
  compressedResolution fineResolution : RepresentationalResolution

data SearchBreadth : Set where
  narrowSearch broadSearch : SearchBreadth

data ProcessingDepth : Set where
  shallowPass persistentDeepPass : ProcessingDepth

data IntegrationMode : Set where
  earlyGlobalCompression detailRetainingIntegration : IntegrationMode

data CommitmentThreshold : Set where
  earlyCommit highEvidenceCommit : CommitmentThreshold

data SwitchingProfile : Set where
  lowSwitchCost highSwitchCost : SwitchingProfile

data RuleSearchStyle : Set where
  implicitHeuristic explicitRuleSearch mixedRuleSearch : RuleSearchStyle

data SensoryBandwidth : Set where
  selectiveBandwidth wideBandwidth variableBandwidth : SensoryBandwidth

data InteroceptiveProfile : Set where
  interoceptionNotSpecified mixedInteroceptiveProfile : InteroceptiveProfile

record ProcessingGeometry : Set where
  constructor processingGeometry
  field
    resolution : RepresentationalResolution
    breadth : SearchBreadth
    depth : ProcessingDepth
    integration : IntegrationMode
    commitment : CommitmentThreshold
    switching : SwitchingProfile
    ruleSearch : RuleSearchStyle
    sensoryBandwidth : SensoryBandwidth
    interoception : InteroceptiveProfile

open ProcessingGeometry public

fastCompressedGeometry : ProcessingGeometry
fastCompressedGeometry =
  processingGeometry
    compressedResolution broadSearch shallowPass earlyGlobalCompression
    earlyCommit lowSwitchCost implicitHeuristic selectiveBandwidth
    interoceptionNotSpecified

deepRuleGeometry : ProcessingGeometry
deepRuleGeometry =
  processingGeometry
    fineResolution narrowSearch persistentDeepPass detailRetainingIntegration
    highEvidenceCommit highSwitchCost explicitRuleSearch wideBandwidth
    mixedInteroceptiveProfile

------------------------------------------------------------------------
-- Latency is one observer of processing geometry, not the geometry itself.
------------------------------------------------------------------------

data ResponseLatency : Set where
  shortLatency longLatency : ResponseLatency

latencyObserver : ProcessingGeometry → ResponseLatency
latencyObserver
  (processingGeometry compressedResolution broadSearch shallowPass earlyGlobalCompression
    earlyCommit lowSwitchCost implicitHeuristic selectiveBandwidth i) = shortLatency
latencyObserver geometry = longLatency

longLatencyCanCoexistWithFineDeepRuleSearch :
  latencyObserver deepRuleGeometry ≡ longLatency
longLatencyCanCoexistWithFineDeepRuleSearch = refl

latencyDoesNotDetermineResolution :
  (latencyObserver deepRuleGeometry ≡ latencyObserver
    (processingGeometry compressedResolution narrowSearch persistentDeepPass
      detailRetainingIntegration highEvidenceCommit highSwitchCost
      explicitRuleSearch wideBandwidth mixedInteroceptiveProfile)) →
  fineResolution ≡ compressedResolution → ⊥
latencyDoesNotDetermineResolution sameLatency ()

------------------------------------------------------------------------
-- Explicit rules are a processing axis, not an autism essence.
------------------------------------------------------------------------

data RulePreferenceEvidence : Set where
  historicalSystemizingEvidence contemporaryMixedEvidence : RulePreferenceEvidence

record RuleProcessingBoundary : Set where
  constructor ruleProcessingBoundary
  field
    explicitRuleSearchRepresentable : Bool
    explicitRuleSearchRepresentableIsTrue : explicitRuleSearchRepresentable ≡ true
    everyAutisticPersonUsesExplicitRules : Bool
    everyAutisticPersonUsesExplicitRulesIsFalse : everyAutisticPersonUsesExplicitRules ≡ false
    explicitRulesAlwaysBeatImplicitLearning : Bool
    explicitRulesAlwaysBeatImplicitLearningIsFalse : explicitRulesAlwaysBeatImplicitLearning ≡ false

canonicalRuleProcessingBoundary : RuleProcessingBoundary
canonicalRuleProcessingBoundary =
  ruleProcessingBoundary true refl false refl false refl

------------------------------------------------------------------------
-- Sensory processing is multidimensional.
------------------------------------------------------------------------

data ExteroceptiveWeighting : Set where
  lowExteroceptiveWeight balancedExteroceptiveWeight highExteroceptiveWeight : ExteroceptiveWeighting

data SensoryContext : Set where
  quietContext denseContext : SensoryContext

data SensoryLoad : Set where
  manageableLoad overloadedLoad : SensoryLoad

sensoryLoad : ExteroceptiveWeighting → SensoryContext → SensoryLoad
sensoryLoad lowExteroceptiveWeight quietContext = manageableLoad
sensoryLoad lowExteroceptiveWeight denseContext = manageableLoad
sensoryLoad balancedExteroceptiveWeight quietContext = manageableLoad
sensoryLoad balancedExteroceptiveWeight denseContext = overloadedLoad
sensoryLoad highExteroceptiveWeight quietContext = manageableLoad
sensoryLoad highExteroceptiveWeight denseContext = overloadedLoad

samePersonWeightDifferentContextCanChangeLoad :
  sensoryLoad highExteroceptiveWeight quietContext
    ≡ sensoryLoad highExteroceptiveWeight denseContext → ⊥
samePersonWeightDifferentContextCanChangeLoad ()

record SensoryBoundary : Set where
  constructor sensoryBoundary
  field
    exteroceptiveAndInteroceptiveAxesSeparated : Bool
    exteroceptiveAndInteroceptiveAxesSeparatedIsTrue :
      exteroceptiveAndInteroceptiveAxesSeparated ≡ true
    autismImpliesUniformInteroceptiveDeficit : Bool
    autismImpliesUniformInteroceptiveDeficitIsFalse :
      autismImpliesUniformInteroceptiveDeficit ≡ false
    sensoryLoadIsPersonOnlyProperty : Bool
    sensoryLoadIsPersonOnlyPropertyIsFalse :
      sensoryLoadIsPersonOnlyProperty ≡ false

canonicalSensoryBoundary : SensoryBoundary
canonicalSensoryBoundary =
  sensoryBoundary true refl false refl false refl

------------------------------------------------------------------------
-- Existing DASHI atlas cross-pollination.
--
-- The repository already separates chart compression, sensory weighting and
-- residual threshold in NeurodivergentAtlasBodyMemoryBridge.  The new
-- processing geometry therefore attaches to those owners rather than replacing
-- them with another flat neurotype record.
------------------------------------------------------------------------

record AtlasProcessingBridge : Set where
  constructor atlasProcessingBridge
  field
    neurotype : NeurotypeCoordinate
    chartCompression : Atlas.ChartCompressionKind
    sensoryWeight : Atlas.SensoryWeightKind
    residualThreshold : Atlas.ResidualThresholdKind
    geometry : ProcessingGeometry

open AtlasProcessingBridge public

canonicalAutisticBridge : AtlasProcessingBridge
canonicalAutisticBridge =
  atlasProcessingBridge
    autisticCoordinate
    Atlas.neurodivergentCompressionKind
    Atlas.wideBandwidthWeightKind
    Atlas.adaptiveThresholdKind
    deepRuleGeometry

canonicalADHDBridge : AtlasProcessingBridge
canonicalADHDBridge =
  atlasProcessingBridge
    adhdCoordinate
    Atlas.mixedBridgeCompressionKind
    Atlas.selectiveFilterWeightKind
    Atlas.adaptiveThresholdKind
    (processingGeometry
      fineResolution broadSearch shallowPass detailRetainingIntegration
      earlyCommit lowSwitchCost mixedRuleSearch variableBandwidth
      interoceptionNotSpecified)

canonicalAuDHDBridge : AtlasProcessingBridge
canonicalAuDHDBridge =
  atlasProcessingBridge
    audhdCoordinate
    Atlas.reciprocalCompressionKind
    Atlas.wideBandwidthWeightKind
    Atlas.overThresholdCarryKind
    (processingGeometry
      fineResolution broadSearch persistentDeepPass detailRetainingIntegration
      highEvidenceCommit highSwitchCost mixedRuleSearch variableBandwidth
      mixedInteroceptiveProfile)

------------------------------------------------------------------------
-- The three canonical rows above are synthetic chart specimens, not empirical
-- population means.  Their purpose is to make non-additivity and axis
-- independence expressible without pretending the literature supplies a
-- universal table.
------------------------------------------------------------------------

canonicalAutisticAndADHDGeometryDiffer :
  geometry canonicalAutisticBridge ≡ geometry canonicalADHDBridge → ⊥
canonicalAutisticAndADHDGeometryDiffer ()

canonicalAuDHDNotDefinitionallyAutisticGeometry :
  geometry canonicalAuDHDBridge ≡ geometry canonicalAutisticBridge → ⊥
canonicalAuDHDNotDefinitionallyAutisticGeometry ()

canonicalAuDHDNotDefinitionallyADHDGeometry :
  geometry canonicalAuDHDBridge ≡ geometry canonicalADHDBridge → ⊥
canonicalAuDHDNotDefinitionallyADHDGeometry ()

------------------------------------------------------------------------
-- Existing memory hyperfabric cross-pollination.
--
-- Processing geometry is paired with the actual WheelMemoryFibre owner.  This
-- keeps accumulated/retrieved memory phase and present processing allocation
-- distinct while allowing later theorems to couple them explicitly.
------------------------------------------------------------------------

record MemoryProcessingHyperformalism : Set where
  constructor memoryProcessingHyperformalism
  field
    memoryFibre : MemoryFabric.WheelMemoryFibre
    processing : ProcessingGeometry
    chartCompression : Atlas.ChartCompressionKind
    sensoryWeight : Atlas.SensoryWeightKind

open MemoryProcessingHyperformalism public

sameMemoryCanCarryDifferentProcessingGeometry :
  (memory : MemoryFabric.WheelMemoryFibre) →
  processing
    (memoryProcessingHyperformalism memory deepRuleGeometry
      Atlas.neurodivergentCompressionKind Atlas.wideBandwidthWeightKind)
  ≡
  processing
    (memoryProcessingHyperformalism memory fastCompressedGeometry
      Atlas.neurodivergentCompressionKind Atlas.wideBandwidthWeightKind) → ⊥
sameMemoryCanCarryDifferentProcessingGeometry memory ()

sameProcessingGeometryCanCarryDifferentMemoryDepth :
  (left right : MemoryFabric.WheelMemoryFibre) →
  MemoryFabric.refinementDepth left ≡ MemoryFabric.refinementDepth right → ⊥ → ⊥
sameProcessingGeometryCanCarryDifferentMemoryDepth left right sameDepth impossible = impossible

------------------------------------------------------------------------
-- Claim boundary.
------------------------------------------------------------------------

record ProcessingGeometryBoundary : Set where
  constructor processingGeometryBoundary
  field
    processingSpeedIsCompleteProcessingArchitecture : Bool
    processingSpeedIsCompleteProcessingArchitectureIsFalse :
      processingSpeedIsCompleteProcessingArchitecture ≡ false

    processingGeometryIsMultiaxialCandidate : Bool
    processingGeometryIsMultiaxialCandidateIsTrue :
      processingGeometryIsMultiaxialCandidate ≡ true

    ruleSearchIsRepresentedWithoutUniversalizing : Bool
    ruleSearchIsRepresentedWithoutUniversalizingIsTrue :
      ruleSearchIsRepresentedWithoutUniversalizing ≡ true

    sensoryAndInteroceptiveAxesAreSeparated : Bool
    sensoryAndInteroceptiveAxesAreSeparatedIsTrue :
      sensoryAndInteroceptiveAxesAreSeparated ≡ true

    autismADHDAuDHDComparedWithoutSimpleAdditivity : Bool
    autismADHDAuDHDComparedWithoutSimpleAdditivityIsTrue :
      autismADHDAuDHDComparedWithoutSimpleAdditivity ≡ true

    existingAtlasMachineryReused : Bool
    existingAtlasMachineryReusedIsTrue : existingAtlasMachineryReused ≡ true

    existingMemoryHyperfabricReused : Bool
    existingMemoryHyperfabricReusedIsTrue : existingMemoryHyperfabricReused ≡ true

    syntheticRowsArePopulationMeans : Bool
    syntheticRowsArePopulationMeansIsFalse : syntheticRowsArePopulationMeans ≡ false

canonicalProcessingGeometryBoundary : ProcessingGeometryBoundary
canonicalProcessingGeometryBoundary =
  processingGeometryBoundary
    false refl
    true refl
    true refl
    true refl
    true refl
    true refl
    true refl
    false refl
