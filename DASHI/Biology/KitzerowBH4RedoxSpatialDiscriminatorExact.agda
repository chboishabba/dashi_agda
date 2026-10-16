module DASHI.Biology.KitzerowBH4RedoxSpatialDiscriminatorExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.String using (String)

import DASHI.Biology.KitzerowBH4NeuralContextSourceAtlasExact as Sources
import DASHI.Biology.KitzerowBH4FluxCausalModelsExact as Flux

------------------------------------------------------------------------
-- REDOX / SPATIAL / ROUTE DISCRIMINATOR
--
-- The acquired evidence rules out a single well-mixed scalar BH4 pool as a
-- sufficient physical description.  Supply, binding/turnover, intracellular
-- versus extracellular exposure, redox regeneration and cell topology are
-- independent coordinates.  None of these local results closes the whole
-- Kitzerow causal architecture.
------------------------------------------------------------------------

data BH4PoolNodeKind : Set where
  monoaminergicSynthesisNode : BH4PoolNodeKind
  nosConsumerNode : BH4PoolNodeKind
  intracellularFreePoolNode : BH4PoolNodeKind
  nosBoundPoolNode : BH4PoolNodeKind
  extracellularPoolNode : BH4PoolNodeKind
  vascularOrSystemicPoolNode : BH4PoolNodeKind

record BH4PoolNode : Set where
  constructor bh4PoolNode
  field
    nodeKey : String
    nodeKind : BH4PoolNodeKind
    biologicalScope : String
    sourceReference : String
    measuredStatus : String

open BH4PoolNode public

monoamineSynthesisNode : BH4PoolNode
monoamineSynthesisNode =
  bh4PoolNode
    "monoamine-cell GTPCH/BH4 synthesis"
    monoaminergicSynthesisNode
    "rat TH-positive substantia nigra/VTA/hypothalamus/locus ceruleus/adrenal medulla and TPH-positive dorsal raphe/pineal contexts"
    "KitzerowBH4NeuralContextSourceAtlasExact.hwangEtAl1998Localization"
    "GTPCH localization paid; local quantitative BH4 production flux unpaid"

nNOSSpatialNode : BH4PoolNode
nNOSSpatialNode =
  bh4PoolNode
    "nNOS consumer cells lacking measured GTPCH colocalization"
    nosConsumerNode
    "rat cortex/striatum/cerebellum/olfactory bulb source context"
    "KitzerowBH4NeuralContextSourceAtlasExact.hwangEtAl1998Localization"
    "lack of GTPCH/nNOS colocalization paid; exact BH4 import route/flux unpaid"

nosBoundRedoxNode : BH4PoolNode
nosBoundRedoxNode =
  bh4PoolNode
    "NOS-bound BH4 redox pool"
    nosBoundPoolNode
    "purified/source NOS turnover system"
    "KitzerowBH4NeuralContextSourceAtlasExact.witteveenGiovanelliKaufman1999NOSRedox"
    "dynamic BH4 oxidation/regeneration paid; whole-cell NADPH flux allocation unpaid"

striatalIntracellularNode : BH4PoolNode
striatalIntracellularNode =
  bh4PoolNode
    "rat-striatal intracellular BH4"
    intracellularFreePoolNode
    "rat striatum slice superfusion after intracellular repletion via 7,8-dihydrobiopterin"
    "KitzerowBH4NeuralContextSourceAtlasExact.liangKaufman1998Striatum"
    "intracellular repletion and TH/NOS-sensitive dopamine-release component paid"

striatalExtracellularNode : BH4PoolNode
striatalExtracellularNode =
  bh4PoolNode
    "rat-striatal extracellular BH4 exposure"
    extracellularPoolNode
    "BH4 added directly to superfusion fluid"
    "KitzerowBH4NeuralContextSourceAtlasExact.liangKaufman1998Striatum"
    "large dopamine-release effect paid; effect largely independent of TH/NOS inhibition and strongly ROS-sensitive"

canonicalBH4PoolTopologyNodes : List BH4PoolNode
canonicalBH4PoolTopologyNodes =
  monoamineSynthesisNode
  ∷ nNOSSpatialNode
  ∷ nosBoundRedoxNode
  ∷ striatalIntracellularNode
  ∷ striatalExtracellularNode
  ∷ []

data BH4PoolEdgeStatus : Set where
  directlyMeasuredEdge : BH4PoolEdgeStatus
  sourceSupportedMechanisticEdge : BH4PoolEdgeStatus
  sourceProposedUnmeasuredEdge : BH4PoolEdgeStatus
  unresolvedEdge : BH4PoolEdgeStatus

record BH4PoolEdge : Set where
  constructor bh4PoolEdge
  field
    edgeKey : String
    sourceNode : String
    targetNode : String
    edgeStatus : BH4PoolEdgeStatus
    evidenceReference : String
    interpretation : String

open BH4PoolEdge public

nosReductiveRegenerationEdge : BH4PoolEdge
nosReductiveRegenerationEdge =
  bh4PoolEdge
    "reductive regeneration of NOS-bound BH4"
    "NADPH-regenerating reducing context"
    "NOS-bound BH4 redox pool"
    sourceSupportedMechanisticEdge
    "Witteveen/Giovanelli/Kaufman 1999"
    "NOS-bound BH4 redox state reflects oxidation plus reductive regeneration; this pays redox coupling but not a quantitative cell-wide NADPH allocation coefficient"

monoamineToNnosTransferHypothesis : BH4PoolEdge
monoamineToNnosTransferHypothesis =
  bh4PoolEdge
    "monoamine-cell BH4 supply to nNOS cells"
    "GTPCH-positive monoaminergic cells/processes or systemic source"
    "nNOS-positive cells lacking GTPCH colocalization"
    sourceProposedUnmeasuredEdge
    "Hwang et al. 1998 localization plus authors' proposed supply routes"
    "spatial separation is measured; direct intercellular BH4 transfer magnitude/direction is not"

intracellularBH4ToDopamineRelease : BH4PoolEdge
intracellularBH4ToDopamineRelease =
  bh4PoolEdge
    "intracellular BH4 repletion to dopamine release"
    "intracellular BH4"
    "striatal dopamine release"
    directlyMeasuredEdge
    "Liang/Kaufman 1998"
    "intracellular BH4 repletion restores much of arginine-driven dopamine release; TH and NOS inhibition each reduce components of the effect"

extracellularBH4ToDopamineRelease : BH4PoolEdge
extracellularBH4ToDopamineRelease =
  bh4PoolEdge
    "extracellular BH4 to dopamine release"
    "extracellular BH4"
    "striatal dopamine release"
    directlyMeasuredEdge
    "Liang/Kaufman 1998"
    "direct extracellular BH4 evokes a large dopamine-release response that is largely insensitive to TH/NOS inhibition and approximately 75% suppressed by superoxide dismutase plus catalase"

canonicalBH4PoolTopologyEdges : List BH4PoolEdge
canonicalBH4PoolTopologyEdges =
  nosReductiveRegenerationEdge
  ∷ monoamineToNnosTransferHypothesis
  ∷ intracellularBH4ToDopamineRelease
  ∷ extracellularBH4ToDopamineRelease
  ∷ []

record RedoxSpatialDiscriminator : Set where
  constructor redoxSpatialDiscriminator
  field
    scalarPoolReference : Flux.BH4PoolBalance
    topologyNodes : List BH4PoolNode
    topologyEdges : List BH4PoolEdge
    paidRedoxCoordinate : String
    paidSpatialCoordinate : String
    paidRouteCoordinate : String
    liveIntercellTransferResidual : String
    liveMultiBranchResidual : String
    nextExperimentReference : String

open RedoxSpatialDiscriminator public

canonicalRedoxSpatialDiscriminator : RedoxSpatialDiscriminator
canonicalRedoxSpatialDiscriminator =
  redoxSpatialDiscriminator
    Flux.canonicalBH4PoolBalance
    canonicalBH4PoolTopologyNodes
    canonicalBH4PoolTopologyEdges
    "NOS-bound BH4 is dynamically oxidized/regenerated; reductive regeneration is observed in an NADPH-regenerating context"
    "GTPCH is colocalized with monoaminergic TH/TPH cells in studied regions but not with nNOS-positive cells"
    "intracellular and extracellular BH4 manipulations produce separable dopamine-release mechanisms in rat striatum slices"
    "measure BH4 movement/supply between synthesis-positive and nNOS-positive cells rather than inferring transport from adjacency/localization"
    "resolve BH4/BH2 + NAD(P)H + branch flux by cell/region/compartment and exposure route under one perturbation"
    "extend A1 with route-resolved, compartment-resolved, multi-branch measurements and explicit redox-regeneration readouts"

record RedoxSpatialBoundary : Set where
  constructor redoxSpatialBoundary
  field
    nadphRegenerationRelevant : Bool
    nadphRegenerationRelevantIsTrue : nadphRegenerationRelevant ≡ true
    intracellularExtracellularRouteDistinctionPaid : Bool
    intracellularExtracellularRouteDistinctionPaidIsTrue :
      intracellularExtracellularRouteDistinctionPaid ≡ true
    scalarWellMixedPoolSufficient : Bool
    scalarWellMixedPoolSufficientIsFalse : scalarWellMixedPoolSufficient ≡ false
    gtpchAndNnosMustBeSameCell : Bool
    gtpchAndNnosMustBeSameCellIsFalse : gtpchAndNnosMustBeSameCell ≡ false
    intercellBH4TransferDirectlyMeasured : Bool
    intercellBH4TransferDirectlyMeasuredIsFalse : intercellBH4TransferDirectlyMeasured ≡ false
    exogenousBH4EffectRequiresTHOrNOS : Bool
    exogenousBH4EffectRequiresTHOrNOSIsFalse : exogenousBH4EffectRequiresTHOrNOS ≡ false
    intracellularBH4CanEngageTHAndNOS : Bool
    intracellularBH4CanEngageTHAndNOSIsTrue : intracellularBH4CanEngageTHAndNOS ≡ true
    redoxSpatialEvidenceClosesWholeAllocator : Bool
    redoxSpatialEvidenceClosesWholeAllocatorIsFalse : redoxSpatialEvidenceClosesWholeAllocator ≡ false

open RedoxSpatialBoundary public

canonicalRedoxSpatialBoundary : RedoxSpatialBoundary
canonicalRedoxSpatialBoundary =
  redoxSpatialBoundary
    true refl
    true refl
    false refl
    false refl
    false refl
    false refl
    true refl
    false refl
