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
-- sufficient physical description. Supply, binding/turnover, cellular uptake,
-- intracellular versus extracellular exposure, redox regeneration and cell
-- topology are independent coordinates. None of these local results closes the
-- whole Kitzerow causal architecture.
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
    "lack of GTPCH/nNOS colocalization paid; exact donor-to-recipient BH4 flux unpaid"

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

cellularUptakeNode : BH4PoolNode
cellularUptakeNode =
  bh4PoolNode
    "exogenous BH4 cellular uptake"
    intracellularFreePoolNode
    "rat brain synaptosomes, PC12 cells and rat striatum after peripheral administration"
    "KitzerowBH4NeuralContextSourceAtlasExact.anastasiadisKuhnLevine1994Uptake"
    "linear concentration-dependent uptake paid; studied uptake did not require sodium/glucose and was interpreted as passive diffusion rather than a specific carrier"

humanNnosRecipientNode : BH4PoolNode
humanNnosRecipientNode =
  bh4PoolNode
    "human nNOS neuroblastoma recipient pool"
    nosConsumerNode
    "TGW-I-nu nNOS-expressing human neuroblastoma cells"
    "KitzerowBH4NeuralContextSourceAtlasExact.choiEtAl2003HumanNnosUptake"
    "dose-dependent exogenous BH4 uptake with increased NO production paid; physiological in-vivo transfer magnitude unpaid"

canonicalBH4PoolTopologyNodes : List BH4PoolNode
canonicalBH4PoolTopologyNodes =
  monoamineSynthesisNode
  ∷ nNOSSpatialNode
  ∷ nosBoundRedoxNode
  ∷ striatalIntracellularNode
  ∷ striatalExtracellularNode
  ∷ cellularUptakeNode
  ∷ humanNnosRecipientNode
  ∷ []

data BH4PoolEdgeStatus : Set where
  directlyMeasuredEdge : BH4PoolEdgeStatus
  sourceSupportedMechanisticEdge : BH4PoolEdgeStatus
  functionalCrossTalkEdge : BH4PoolEdgeStatus
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

exogenousBH4UptakeEdge : BH4PoolEdge
exogenousBH4UptakeEdge =
  bh4PoolEdge
    "extracellular BH4 uptake into neural/catecholaminergic preparations"
    "extracellular BH4"
    "synaptosome/PC12 intracellular BH4 pool"
    directlyMeasuredEdge
    "Anastasiadis/Kuhn/Levine 1994"
    "linear concentration-dependent cellular accumulation is directly measured; the studied uptake was interpreted as passive diffusion rather than a dedicated membrane carrier"

catecholaminergicToNnosFunctionalCrossTalk : BH4PoolEdge
catecholaminergicToNnosFunctionalCrossTalk =
  bh4PoolEdge
    "catecholaminergic donor to nNOS-recipient functional BH4 crosstalk"
    "CATH.a catecholaminergic coculture"
    "TGW-I-nu human nNOS neuroblastoma NO output"
    functionalCrossTalkEdge
    "Choi et al. 2003"
    "coculture increases NO production in recipient nNOS cells and exogenous BH4 is taken up dose-dependently; supports functional extracellular/intercellular supply but does not directly quantify donor-derived BH4 molecular flux"

monoamineToNnosTransferHypothesis : BH4PoolEdge
monoamineToNnosTransferHypothesis =
  bh4PoolEdge
    "monoamine-cell BH4 supply to nNOS cells"
    "GTPCH-positive monoaminergic cells/processes or systemic source"
    "nNOS-positive cells lacking GTPCH colocalization"
    sourceSupportedMechanisticEdge
    "Hwang 1998 localization + Anastasiadis 1994 uptake + Choi 2003 uptake/coculture"
    "spatial separation, cellular uptake and functional coculture crosstalk are paid; direct quantitative donor-to-recipient BH4 flux in vivo remains unpaid"

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
  ∷ exogenousBH4UptakeEdge
  ∷ catecholaminergicToNnosFunctionalCrossTalk
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
    paidUptakeCrossTalkCoordinate : String
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
    "exogenous BH4 uptake is directly measured in neural/catecholaminergic preparations, and human nNOS-recipient cells show BH4 uptake/NO response plus functional catecholaminergic coculture crosstalk"
    "quantify donor-to-recipient BH4 molecular transfer, direction and rate in target-relevant intact neural systems rather than inferring physiological flux from uptake/coculture function"
    "resolve BH4/BH2 + NAD(P)H + branch flux by cell/region/compartment, exposure route and transfer topology under one perturbation"
    "extend A1 with route-resolved, transfer-resolved, compartment-resolved multi-branch measurements and explicit redox-regeneration readouts"

record RedoxSpatialBoundary : Set where
  constructor redoxSpatialBoundary
  field
    nadphRegenerationRelevant : Bool
    nadphRegenerationRelevantIsTrue : nadphRegenerationRelevant ≡ true
    intracellularExtracellularRouteDistinctionPaid : Bool
    intracellularExtracellularRouteDistinctionPaidIsTrue :
      intracellularExtracellularRouteDistinctionPaid ≡ true
    cellularBH4UptakeDirectlyMeasured : Bool
    cellularBH4UptakeDirectlyMeasuredIsTrue : cellularBH4UptakeDirectlyMeasured ≡ true
    specificMembraneCarrierRequiredByUptakeStudy : Bool
    specificMembraneCarrierRequiredByUptakeStudyIsFalse :
      specificMembraneCarrierRequiredByUptakeStudy ≡ false
    functionalCocultureCrossTalkSupported : Bool
    functionalCocultureCrossTalkSupportedIsTrue : functionalCocultureCrossTalkSupported ≡ true
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
    true refl
    false refl
    true refl
    false refl
    false refl
    false refl
    false refl
    true refl
    false refl

------------------------------------------------------------------------
-- TOPOLOGY-RESOLVED POOL BALANCE
--
-- The scalar balance remains a useful coarse projection, but the paid evidence
-- above requires a state space that retains node identity, transport route and
-- redox/consumer coupling. Numerical edge fluxes remain explicit acquisition
-- debt rather than being inferred from localization, uptake or coculture data.
------------------------------------------------------------------------

record TopologyResolvedPoolBalance : Set where
  constructor topologyResolvedPoolBalance
  field
    scalarProjection : Flux.BH4PoolBalance
    stateNodes : List BH4PoolNode
    transportAndCouplingEdges : List BH4PoolEdge
    localBalanceReference : String
    projectionReference : String
    topologyResolvedStateRequired : Bool
    topologyResolvedStateRequiredIsTrue : topologyResolvedStateRequired ≡ true
    scalarProjectionIsLossy : Bool
    scalarProjectionIsLossyIsTrue : scalarProjectionIsLossy ≡ true
    numericEdgeFluxesPaid : Bool
    numericEdgeFluxesPaidIsFalse : numericEdgeFluxesPaid ≡ false
    directTransferFluxPaid : Bool
    directTransferFluxPaidIsFalse : directTransferFluxPaid ≡ false

open TopologyResolvedPoolBalance public

canonicalTopologyResolvedPoolBalance : TopologyResolvedPoolBalance
canonicalTopologyResolvedPoolBalance =
  topologyResolvedPoolBalance
    Flux.canonicalBH4PoolBalance
    canonicalBH4PoolTopologyNodes
    canonicalBH4PoolTopologyEdges
    "for each node v: d[BH4_v]/dt = local synthesis_v + local recycle_v + sum incoming transfer/redox terms - local consumer sinks_v - sum outgoing transfer/loss terms"
    "summing node-local balances yields the legacy scalar pool equation only after forgetting route, compartment, cell/region identity, bound/free state and transfer topology"
    true refl
    true refl
    false refl
    false refl
