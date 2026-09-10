module DASHI.Interop.CrossLaneProofArchaeologyLedgerExact where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.String using (String)
open import Agda.Builtin.List using (List; []; _∷_)

------------------------------------------------------------------------
-- CROSS-LANE PROOF ARCHAEOLOGY LEDGER
--
-- Purpose:
--   keep one compact, inspectable owner for the historical route families,
--   dated pivots, buried-donor windows, present consumers and live theorem
--   obligations across Navier--Stokes, Yang--Mills, RH and GR/QFT unification.
--
-- IMPORTANT DATE RULE:
--   a date in this file is an evidenced repository lower bound, not an origin
--   claim.  In particular, the July 2026 tranche is a later formal/source-
--   faithful consolidation wave.  The constructions and route families have
--   earlier ancestry, including May dashi_agda and sibling-repo work.
--
-- This file is a navigation/proof-search object.  It does not promote a route,
-- date, source receipt, compiler, diagnostic, finite model or status flag into
-- theorem content.  Existing mathematical owners remain authoritative.
------------------------------------------------------------------------

data Lane : Set where
  navierStokes yangMills riemannHypothesis grQuantum : Lane

data HistoricalRole : Set where
  terminalConsumer
  directProducer
  producerTactic
  compiler
  representationWeld
  negativeControl
  diagnostic
  supersededOverpayment
  sourceTranscriptionDebt
  liveLevel2Theorem : HistoricalRole

data EvidenceKind : Set where
  exactCommitDate
  pullRequestDate
  repositorySequence
  historicalInference : EvidenceKind

-- Keep distinct clocks.  A later formalization date must never overwrite an
-- earlier construction or experimental ancestor.
data HistoricalClock : Set where
  constructionAncestry
  firstTypedAppearance
  formalConsolidation
  canonicalConsumerRecovery : HistoricalClock

data HistoricalIdentityStatus : Set where
  sameObjectProved
  structuralAncestorOnly
  candidateAlias
  notSameObject : HistoricalIdentityStatus

record ClockedArchaeologyAnchor : Set where
  constructor clocked-anchor
  field
    anchorLane : Lane
    anchorDateBrisbane : String
    anchorClock : HistoricalClock
    anchorEvidence : EvidenceKind
    anchorRepositoryReference : String
    anchorObject : String
    anchorRole : HistoricalRole
    anchorIdentityStatus : HistoricalIdentityStatus
    anchorInterpretation : String

open ClockedArchaeologyAnchor public

------------------------------------------------------------------------
-- PRE-JULY ANCHORS.
--
-- These correct the first pass: July is not the beginning.  The earliest
-- confirmed dates below are lower bounds only.  Earlier parent repositories,
-- local work, unindexed branches or differently named constructions may move
-- them further back as archaeology continues.
------------------------------------------------------------------------

preJulyArchaeologyAnchors : List ClockedArchaeologyAnchor
preJulyArchaeologyAnchors =

  clocked-anchor riemannHypothesis "2026-05-19" constructionAncestry
    exactCommitDate
    "dashi_agda commit 9955429d8dbe1aae4bbf3778808993cfdc6172c9 / post-checkpoint-2026-05-01"
    "DASHI.Analysis.ZetaVisualization: Abel-zeta samples, phase/zero-spacing feature views, explicit no-RH boundary"
    diagnostic structuralAncestorOnly
    "RH/zeta exploration is already present in the first visible dashi_agda history. It is deliberately non-theorem-bearing and is ancestry for later phase-visible work, not the same object as the pole-quotient high producer."
  ∷

  clocked-anchor yangMills "2026-05-29" firstTypedAppearance
    exactCommitDate
    "dashi_agda commit bdd0801cc7e544304c52412ea1ccd0164904d12f / pre-submission freeze"
    "DASHI.Physics.Closure.YangMillsMassGapBoundary"
    terminalConsumer structuralAncestorOnly
    "Typed YM mass-gap boundary already records finite-volume coercivity, reflection positivity, transfer positivity, spectral isolation, continuum/infinite-volume stability and physical-spectrum transport as open obligations. July source-faithful Balaban work is a later refinement, not the origin of the mass-gap programme."
  ∷

  clocked-anchor navierStokes "2026-05-29" firstTypedAppearance
    exactCommitDate
    "dashi_agda commit bdd0801cc7e544304c52412ea1ccd0164904d12f / pre-submission freeze"
    "DASHI.Physics.Closure.NavierStokesRegularityTowerReceipt"
    terminalConsumer structuralAncestorOnly
    "Typed NS regularity tower already separates finite-depth enstrophy/vorticity structure from missing uniform continuum persistence, BKM/Serrin discharge and nonlinear continuum control. Later signed-transfer routes must be read as attempts to pay this older continuum wall."
  ∷

  clocked-anchor grQuantum "2026-05-29" firstTypedAppearance
    exactCommitDate
    "dashi_agda commit bdd0801cc7e544304c52412ea1ccd0164904d12f / pre-submission freeze"
    "DASHI.Physics.Closure.GRQFTTerminalCompositionBoundary"
    terminalConsumer structuralAncestorOnly
    "GR/QFT terminal composition already names discrete-to-smooth passage, AQFT construction, stress-energy bridge and terminal receipt composition while keeping the terminal claim non-promoted. The July deep-QG cutset and August same-action weld are later normalizations of an older unification programme."
  ∷

  clocked-anchor navierStokes "2026-06-04" constructionAncestry
    exactCommitDate
    "chboishabba/dashiCFD commit 1c9ca183515e3a26988ae21785de9a45481e37d2; earlier visible parent 125e52e04bed4042890d95db5d5371104ba1aafe on 2026-06-04 Brisbane"
    "3D periodic incompressible truth lane + shell enstrophy / flux-to-dissipation theta diagnostics"
    diagnostic structuralAncestorOnly
    "dashiCFD was already testing the physical NS carrier, Leray projection, vorticity shells, enstrophy and theta(k,t)=|Flux_tail|/Diss_tail before the July/round formal wave. This is empirical construction ancestry, not by itself the later signed analytic theorem."
  ∷ []

------------------------------------------------------------------------
-- SIBLING-REPOSITORY LOWER BOUNDS.
------------------------------------------------------------------------

record RepositoryAncestryLowerBound : Set where
  constructor repository-lower-bound
  field
    repository : String
    earliestConfirmedDateBrisbane : String
    evidenceReference : String
    relevance : String
    originClaim : Bool

open RepositoryAncestryLowerBound public

repositoryAncestryLowerBounds : List RepositoryAncestryLowerBound
repositoryAncestryLowerBounds =
  repository-lower-bound
    "chboishabba/dashiCORE"
    "2026-03-05"
    "commit 684b899b3b05b4fbbf6799fe368c5da6551f0c13 and descendants"
    "Cross-programme implementation ancestry predates dashi_agda; lane-specific same-object bridges still require proof before promotion."
    false
  ∷ repository-lower-bound
    "chboishabba/dashiCFD"
    "2026-06-04"
    "commit 125e52e04bed4042890d95db5d5371104ba1aafe and descendants"
    "NS physical/empirical construction ancestry with 3D incompressible truth, vorticity/shell diagnostics and flux/dissipation experiments."
    false
  ∷ []

------------------------------------------------------------------------
-- SAME-OBJECT FIREWALL FOR HISTORICAL ALIASES.
------------------------------------------------------------------------

record HistoricalAliasBridge : Set where
  constructor historical-alias
  field
    aliasLane : Lane
    oldReference : String
    laterCanonicalReference : String
    outputShapeRelation : String
    identityStatus : HistoricalIdentityStatus

open HistoricalAliasBridge public

canonicalHistoricalAliasBridges : List HistoricalAliasBridge
canonicalHistoricalAliasBridges =
  historical-alias navierStokes
    "dashiCFD shell flux / theta / signed-transfer diagnostics"
    "dashi_agda signed physical transfer -> uniform critical-cone payment"
    "same physical theme and candidate output comparison, but empirical absolute-flux theta is not definitionally the later signed theorem"
    candidateAlias
  ∷ historical-alias riemannHypothesis
    "May Abel-zeta phase/zero-spacing visualization"
    "September universal pole-quotient literal response"
    "early phase-visible zeta exploration is conceptual ancestry only; carrier and theorem are different"
    notSameObject
  ∷ historical-alias yangMills
    "May finite-depth/RG mass-gap receipt and Stone-spectrum target"
    "September same-family quantitative continuum clustering consumer"
    "old target is downstream-compatible ancestry; it does not itself inhabit the later quantitative clustering theorem"
    structuralAncestorOnly
  ∷ historical-alias grQuantum
    "May GRQFT terminal stress-energy/composition target"
    "August endpoint-only common action/metric/stress weld"
    "later work sharpens the old stress-energy target to one same-object variational consumer"
    structuralAncestorOnly
  ∷ []

record DatedArchaeologyEntry : Set where
  constructor dated-entry
  field
    lane : Lane
    dateBrisbane : String
    evidenceKind : EvidenceKind
    repositoryReference : String
    objectOrRoute : String
    role : HistoricalRole
    interpretation : String

open DatedArchaeologyEntry public

------------------------------------------------------------------------
-- LATER CONSOLIDATION / RECOVERY CHRONOLOGY.
--
-- These dates must be read after preJulyArchaeologyAnchors.  They record later
-- source-faithful formalization, route proliferation, compression and consumer
-- recovery, not the origin of the programmes.
------------------------------------------------------------------------

canonicalDatedArchaeology : List DatedArchaeologyEntry
canonicalDatedArchaeology =

  dated-entry riemannHypothesis "2026-07-19" exactCommitDate
    "commit 78bdf33b725596bd0c1bc399a3e5bb78cc9bb14c / PR #100"
    "Riemann zeta + DASHI-Weil explicit-formula theorem ladder"
    compiler
    "Formal consolidation of a broader RH/Weil route; it postdates the May zeta/phase diagnostic ancestry and is not yet the later literal pole-quotient producer."
  ∷

  dated-entry grQuantum "2026-07-20" pullRequestDate
    "PR #246"
    "deep GR/quantum research authority cutset"
    terminalConsumer
    "Later formal consolidation of an already-existing GR/QFT programme: continuum geometry, anomaly freedom, renormalized amplitudes, low-energy recovery and empirical correspondence. Useful terminal gate, too broad as first proof-search target."
  ∷

  dated-entry yangMills "2026-07-21" pullRequestDate
    "PR #309"
    "source-faithful Balaban matching + unconditional YM solution gate"
    terminalConsumer
    "Later source-faithful refinement. Uniform positive clustering and a physical Hamiltonian gap remain explicit unresolved obligations, continuous with the May mass-gap boundary."
  ∷

  dated-entry yangMills "2026-07-29" exactCommitDate
    "commit c4910cdcde12c764c818545fb658bb93171c471b"
    "BalabanClayT5ClusteringToTransferGapExact"
    compiler
    "The modern clustering-to-gap consumer already existed by July: quantitative clustering plus spectral interpretation excludes positive subgap modes."
  ∷

  dated-entry yangMills "2026-08-05" repositorySequence
    "commits f6759d1f4bf5ac94da33906717147ce33eafe363 and 4f5fc7e4d941d324534b543c1103129432106943"
    "lattice-to-physical clustering exponent transport + dense-core clustering-to-gap route"
    compiler
    "Downstream spectral conversion was mature early; missing mathematics is upstream quantitative physical clustering."
  ∷

  dated-entry riemannHypothesis "2026-08-21" repositorySequence
    "Riemann Hermitian/top-down commit tranche beginning cb78f41b6f32955cc0121eb61dd8d78a6d133e54"
    "Hermitian retention / mixed interference / Poisson / alpha-square coercivity family"
    producerTactic
    "Important alternate producer ancestry and diagnostic vocabulary; not identical to the later final pole-quotient consumer."
  ∷

  dated-entry grQuantum "2026-08-30" pullRequestDate
    "PR #639"
    "endpoint-only QFT/GR common metric + action variation + stress weld"
    directProducer
    "Consumer sharpening: target one physical same-object theorem delta S[h] = <T,h> on one common metric language rather than the old monolithic terminal composition object."
  ∷

  dated-entry yangMills "2026-08-31" exactCommitDate
    "commit 0ab210dfa75c584699decb64869eb2fa1d293ae3 / Round146"
    "literal CMP98 Eq.(119) one-step derivative"
    sourceTranscriptionDebt
    "Literal source reconstruction phase: represent the source operator exactly and discharge same-object lattice/background semantics rather than inventing another qPrime socket."
  ∷

  dated-entry riemannHypothesis "2026-08-31" pullRequestDate
    "PR #677"
    "H_X -> H_A -> H_M -> H_T -> H_W -> H_E phase/modulation chain"
    supersededOverpayment
    "Historically useful decomposition. Later least-privilege work showed several layers were producer/representation structure rather than primitive terminal obligations."
  ∷

  dated-entry riemannHypothesis "2026-09-10" pullRequestDate
    "PR #855"
    "generic high contradiction with direct-phase and certified-upper producers"
    terminalConsumer
    "Canonical-consumer recovery: the high-side consumer becomes implementation-neutral; direct analytic and proof-carrying numerical routes compile to the same contradiction."
  ∷

  dated-entry yangMills "2026-09-10" pullRequestDate
    "PR #869"
    "canonical mass-gap search normalized to quantitative clustering consumer"
    terminalConsumer
    "Canonical-consumer recovery: Heat/Doob/Langevin/Dyson, unified polymer norms and source-native cluster expansion become optional tactics. This recovers an older consumer rather than inventing a new route."
  ∷ []

------------------------------------------------------------------------
-- BURIED-DONOR WINDOWS.
------------------------------------------------------------------------

record BuriedDonorWindow : Set where
  constructor donor-window
  field
    donorLane : Lane
    fromDate : String
    toDate : String
    searchByOutputShape : String
    whyThisWindow : String

open BuriedDonorWindow public

canonicalBuriedDonorWindows : List BuriedDonorWindow
canonicalBuriedDonorWindows =
  donor-window yangMills "2026-05-01" "2026-08-20"
    "physical mass-gap / correlation-decay / coercivity / reflection-positive / transfer-semigroup theorem on a carrier transportable to the same continuum Schwinger family"
    "The May boundary already has the gap and continuum wall; July-August then expands Balaban, clustering, decoupling and spectral machinery. Search the whole ancestry, not only rounds after July."
  ∷ donor-window riemannHypothesis "2026-05-01" "2026-08-31"
    "phase-sensitive zeta/zero response, reflection-paired oscillatory inequality, or one-sided target-centred upper bound"
    "May already has Abel-zeta phase/spacing diagnostic ancestry. July Weil and August Hermitian/pole routes are later layers; search aliases across the full interval."
  ∷ donor-window grQuantum "2026-05-01" "2026-08-30"
    "same action variation / metric perturbation / stress-energy identity across literal theory sectors"
    "The May terminal composition already names a stress-energy bridge; July and August sharpen rather than originate the unification programme."
  ∷ donor-window navierStokes "2026-05-01" "current"
    "signed physical production/transfer retained before absolute value, then uniform spacetime/potential payment"
    "May typed regularity/enstrophy/vorticity walls and June dashiCFD physical experiments predate the round-labelled signed-transfer programme. Search sibling repos and semantic aliases."
  ∷ []

------------------------------------------------------------------------
-- CANONICAL PROOF-SEARCH TARGETS.
------------------------------------------------------------------------

record LiveFrontier : Set where
  constructor live-frontier
  field
    frontierLane : Lane
    literalConsumer : String
    firstLiveLevel2Theorem : String
    knownCompilers : String
    optionalProducerFamilies : String
    sameObjectFirewall : String
    nextArchaeologySearch : String

open LiveFrontier public

nsFrontier : LiveFrontier
nsFrontier = live-frontier navierStokes
  "critical-cone / physical high-frequency regularity consumer"
  "cutoff-uniform signed physical transfer/production -> spacetime or potential-budget payment"
  "finite-depth enstrophy/vorticity tower; Abel/telescope/Gram/resolvent/critical-cone transports downstream where inputs are available"
  "May BKM/enstrophy ancestry; June dashiCFD truth/theta diagnostics; signed commutator; spectator resolvent; packet/danger families"
  "do not take absolute values or quotient away sign/coherence before the physical consumer is paid"
  "search May-June pre-round and sibling-repo aliases for signed transfer + dissipation/potential comparison composed in the correct order"

yangMillsFrontier : LiveFrontier
yangMillsFrontier = live-frontier yangMills
  "same reconstructed continuum family with quantitative connected-correlation decay and positive physical spectral gap"
  "quantitative continuum clustering on the same physical Schwinger family; independently identify the positive candidate decay rate with the physical spectrum"
  "May mass-gap boundary; clustering-to-transfer-gap; OS reconstruction; dense-core and lattice-to-physical exponent transports"
  "finite-depth RG/coercivity/reflection-positive ancestry; CMP109/CMP116 Hessian influence; Langevin/Dyson; Balaban cluster expansion; unified polymer/Schwinger norm"
  "finite/RG decay, generic Clustered predicates or selected-carrier gaps may not be silently identified with prize-facing same-family quantitative continuum clustering"
  "search May-August ancestry by theorem output, especially direct correlation decay or transfer-semigroup decay, before paying Row-C machinery again"

rhFrontier : LiveFrontier
rhFrontier = live-frontier riemannHypothesis
  "forall high off-line zero: contradiction on the actual universal pole-quotient response"
  "uniform strict high-side bound on the literal reflection-paired oscillatory response; executable route reduces further to proof-bearing one-sided finite-cell uppers"
  "near/far monotonicity, certificate folding, Off/Gamma compilers, high contradiction and high/low terminal compilation"
  "May Abel-zeta phase diagnostics; July Weil; August Hermitian/interference; direct phase-visible; certified interval/rational; integration-by-parts/Taylor/quadrature"
  "diagnostic phase ancestry is not same-object proof; analytic payment cannot see downstream balance; determinant taper, coarse counts and absolute envelopes are not final pole quotient"
  "search May-August aliases for a signed/phase-sensitive bound that lands or transports exactly to current cellResponse/nearResponse"

grQuantumFrontier : LiveFrontier
grQuantumFrontier = live-frontier grQuantum
  "one common physical metric/action language whose QFT and Einstein variations yield the same stress-energy source"
  "instantiate the same-action/same-stress weld on literal sectors; after that true QG jump is anomaly-free quantum dynamics + renormalized continuum amplitudes + semiclassical GR/backreaction recovery"
  "May terminal stress-energy target; endpoint-only sector variation; native-stress transport; common metric language; pairing commutation; SameStressEnergyWeld"
  "older stress-energy/Noether/action variation owners; YM stress recovery; Maxwell/scalar/spinor/Higgs sectors; Einstein-Hilbert variation and pairing separation"
  "shared names, flat compatibility or terminal target status do not establish same action, same metric, same stress tensor, interaction or quantum gravity"
  "search May-August variational/Noether/stress ancestry for literal sector inhabitants of the common-action endpoint before broad QG proof search"

canonicalLiveFrontiers : List LiveFrontier
canonicalLiveFrontiers =
  nsFrontier ∷ yangMillsFrontier ∷ rhFrontier ∷ grQuantumFrontier ∷ []

------------------------------------------------------------------------
-- CROSS-PROGRAMME ARCHAEOLOGY DISCIPLINE.
------------------------------------------------------------------------

record ArchaeologyDiscipline : Set where
  constructor archaeology-discipline
  field
    consumerFirst : Bool
    roundNumbersAreOnlyOneIndex : Bool
    searchSemanticAliases : Bool
    searchSiblingRepositories : Bool
    distinguishHistoricalClocks : Bool
    earliestConfirmedDateIsOnlyLowerBound : Bool
    compilerDoesNotCreateAnalyticContent : Bool
    producerTacticIsNotMandatoryRoute : Bool
    sameObjectBeforePromotion : Bool
    negativeResultsPruneRoutes : Bool
    datesRemainProvenanceNotProof : Bool

canonicalArchaeologyDiscipline : ArchaeologyDiscipline
canonicalArchaeologyDiscipline = archaeology-discipline
  true true true true true true true true true true true

------------------------------------------------------------------------
-- HUMAN-READABLE CATALYST SUMMARY.
------------------------------------------------------------------------

record ProofCatalystDashboard : Set where
  constructor proof-catalyst-dashboard
  field
    nsTarget : String
    ymTarget : String
    rhTarget : String
    grQuantumTarget : String
    historicalWarning : String

canonicalProofCatalystDashboard : ProofCatalystDashboard
canonicalProofCatalystDashboard = proof-catalyst-dashboard
  "NS: signed physical transfer -> uniform spacetime/potential payment"
  "YM: continuum physical measure/Schwinger family -> quantitative clustering -> physical spectrum"
  "RH: literal oscillatory zero response -> uniform strict high margin"
  "GR/QFT: literal sector + Einstein variations -> same action/metric/stress weld -> anomaly/UV/semiclassical QG recovery"
  "Dates are lower bounds: construction ancestry predates the July formal consolidation wave; search backwards by output shape and prove same-object transport before reuse."
