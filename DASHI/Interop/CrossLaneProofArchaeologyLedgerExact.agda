module DASHI.Interop.CrossLaneProofArchaeologyLedgerExact where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.String using (String)
open import Agda.Builtin.List using (List; []; _∷_)

------------------------------------------------------------------------
-- CROSS-LANE PROOF ARCHAEOLOGY LEDGER
--
-- One inspectable navigation/proof-search owner for NS, YM, RH and GR/QFT.
-- Dates are evidenced repository LOWER BOUNDS, never origin claims.
-- Construction ancestry, first typed appearance, later formal consolidation
-- and canonical-consumer recovery are deliberately different clocks.
-- Existing mathematical owners remain authoritative.
------------------------------------------------------------------------

data Lane : Set where
  navierStokes yangMills riemannHypothesis grQuantum : Lane

data HistoricalRole : Set where
  terminalConsumer directProducer producerTactic compiler
  representationWeld negativeControl diagnostic supersededOverpayment
  sourceTranscriptionDebt liveLevel2Theorem : HistoricalRole

data EvidenceKind : Set where
  exactCommitDate pullRequestDate repositorySequence historicalInference : EvidenceKind

data HistoricalClock : Set where
  constructionAncestry firstTypedAppearance formalConsolidation
  canonicalConsumerRecovery : HistoricalClock

data HistoricalIdentityStatus : Set where
  sameObjectProved structuralAncestorOnly candidateAlias notSameObject : HistoricalIdentityStatus

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
-- EARLIEST CURRENTLY CONFIRMED LANE-SPECIFIC ANCHORS.
------------------------------------------------------------------------

preJulyArchaeologyAnchors : List ClockedArchaeologyAnchor
preJulyArchaeologyAnchors =
  clocked-anchor riemannHypothesis "2026-04-17" constructionAncestry
    exactCommitDate
    "dashi_agda commit d59286c1eed63a1441b9243af031dbcf50f0edc5; file history DASHI/Analysis/ZetaVisualization.agda"
    "Abel-zeta sampling + phase/zero-spacing feature views + explicit no-RH boundary"
    diagnostic notSameObject
    "RH/zeta work is already present in April. It is deliberately visualization-first/non-theorem-bearing, so it is conceptual ancestry for later phase-sensitive searches, not the same carrier as the universal pole-quotient high producer."
  ∷
  clocked-anchor grQuantum "2026-05-17" firstTypedAppearance
    exactCommitDate
    "dashi_agda commit 81fc16c11af4f4152410ea9ce9269c68cc223387; file history DASHI/Physics/Closure/GRQFTTerminalCompositionBoundary.agda"
    "GR/QFT terminal composition: discrete-to-smooth, AQFT, stress-energy bridge, receipt composition"
    terminalConsumer structuralAncestorOnly
    "The GR/QFT terminal programme predates July by at least two months. Later QG cutsets and the August common-action weld sharpen an older stress-energy/composition target."
  ∷
  clocked-anchor yangMills "2026-05-27" firstTypedAppearance
    exactCommitDate
    "dashi_agda commit 6e423ec962cc43ee1e678b490d253abb61ed8ef0; file history DASHI/Physics/Closure/YangMillsMassGapBoundary.agda"
    "YM mass-gap boundary: coercivity, reflection/transfer positivity, spectral isolation, continuum stability, physical-spectrum transport"
    terminalConsumer structuralAncestorOnly
    "The typed YM mass-gap consumer predates the July source-faithful Bałaban wave. It already distinguishes selected/finite receipts from the physical continuum Hamiltonian spectrum."
  ∷
  clocked-anchor navierStokes "2026-05-29" firstTypedAppearance
    exactCommitDate
    "dashi_agda commit bdd0801cc7e544304c52412ea1ccd0164904d12f; file histories NavierStokesRegularityTowerReceipt.agda and NavierStokesWeakSolutionInterface.agda"
    "finite-depth enstrophy/vorticity/weak-solution tower with continuum BKM/Serrin/nonlinear-control wall"
    terminalConsumer structuralAncestorOnly
    "The typed NS continuum wall predates the later round-labelled signed-transfer constructions. Finite-depth enstrophy/vorticity control is explicitly not promoted to PDE regularity."
  ∷
  clocked-anchor navierStokes "2026-06-04" constructionAncestry
    exactCommitDate
    "chboishabba/dashiCFD commit 125e52e04bed4042890d95db5d5371104ba1aafe and descendants"
    "3D periodic incompressible truth + Leray/vorticity shells + shell-enstrophy + flux/dissipation theta diagnostics"
    diagnostic candidateAlias
    "dashiCFD was already testing the physical NS carrier and a flux/dissipation barrier before the later signed analytic route. The absolute-flux theta diagnostic is not silently identified with the later signed theorem."
  ∷ []

------------------------------------------------------------------------
-- REPOSITORY-LEVEL LOWER BOUNDS.
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
  repository-lower-bound "chboishabba/dashiCORE" "2026-03-05"
    "commit 684b899b3b05b4fbbf6799fe368c5da6551f0c13 and descendants"
    "Cross-programme implementation ancestry predates the currently confirmed lane-specific dashi_agda anchors; exact lane/same-object lineage still requires file-level recovery."
    false
  ∷ repository-lower-bound "chboishabba/dashi_agda" "2026-04-17"
    "RH file history d59286c1eed63a1441b9243af031dbcf50f0edc5"
    "Current lane-specific lower bound; repository ancestry itself may be older."
    false
  ∷ repository-lower-bound "chboishabba/dashiCFD" "2026-06-04"
    "commit 125e52e04bed4042890d95db5d5371104ba1aafe and descendants"
    "NS empirical/physical construction ancestry; not theorem promotion."
    false
  ∷ []

------------------------------------------------------------------------
-- HISTORICAL ALIAS / SAME-OBJECT FIREWALL.
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
    "dashiCFD shell flux/theta/signed-transfer family"
    "dashi_agda signed physical transfer -> uniform critical-cone payment"
    "same physical theme and candidate barrier; empirical absolute-flux theta is not definitionally the signed analytic carrier"
    candidateAlias
  ∷ historical-alias riemannHypothesis
    "April Abel-zeta phase/zero-spacing visualization"
    "September universal pole-quotient literal response"
    "phase-sensitive ancestry only; different carrier and theorem"
    notSameObject
  ∷ historical-alias yangMills
    "May finite-depth/RG mass-gap and Stone-spectrum target"
    "September same-family quantitative continuum clustering consumer"
    "downstream-compatible ancestry; does not itself inhabit the clustering theorem"
    structuralAncestorOnly
  ∷ historical-alias grQuantum
    "May GRQFT stress-energy/composition target"
    "August endpoint-only common action/metric/stress weld"
    "later route sharpens the old target to one same-object variational consumer"
    structuralAncestorOnly
  ∷ []

------------------------------------------------------------------------
-- LATER FORMAL CONSOLIDATION / ROUTE COMPRESSION.
------------------------------------------------------------------------

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

canonicalDatedArchaeology : List DatedArchaeologyEntry
canonicalDatedArchaeology =
  dated-entry riemannHypothesis "2026-07-19" exactCommitDate
    "commit 78bdf33b725596bd0c1bc399a3e5bb78cc9bb14c / PR #100"
    "DASHI-Weil / explicit-formula theorem ladder" compiler
    "Later formal consolidation of an RH route whose zeta/phase ancestry is already visible in April."
  ∷ dated-entry grQuantum "2026-07-20" pullRequestDate
    "PR #246" "deep GR/quantum research authority cutset" terminalConsumer
    "Later comprehensive terminal gate; useful promotion contract, too broad as first proof-search target."
  ∷ dated-entry yangMills "2026-07-21" pullRequestDate
    "PR #309" "source-faithful Balaban matching + unconditional YM gate" terminalConsumer
    "Later source-faithful refinement of a May mass-gap programme; uniform clustering and physical gap remain genuine obligations."
  ∷ dated-entry yangMills "2026-07-29" exactCommitDate
    "commit c4910cdcde12c764c818545fb658bb93171c471b"
    "BalabanClayT5ClusteringToTransferGapExact" compiler
    "Clustering-to-gap spectral consumer is explicit by July; downstream gap compilation is not the missing Level-2 physics."
  ∷ dated-entry yangMills "2026-08-05" repositorySequence
    "commits f6759d1f4bf5ac94da33906717147ce33eafe363 + 4f5fc7e4d941d324534b543c1103129432106943"
    "lattice-to-physical clustering exponent + dense-core clustering-to-gap" compiler
    "Spectral conversion matures while upstream quantitative physical clustering remains the real producer problem."
  ∷ dated-entry riemannHypothesis "2026-08-21" repositorySequence
    "Hermitian/top-down tranche beginning cb78f41b6f32955cc0121eb61dd8d78a6d133e54"
    "retained pair / interference / Poisson / alpha-square coercivity" producerTactic
    "Alternate producer ancestry; not identical to the final pole-quotient response."
  ∷ dated-entry grQuantum "2026-08-30" pullRequestDate
    "PR #639" "endpoint-only common metric/action/stress weld" directProducer
    "Consumer sharpening: one physical variational/stress theorem replaces monolithic downstream knowledge of QFT manufacturing details."
  ∷ dated-entry yangMills "2026-08-31" exactCommitDate
    "commit 0ab210dfa75c584699decb64869eb2fa1d293ae3 / Round146"
    "literal CMP98 Eq.(119) one-step derivative" sourceTranscriptionDebt
    "Literal source reconstruction phase; valuable same-object plumbing, not automatically the prize-facing clustering producer."
  ∷ dated-entry riemannHypothesis "2026-08-31" pullRequestDate
    "PR #677" "H_X -> H_A -> H_M -> H_T -> H_W -> H_E" supersededOverpayment
    "Useful decomposition later compressed when representation/producer structure was separated from primitive analytic debt."
  ∷ dated-entry riemannHypothesis "2026-09-10" pullRequestDate
    "PR #855" "generic high contradiction; direct-phase and certified-upper producers" terminalConsumer
    "Canonical-consumer recovery: implementation-neutral high contradiction."
  ∷ dated-entry yangMills "2026-09-10" pullRequestDate
    "PR #869" "normalize mass-gap search to quantitative clustering consumer" terminalConsumer
    "Canonical-consumer recovery: sophisticated sufficient tactics are demoted; the old direct consumer returns to the centre."
  ∷ []

------------------------------------------------------------------------
-- BURIED-DONOR WINDOWS: SEARCH BY OUTPUT SHAPE, NOT ROUND NUMBER.
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
  donor-window yangMills "2026-05-27" "2026-08-20"
    "physical mass-gap/correlation-decay/coercivity/reflection-positive/transfer-semigroup theorem transportable to the same continuum Schwinger family"
    "May already contains the typed mass-gap wall; July-August adds Balaban, clustering, decoupling and spectral machinery."
  ∷ donor-window riemannHypothesis "2026-04-17" "2026-08-31"
    "phase-sensitive zeta/zero response, reflection-paired oscillatory inequality, or one-sided target-centred upper bound"
    "April zeta/phase diagnostics precede July Weil and August Hermitian/pole families."
  ∷ donor-window grQuantum "2026-05-17" "2026-08-30"
    "same action variation / metric perturbation / stress-energy identity across literal theory sectors"
    "May terminal composition already names the stress-energy bridge; later work sharpens it."
  ∷ donor-window navierStokes "2026-05-29" "current"
    "signed physical production/transfer retained before absolute value, then uniform spacetime/potential payment"
    "May typed continuum wall plus June dashiCFD experiments predate the round-labelled signed-transfer programme."
  ∷ []

------------------------------------------------------------------------
-- CANONICAL CURRENT PROOF-SEARCH TARGETS.
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
  "May enstrophy/vorticity tower; Abel/telescope/Gram/resolvent/critical-cone transports"
  "dashiCFD truth/theta; signed commutator; spectator resolvent; packet/danger families"
  "do not take absolute value or quotient away sign/coherence before payment"
  "search May-June pre-round and sibling-repo aliases for signed transfer + dissipation/potential comparison in the correct order"

yangMillsFrontier : LiveFrontier
yangMillsFrontier = live-frontier yangMills
  "same reconstructed continuum family: quantitative connected-correlation decay -> positive physical spectral gap"
  "quantitative continuum clustering on that same Schwinger family; separately identify candidate decay rate with physical spectrum"
  "May gap boundary; OS reconstruction; clustering-to-gap; dense-core; lattice-to-physical exponent transports"
  "coercivity/reflection-positive ancestry; CMP109/CMP116 influence; Langevin/Dyson; Balaban cluster expansion; polymer/Schwinger norm"
  "finite/RG decay, generic Clustered or selected-carrier gaps are not the prize-facing same-family clustering theorem"
  "search May-August history by direct correlation-decay/transfer-semigroup output before paying Row-C again"

rhFrontier : LiveFrontier
rhFrontier = live-frontier riemannHypothesis
  "forall high off-line zero: contradiction on actual universal pole-quotient response"
  "uniform strict high-side bound on literal reflection-paired oscillatory response; executable route: proof-bearing one-sided finite-cell uppers"
  "near/far monotonicity; certificate folding; Off/Gamma; high contradiction; high/low terminal compiler"
  "April phase diagnostics; July Weil; August Hermitian/interference; direct phase; certified interval/rational; IBP/Taylor/quadrature"
  "diagnostic ancestry is not same-object proof; payment cannot see downstream balance; determinant/coarse-count/absolute-envelope routes are not final carrier"
  "search April-August aliases for signed/phase-sensitive bounds that land or exactly transport to cellResponse/nearResponse"

grQuantumFrontier : LiveFrontier
grQuantumFrontier = live-frontier grQuantum
  "one common physical metric/action language whose QFT and Einstein variations yield the same stress-energy source"
  "instantiate same-action/same-stress on literal sectors; then anomaly-free dynamics + renormalized continuum amplitudes + semiclassical GR/backreaction"
  "May stress-energy target; endpoint sector variation; native-stress transport; common metric; pairing commutation; SameStressEnergyWeld"
  "old Noether/action/stress owners; YM; Maxwell/scalar/spinor/Higgs; Einstein-Hilbert variation/separation"
  "shared names, flat compatibility or target status do not prove same action/metric/stress or quantum gravity"
  "search May-August variational/Noether/stress ancestry for literal sector inhabitants before broad QG search"

canonicalLiveFrontiers : List LiveFrontier
canonicalLiveFrontiers =
  nsFrontier ∷ yangMillsFrontier ∷ rhFrontier ∷ grQuantumFrontier ∷ []

------------------------------------------------------------------------
-- DISCIPLINE / CATALYST.
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
  "YM: continuum physical Schwinger family -> quantitative clustering -> physical spectrum"
  "RH: literal oscillatory zero response -> uniform strict high margin"
  "GR/QFT: literal sector + Einstein variations -> same action/metric/stress weld -> anomaly/UV/semiclassical QG recovery"
  "Dates are lower bounds only. April/May lane-specific ancestry and March dashiCORE ancestry already predate the July formal consolidation wave; keep searching backwards by output shape and prove same-object transport before reuse."
