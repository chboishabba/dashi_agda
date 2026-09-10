module DASHI.Interop.CrossLaneProofArchaeologyLedgerExact where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.String using (String)
open import Agda.Builtin.List using (List; []; _∷_)

------------------------------------------------------------------------
-- CROSS-LANE PROOF ARCHAEOLOGY LEDGER
--
-- One inspectable navigation/proof-search owner for NS, YM, RH and GR/QFT.
-- Dates are evidenced repository LOWER BOUNDS, never origin claims.
-- Keep distinct: construction ancestry, first typed appearance, later formal
-- consolidation, and canonical-consumer recovery.
-- Existing mathematical owners remain authoritative.
------------------------------------------------------------------------

data Lane : Set where
  navierStokes yangMills riemannHypothesis grQuantum : Lane

data HistoricalRole : Set where
  terminalConsumer directProducer producerTactic compiler representationWeld
  negativeControl diagnostic supersededOverpayment sourceTranscriptionDebt
  liveLevel2Theorem : HistoricalRole

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
  clocked-anchor riemannHypothesis "2026-02-23" constructionAncestry exactCommitDate
    "dashi_agda commit 8bf9e75a159e90c837836a998a43f55680ae66a9; file history DASHI/Analysis/AbelZeta.agda"
    "Abel-summed eta/zeta analytic-continuation carrier"
    diagnostic structuralAncestorOnly
    "RH/zeta analytic machinery is already present in February. It predates the April visualization, July Weil ladder, August Hermitian family and September pole-quotient route; exact transport into the final pole response is not inferred."
  ∷ clocked-anchor riemannHypothesis "2026-04-17" constructionAncestry exactCommitDate
    "dashi_agda commit d59286c1eed63a1441b9243af031dbcf50f0edc5; file history DASHI/Analysis/ZetaVisualization.agda"
    "phase/zero-spacing feature views over Abel-zeta samples with explicit no-RH boundary"
    diagnostic notSameObject
    "Phase-visible zeta exploration predates the later proof-search families but is intentionally non-theorem-bearing and is not the universal pole-quotient carrier."
  ∷ clocked-anchor grQuantum "2026-05-12" firstTypedAppearance exactCommitDate
    "dashi_agda commit 78c96a5c27795f3c3f7500bad71d4db72f53755e; file history DASHI/Physics/Closure/W4MatterStressEnergyInterfaceReceipt.agda"
    "matter/stress-energy interface ancestry"
    representationWeld structuralAncestorOnly
    "The stress-energy seam that later becomes the common-action/common-stress consumer is already typed by 12 May."
  ∷ clocked-anchor grQuantum "2026-05-17" firstTypedAppearance exactCommitDate
    "dashi_agda commit 81fc16c11af4f4152410ea9ce9269c68cc223387; file history DASHI/Physics/Closure/GRQFTTerminalCompositionBoundary.agda"
    "GR/QFT terminal composition: discrete-to-smooth, AQFT, stress-energy bridge, receipt composition"
    terminalConsumer structuralAncestorOnly
    "The broad terminal programme therefore predates the July QG cutset and August common-action normalization."
  ∷ clocked-anchor yangMills "2026-05-17" firstTypedAppearance exactCommitDate
    "dashi_agda commit 81fc16c11af4f4152410ea9ce9269c68cc223387; file history DASHI/Physics/Closure/BalabanRGMassGapReceiptSurface.agda"
    "Balaban RG -> finite gap / mass-gap receipt surface"
    producerTactic structuralAncestorOnly
    "A Balaban/RG mass-gap route exists by 17 May, well before the July source-faithful tranche. It is historical producer ancestry, not automatically the later same-family quantitative continuum clustering theorem."
  ∷ clocked-anchor yangMills "2026-05-27" firstTypedAppearance exactCommitDate
    "dashi_agda commit 6e423ec962cc43ee1e678b490d253abb61ed8ef0; file history DASHI/Physics/Closure/YangMillsMassGapBoundary.agda"
    "YM physical gap boundary: reflection/transfer positivity, spectral isolation, continuum stability, physical-spectrum transport"
    terminalConsumer structuralAncestorOnly
    "The explicit physical-spectrum consumer is typed by 27 May; July is a later refinement wave."
  ∷ clocked-anchor navierStokes "2026-05-29" firstTypedAppearance exactCommitDate
    "dashi_agda commit bdd0801cc7e544304c52412ea1ccd0164904d12f; NavierStokesRegularityTowerReceipt.agda + NavierStokesWeakSolutionInterface.agda"
    "finite-depth enstrophy/vorticity/weak-solution tower with continuum BKM/Serrin/nonlinear-control wall"
    terminalConsumer structuralAncestorOnly
    "The typed NS continuum wall predates the round-labelled signed-transfer family; finite-depth control is explicitly not promoted to PDE regularity."
  ∷ clocked-anchor navierStokes "2026-06-04" constructionAncestry exactCommitDate
    "chboishabba/dashiCFD commit 125e52e04bed4042890d95db5d5371104ba1aafe and descendants"
    "3D periodic incompressible truth + Leray/vorticity shells + shell-enstrophy + flux/dissipation theta diagnostics"
    diagnostic candidateAlias
    "The physical NS carrier and flux/dissipation barrier were being tested before later Agda rounds; absolute-flux theta is not silently identified with the later signed theorem."
  ∷ []

record RepositoryAncestryLowerBound : Set where
  constructor repository-lower-bound
  field
    repository earliestConfirmedDateBrisbane evidenceReference relevance : String
    originClaim : Bool

open RepositoryAncestryLowerBound public

repositoryAncestryLowerBounds : List RepositoryAncestryLowerBound
repositoryAncestryLowerBounds =
  repository-lower-bound "chboishabba/dashi_agda" "2026-02-23"
    "AbelZeta file history 8bf9e75a159e90c837836a998a43f55680ae66a9"
    "Earliest currently pinned lane-specific mathematical ancestor in this audit; not an origin claim." false
  ∷ repository-lower-bound "chboishabba/dashiCORE" "2026-03-05"
    "commit 684b899b3b05b4fbbf6799fe368c5da6551f0c13 and descendants"
    "Cross-programme sibling-repo ancestry; lane-specific same-object lineage still requires file-level recovery." false
  ∷ repository-lower-bound "chboishabba/dashiCFD" "2026-06-04"
    "commit 125e52e04bed4042890d95db5d5371104ba1aafe and descendants"
    "NS physical/empirical construction ancestry." false
  ∷ []

record HistoricalAliasBridge : Set where
  constructor historical-alias
  field
    aliasLane : Lane
    oldReference laterCanonicalReference outputShapeRelation : String
    identityStatus : HistoricalIdentityStatus

open HistoricalAliasBridge public

canonicalHistoricalAliasBridges : List HistoricalAliasBridge
canonicalHistoricalAliasBridges =
  historical-alias navierStokes
    "dashiCFD shell flux/theta/signed-transfer family"
    "dashi_agda signed physical transfer -> uniform critical-cone payment"
    "candidate physical ancestor; absolute-flux theta is not definitionally the signed analytic carrier" candidateAlias
  ∷ historical-alias riemannHypothesis
    "February AbelZeta + April phase/spacing visualization"
    "September universal pole-quotient literal response"
    "analytic/phase ancestry exists, but carrier identity and final strict theorem are not inherited" structuralAncestorOnly
  ∷ historical-alias yangMills
    "May Balaban RG mass-gap receipt + physical gap boundary"
    "September same-family quantitative continuum clustering consumer"
    "same programme and downstream target; old finite/RG gap route does not itself inhabit continuum clustering" structuralAncestorOnly
  ∷ historical-alias grQuantum
    "May matter/stress-energy interface + GRQFT terminal composition"
    "August endpoint-only common action/metric/stress weld"
    "later route sharpens an old stress-energy target to one common variational carrier" structuralAncestorOnly
  ∷ []

record DatedArchaeologyEntry : Set where
  constructor dated-entry
  field
    lane : Lane
    dateBrisbane : String
    evidenceKind : EvidenceKind
    repositoryReference objectOrRoute : String
    role : HistoricalRole
    interpretation : String

open DatedArchaeologyEntry public

canonicalDatedArchaeology : List DatedArchaeologyEntry
canonicalDatedArchaeology =
  dated-entry riemannHypothesis "2026-07-19" exactCommitDate
    "commit 78bdf33b725596bd0c1bc399a3e5bb78cc9bb14c / PR #100"
    "DASHI-Weil / explicit-formula theorem ladder" compiler
    "Formal consolidation, not origin: Abel-zeta ancestry is already pinned in February."
  ∷ dated-entry grQuantum "2026-07-20" pullRequestDate "PR #246"
    "deep GR/quantum research authority cutset" terminalConsumer
    "Comprehensive later promotion gate; the stress-energy/unification spine is already present in May."
  ∷ dated-entry yangMills "2026-07-21" pullRequestDate "PR #309"
    "source-faithful Balaban matching + unconditional YM gate" terminalConsumer
    "Source-faithful consolidation of a Balaban/mass-gap lane already visible in May."
  ∷ dated-entry yangMills "2026-07-29" exactCommitDate
    "commit c4910cdcde12c764c818545fb658bb93171c471b"
    "clustering-to-transfer-gap spectral cutset" compiler
    "Downstream gap compilation is explicit; quantitative continuum clustering remains upstream physics."
  ∷ dated-entry yangMills "2026-08-05" repositorySequence
    "f6759d1f4bf5ac94da33906717147ce33eafe363 + 4f5fc7e4d941d324534b543c1103129432106943"
    "lattice-to-physical clustering exponent + dense-core clustering-to-gap" compiler
    "Spectral conversion matures while the direct clustering producer remains the key theorem."
  ∷ dated-entry riemannHypothesis "2026-08-21" repositorySequence
    "Hermitian/top-down tranche beginning cb78f41b6f32955cc0121eb61dd8d78a6d133e54"
    "retained pair / interference / Poisson / alpha-square coercivity" producerTactic
    "Alternate producer family; not identical to final pole quotient."
  ∷ dated-entry grQuantum "2026-08-30" pullRequestDate "PR #639"
    "endpoint-only common metric/action/stress weld" directProducer
    "Consumer sharpening of the May stress-energy spine."
  ∷ dated-entry yangMills "2026-08-31" exactCommitDate
    "0ab210dfa75c584699decb64869eb2fa1d293ae3 / Round146"
    "literal CMP98 Eq.(119) one-step derivative" sourceTranscriptionDebt
    "Literal source reconstruction; valuable same-object plumbing, not automatically the clustering producer."
  ∷ dated-entry riemannHypothesis "2026-08-31" pullRequestDate "PR #677"
    "H_X -> H_A -> H_M -> H_T -> H_W -> H_E" supersededOverpayment
    "Useful decomposition later compressed once producer/representation debt was separated from terminal analytic debt."
  ∷ dated-entry riemannHypothesis "2026-09-10" pullRequestDate "PR #855"
    "generic high contradiction with direct-phase and certified-upper producers" terminalConsumer
    "Canonical-consumer recovery."
  ∷ dated-entry yangMills "2026-09-10" pullRequestDate "PR #869"
    "normalize mass-gap search to quantitative clustering consumer" terminalConsumer
    "Canonical-consumer recovery: sophisticated producer tactics are demoted rather than mistaken for prerequisites."
  ∷ []

record BuriedDonorWindow : Set where
  constructor donor-window
  field
    donorLane : Lane
    fromDate toDate searchByOutputShape whyThisWindow : String

open BuriedDonorWindow public

canonicalBuriedDonorWindows : List BuriedDonorWindow
canonicalBuriedDonorWindows =
  donor-window yangMills "2026-05-17" "2026-08-20"
    "correlation decay / transfer-semigroup decay / physical gap / coercivity theorem transportable to SAME continuum Schwinger family"
    "Balaban/RG mass-gap work exists by 17 May; search before paying later Row-C machinery again."
  ∷ donor-window riemannHypothesis "2026-02-23" "2026-08-31"
    "phase-sensitive zeta response / reflection-paired oscillatory inequality / one-sided target-centred upper bound"
    "Abel-zeta machinery predates every later named RH route in the current assay."
  ∷ donor-window grQuantum "2026-05-12" "2026-08-30"
    "same action variation / metric perturbation / stress-energy identity across literal sectors"
    "Stress-energy interface predates the terminal composition and the August common-action weld."
  ∷ donor-window navierStokes "2026-05-29" "current"
    "signed physical production/transfer retained before absolute value -> uniform spacetime/potential payment"
    "May continuum wall plus June dashiCFD experiments predate round-labelled signed-transfer work."
  ∷ []

record LiveFrontier : Set where
  constructor live-frontier
  field
    frontierLane : Lane
    literalConsumer firstLiveLevel2Theorem knownCompilers optionalProducerFamilies
      sameObjectFirewall nextArchaeologySearch : String

open LiveFrontier public

nsFrontier : LiveFrontier
nsFrontier = live-frontier navierStokes
  "critical-cone / physical high-frequency regularity consumer"
  "cutoff-uniform signed physical transfer/production -> spacetime or potential-budget payment"
  "May enstrophy/vorticity tower; Abel/telescope/Gram/resolvent/critical-cone transports"
  "dashiCFD truth/theta; signed commutator; spectator resolvent; packet/danger"
  "do not destroy sign/coherence before payment"
  "search pre-round and sibling-repo aliases for signed transfer + dissipation/potential comparison in correct order"

yangMillsFrontier : LiveFrontier
yangMillsFrontier = live-frontier yangMills
  "same reconstructed continuum family: quantitative connected-correlation decay -> positive physical spectral gap"
  "quantitative continuum clustering on SAME Schwinger family; separately identify candidate decay rate with physical spectrum"
  "May gap boundary; OS reconstruction; clustering-to-gap; dense-core; lattice-to-physical exponent transport"
  "May Balaban RG; coercivity/reflection positivity; CMP109/CMP116 influence; Langevin/Dyson; cluster expansion; polymer norm"
  "finite/RG decay or generic Clustered is not same-family continuum clustering"
  "search May-August history by direct correlation/transfer-semigroup output before paying Row-C again"

rhFrontier : LiveFrontier
rhFrontier = live-frontier riemannHypothesis
  "forall high off-line zero: contradiction on actual universal pole-quotient response"
  "uniform strict bound on literal reflection-paired oscillatory response; executable route: proof-bearing one-sided finite-cell uppers"
  "near/far monotonicity; certificate fold; Off/Gamma; high contradiction; high/low compiler"
  "February AbelZeta; April phase diagnostics; July Weil; August Hermitian; direct phase; certified interval; IBP/Taylor/quadrature"
  "ancestry/status/absolute envelopes do not pay final same-object strict response"
  "search February-August aliases for signed/phase-sensitive bounds landing or transporting exactly to cellResponse/nearResponse"

grQuantumFrontier : LiveFrontier
grQuantumFrontier = live-frontier grQuantum
  "one common physical metric/action language whose QFT and Einstein variations yield SAME stress-energy source"
  "instantiate same-action/same-stress on literal sectors; then anomaly-free dynamics + renormalized continuum amplitudes + semiclassical GR/backreaction"
  "May stress-energy target; endpoint sector variation; native-stress transport; common metric; pairing commutation; SameStressEnergyWeld"
  "old Noether/action/stress; YM; Maxwell/scalar/spinor/Higgs; Einstein-Hilbert variation/separation"
  "shared names or flat compatibility do not prove same action/metric/stress or quantum gravity"
  "search May-August variational/Noether/stress ancestry for literal sector inhabitants before broad QG search"

canonicalLiveFrontiers : List LiveFrontier
canonicalLiveFrontiers = nsFrontier ∷ yangMillsFrontier ∷ rhFrontier ∷ grQuantumFrontier ∷ []

record ArchaeologyDiscipline : Set where
  constructor archaeology-discipline
  field
    consumerFirst roundNumbersAreOnlyOneIndex searchSemanticAliases
      searchSiblingRepositories distinguishHistoricalClocks
      earliestConfirmedDateIsOnlyLowerBound compilerDoesNotCreateAnalyticContent
      producerTacticIsNotMandatoryRoute sameObjectBeforePromotion
      negativeResultsPruneRoutes datesRemainProvenanceNotProof : Bool

canonicalArchaeologyDiscipline : ArchaeologyDiscipline
canonicalArchaeologyDiscipline = archaeology-discipline
  true true true true true true true true true true true

record ProofCatalystDashboard : Set where
  constructor proof-catalyst-dashboard
  field nsTarget ymTarget rhTarget grQuantumTarget historicalWarning : String

canonicalProofCatalystDashboard : ProofCatalystDashboard
canonicalProofCatalystDashboard = proof-catalyst-dashboard
  "NS: signed physical transfer -> uniform spacetime/potential payment"
  "YM: continuum physical Schwinger family -> quantitative clustering -> physical spectrum"
  "RH: literal oscillatory zero response -> uniform strict high margin"
  "GR/QFT: literal sector + Einstein variations -> same action/metric/stress weld -> anomaly/UV/semiclassical QG recovery"
  "Current lower bounds: RH Feb 23; GR stress May 12; YM Balaban/RG May 17; NS typed wall May 29 with June dashiCFD ancestry. July is consolidation, not origin. Keep searching backward by output shape and prove same-object transport before reuse."
