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
-- Dated chronology. Dates are Brisbane-local calendar dates recovered from
-- repository commit/PR timestamps.  Where the exact day is not yet pinned in
-- this ledger, use an interval/window owner below rather than inventing one.
------------------------------------------------------------------------

canonicalDatedArchaeology : List DatedArchaeologyEntry
canonicalDatedArchaeology =

  -- RH: broad Weil/explicit-formula architecture appears first.
  dated-entry riemannHypothesis "2026-07-19" exactCommitDate
    "commit 78bdf33b725596bd0c1bc399a3e5bb78cc9bb14c / PR #100"
    "Riemann zeta + DASHI-Weil explicit-formula theorem ladder"
    compiler
    "Broad terminal/transport architecture; not yet the later literal pole-quotient high producer."
  ∷

  -- GR/QG: detailed terminal cutset predates the later common-action weld.
  dated-entry grQuantum "2026-07-20" pullRequestDate
    "PR #246"
    "deep GR/quantum research authority cutset"
    terminalConsumer
    "Strong promotion checklist: continuum geometry, anomaly freedom, renormalized amplitudes, low-energy recovery and empirical correspondence. Useful as a terminal gate, too broad as the first proof-search target."
  ∷

  -- YM: the honest Clay endpoint already exposes clustering as real debt.
  dated-entry yangMills "2026-07-21" pullRequestDate
    "PR #309"
    "source-faithful Balaban matching + unconditional YM solution gate"
    terminalConsumer
    "Uniform positive clustering and a physical Hamiltonian mass gap are explicit unresolved obligations from the early honest endpoint."
  ∷

  dated-entry yangMills "2026-07-29" exactCommitDate
    "commit c4910cdcde12c764c818545fb658bb93171c471b"
    "BalabanClayT5ClusteringToTransferGapExact"
    compiler
    "The modern clustering-to-gap consumer already existed: quantitative clustering plus spectral interpretation excludes positive subgap modes."
  ∷

  dated-entry yangMills "2026-08-05" repositorySequence
    "commits f6759d1f4bf5ac94da33906717147ce33eafe363 and 4f5fc7e4d941d324534b543c1103129432106943"
    "lattice-to-physical clustering exponent transport + dense-core clustering-to-gap route"
    compiler
    "Downstream spectral conversion was mature early; this strengthens the diagnosis that the missing mathematics is upstream quantitative physical clustering."
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
    "Major unification pivot: target one physical same-object theorem delta S[h] = <T,h> on one common metric language rather than a monolithic quantum-gravity object."
  ∷

  dated-entry yangMills "2026-08-31" exactCommitDate
    "commit 0ab210dfa75c584699decb64869eb2fa1d293ae3 / Round146"
    "literal CMP98 Eq.(119) one-step derivative"
    sourceTranscriptionDebt
    "Beginning of the literal Eq119 archaeology: represent the source operator exactly, then discharge same-object lattice/background semantics rather than inventing another qPrime socket."
  ∷

  dated-entry riemannHypothesis "2026-08-31" pullRequestDate
    "PR #677"
    "H_X -> H_A -> H_M -> H_T -> H_W -> H_E phase/modulation chain"
    supersededOverpayment
    "Historically useful decomposition. Later least-privilege work showed several of these layers were producer/representation structure rather than primitive terminal obligations."
  ∷

  dated-entry riemannHypothesis "2026-09-10" pullRequestDate
    "PR #855"
    "generic high contradiction with direct-phase and certified-upper producers"
    terminalConsumer
    "The high-side consumer becomes implementation-neutral; direct analytic and proof-carrying numerical routes compile to the same high contradiction."
  ∷

  dated-entry yangMills "2026-09-10" pullRequestDate
    "PR #869"
    "canonical mass-gap search normalized to quantitative clustering consumer"
    terminalConsumer
    "Heat/Doob/Langevin/Dyson, unified polymer norms and source-native cluster expansion are demoted to optional producer tactics. This recovers the July clustering consumer rather than inventing a new route."
  ∷ []

------------------------------------------------------------------------
-- Buried-donor windows.  These are the periods to search backwards by output
-- signature rather than by round number or current module name.
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
  donor-window yangMills "2026-07-29" "2026-08-20"
    "actual two-point connected-correlation inequality on the same continuum/OS Schwinger family"
    "Dense clustering, decoupling, H-KP/H-LOC, compactness and spectral-conversion work accumulated here before later Row-C machinery obscured the original consumer."
  ∷ donor-window riemannHypothesis "2026-08-21" "2026-08-31"
    "sharp signed or one-sided upper on the target-centred reflection-paired oscillatory response"
    "Hermitian/interference, retained-pair, Poisson and pole-quotient lines overlap here; search semantic aliases rather than G2/Round names."
  ∷ donor-window grQuantum "2026-07-20" "2026-08-30"
    "same action variation / metric perturbation / stress-energy identity across literal theory sectors"
    "The broad terminal cutset predates the sharper common-action weld; older variational, Noether, stress and metric owners may already pay parts of the later same-object theorem."
  ∷ donor-window navierStokes "historical NS audit" "current"
    "signed physical production/transfer retained before absolute value, then uniform spacetime/potential payment"
    "NS is the methodological reference case: search aliases and older sibling-repo constructions, not round labels alone."
  ∷ []

------------------------------------------------------------------------
-- Canonical proof-search targets.  A live frontier states the first theorem
-- that must manufacture new analytic/physical information for the selected
-- downstream consumer.  Tactics and compilers are deliberately separate.
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
  "Abel/telescope/Gram/resolvent/critical-cone transports already downstream where their inputs are available"
  "signed commutator, spectator resolvent, packet/danger, CFD signed-transfer and theta-barrier families"
  "do not take absolute values or quotient away sign/coherence before the physical consumer is paid"
  "search old NS and dashiCFD aliases for signed transfer + dissipation/potential comparison composed in the correct order"

yangMillsFrontier : LiveFrontier
yangMillsFrontier = live-frontier yangMills
  "same reconstructed continuum family with quantitative connected-correlation decay and positive physical spectral gap"
  "quantitative continuum clustering on the same physical Schwinger family; independently, identify the positive candidate decay rate with the physical spectrum"
  "clustering-to-transfer-gap, OS reconstruction, dense-core and lattice-to-physical exponent transports"
  "CMP109/CMP116 Hessian influence -> weighted row -> Langevin/Dyson; Balaban cluster expansion; unified polymer/Schwinger norm; direct source-native correlation route"
  "finite/RG spatial decay, generic Clustered predicates, or unrelated continuum limits may not be silently identified with the prize-facing same-family quantitative clustering carrier"
  "search 2026-07-29..2026-08-20 owners for an already-strong direct correlation-decay theorem before paying Row-C machinery again"

rhFrontier : LiveFrontier
rhFrontier = live-frontier riemannHypothesis
  "forall high off-line zero: contradiction on the actual universal pole-quotient response"
  "uniform strict high-side bound on the literal reflection-paired oscillatory response; executable route reduces further to proof-bearing one-sided finite-cell uppers"
  "near/far monotonicity, certificate folding, Off/Gamma compilers, high contradiction and high/low terminal compilation"
  "direct phase-visible inequality; certified interval/rational upper route; integration-by-parts/Taylor/quadrature/oscillation families; historical Hermitian/interference donors"
  "the analytic payment must not see the downstream balance; determinant taper, coarse zero counts, absolute envelopes and status receipts are not the final pole-quotient theorem"
  "search 2026-08-21..2026-08-31 aliases for a bound that lands directly on the current cellResponse/nearResponse carrier"

grQuantumFrontier : LiveFrontier
grQuantumFrontier = live-frontier grQuantum
  "one common physical metric/action language whose QFT and Einstein variations yield the same stress-energy source"
  "instantiate the same-action/same-stress weld on literal sectors; after that, the true QG jump is anomaly-free quantum dynamics + renormalized continuum amplitudes + semiclassical GR/backreaction recovery"
  "endpoint-only sector variation, native-stress transport, common metric language, pairing commutation and SameStressEnergyWeld compilers"
  "YM stress recovery; Maxwell/scalar/spinor/Higgs/other sector variations; Einstein-Hilbert variation and pairing separation"
  "shared names or flat compatibility do not establish same action, same metric, same stress tensor, interaction, or quantum gravity"
  "search older variational/Noether/stress owners for cheap literal sector inhabitants of the common-action endpoint before broad QG proof search"

canonicalLiveFrontiers : List LiveFrontier
canonicalLiveFrontiers =
  nsFrontier ∷ yangMillsFrontier ∷ rhFrontier ∷ grQuantumFrontier ∷ []

------------------------------------------------------------------------
-- Cross-programme lesson recovered by archaeology.
------------------------------------------------------------------------

record ArchaeologyDiscipline : Set where
  constructor archaeology-discipline
  field
    consumerFirst : Bool
    roundNumbersAreOnlyOneIndex : Bool
    searchSemanticAliases : Bool
    compilerDoesNotCreateAnalyticContent : Bool
    producerTacticIsNotMandatoryRoute : Bool
    sameObjectBeforePromotion : Bool
    negativeResultsPruneRoutes : Bool
    datesRemainProvenanceNotProof : Bool

canonicalArchaeologyDiscipline : ArchaeologyDiscipline
canonicalArchaeologyDiscipline = archaeology-discipline
  true true true true true true true true

------------------------------------------------------------------------
-- Human-readable catalyst summary: the four highest-alpha theorem shapes.
------------------------------------------------------------------------

record ProofCatalystDashboard : Set where
  constructor proof-catalyst-dashboard
  field
    nsTarget : String
    ymTarget : String
    rhTarget : String
    grQuantumTarget : String

canonicalProofCatalystDashboard : ProofCatalystDashboard
canonicalProofCatalystDashboard = proof-catalyst-dashboard
  "NS: signed physical transfer -> uniform spacetime/potential payment"
  "YM: continuum physical measure/Schwinger family -> quantitative clustering -> physical spectrum"
  "RH: literal oscillatory zero response -> uniform strict high margin"
  "GR/QFT: literal sector + Einstein variations -> same action/metric/stress weld -> anomaly/UV/semiclassical QG recovery"
