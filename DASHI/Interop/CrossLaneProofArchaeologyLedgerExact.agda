module DASHI.Interop.CrossLaneProofArchaeologyLedgerExact where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.String using (String)
open import Agda.Builtin.List using (List; []; _∷_)

------------------------------------------------------------------------
-- CROSS-LANE PROOF ARCHAEOLOGY LEDGER
--
-- Canonical grep-first owner for CURRENT proof search.
-- Active archaeology focus: Yang-Mills + Riemann Hypothesis.
-- NS / GR-QFT remain as continuity coordinates only.
--
-- Search handles:
-- archaeology chronology snowball attribution primary DOI QID Dewey OEIS
-- date commit same-object source consumer producer compiler Clay
-- YM Yang-Mills Jaffe Witten Balaban CMP98 CMP109 CMP116 CMP119 CMP122
-- Round87 Round89 Round95 Round100 Round236 Round259 Round260 Eq119
-- operator domain Kato Mosco Osterwalder Schrader Heat Doob clustering
-- RH Riemann Weil Aristotle pole quotient nearResponse finiteNearSum
-- reflection parity modulation certificate ClusterResponse Bishop
--
-- RULES
-- * dates below are first-confirmed repository clocks, never origin claims;
-- * acquisition order may differ from theorem-payment order;
-- * primary source / DOI / QID / Dewey / OEIS / commit are distinct coordinates;
-- * source identity and source authority do not manufacture theorem payment;
-- * old objects are reused only after same-object transport;
-- * typed theorem state outranks commit-message optimism;
-- * promisingly compressed frontier != Clay-paid theorem.
------------------------------------------------------------------------

data Lane : Set where
  navierStokes yangMills riemannHypothesis grQuantum : Lane

data HistoricalRole : Set where
  terminalConsumer directProducer producerTactic compiler representationWeld
  negativeControl diagnostic crossProverDonor sourceFrontier
  operatorContinuumFrontier liveLevel2Theorem : HistoricalRole

data HistoricalClock : Set where
  constructionAncestry firstTypedAppearance formalConsolidation
  consumerRecovery cutsetCompression sourceFrontierCompression
  crossProverSync operatorContinuumAudit : HistoricalClock

data IdentityStatus : Set where
  sameObjectProved structuralAncestor candidateAlias notSameObject unresolvedIdentity : IdentityStatus

data PaymentStatus : Set where
  paid conditionalPayment unpaid notApplicable : PaymentStatus

data IdentifierStatus : Set where
  verifiedIdentifier unresolvedIdentifier notApplicableIdentifier : IdentifierStatus

------------------------------------------------------------------------
-- CURRENT COMPLETION ROUTER
------------------------------------------------------------------------

record ClayLaneRouter : Set where
  constructor clay-lane-router
  field
    lane : Lane
    mission : String
    wholeProblemCutset : String
    hottestSourceFacingLeaf : String
    alreadyOwned : String
    nextSameObjectTest : String
    firewall : String

open ClayLaneRouter public

ymRouter : ClayLaneRouter
ymRouter = clay-lane-router yangMills
  "Finish the Jaffe-Witten existence + mass-gap problem on one literal compact-simple continuum construction."
  "Frozen Round87-89 research cutset = four physical rows A/B/C/D. A: positive+tuned literal beta trajectory. B: differentiated marked-source locality/composite-stress geometric shell energy. C: same-density compact-Lie Heat/Doob + influence -> mass gap/clustering. D: same-family short-distance OPE/stress/asymptotic-freedom identification."
  "Do not search by one stale round number. Cross-row source frontier R236 chooses literal CMP122 effective-density semantics first; Row-C R259/R260 isolates same-density Heat/Doob, CMP116 comparison+anchor, generator/Hessian identity, relaxation, finite speed and geometric envelope. The operator/continuum owner separately exposes physical domain/core/self-adjointness, Eq119 source instantiation, vacuum recovery, OS reconstruction and finite-to-continuum construction."
  "Round95-100 compilers remove many false analytic debts: beta response algebra, CMP116 geometric-shell summation, curvature/Hessian and generator-row propagation, dense-core spectral exclusion, bounded strong-limit form-gap transport, generator uniqueness and several Eq119 finite/representation compilers."
  "Prefer literal source/repository instantiation over reproving generic analysis: CMP122 density -> CMP119 regular-E -> CMP116 localization/radius/marked Hessian; for Row C identify the actual Heat/Doob derivative generator with that same marked Hessian carrier. In the operator lane construct the genuine partial-domain/self-adjoint physical Hamiltonian and OS continuum carrier rather than treating total-map Lean theorems as that construction."
  "Four-row compression is a research router, not a solution. Lean generic theorems are donors, not Agda proofs and not physical YM producers. Marginal g-history is never assigned fake exponential forgetting."

rhRouter : ClayLaneRouter
rhRouter = clay-lane-router riemannHypothesis
  "Exclude every high off-line zero on the actual universal pole-quotient response, then combine with the independent low/critical bridge."
  "Preferred direct high route = one evaluator-independent representation seam plus one primitive strict high scalar family. Representation: nearResponseAt(chosen J) = finiteNearSum(cellResponse). Analytic family: certified/direct literal complement < actual ClusterResponse."
  "Literal-kernel source identities: checked near-off finset, zeta multiplicity, off-line horizontal displacement, final universal pole taper, reflection-pair odd-channel cancellation, and target-relative modulation/phase realization."
  "FinalNearIndexedFiniteProducer makes signedNearValue=finalNear definitional; FinalCarrierFiniteSumCertificate and CertifiedNearUpperClusterResponseCompiler transport a genuine upper once the literal kernel exists. Bishop four-corner/expression interval and sine/cosine machinery are reusable certificate producers. Lean/Aristotle already machine-checks reflection-pair odd cancellation and finite Schur/parity routes, but those proofs are not transported into Agda."
  "First close the literal same-object representation using existing window/Weil/Aristotle source identities where possible; then produce the strict aggregate high margin. Do not revive an obsolete absolute-W(t) majorant route merely because its finite Schur algebra is strong."
  "A finite certificate, a Lean theorem, or a representation refinement alone is not RH. Current direct owners keep RH derived=false."

nsContinuityRouter : ClayLaneRouter
nsContinuityRouter = clay-lane-router navierStokes
  "Continuity only: NS active archaeology delegated elsewhere."
  "Current live signed/direct-companion spacetime payment remains external to this YM/RH pass."
  "See dedicated NS forensic owners/PRs."
  "Historical signed/coherence, Galerkin and downstream continuation architecture retained elsewhere."
  "No new NS archaeology performed here."
  "Do not infer NS completion from this ledger."

grContinuityRouter : ClayLaneRouter
grContinuityRouter = clay-lane-router grQuantum
  "Non-Clay continuity coordinate."
  "Same-action/metric/stress carrier then anomaly/UV/semiclassical recovery."
  "Literal-sector variation inhabitants."
  "Common-action/common-stress weld already represented."
  "Reuse same-object variational patterns where helpful."
  "Do not confuse GR/QFT compatibility with Clay YM completion."

canonicalRouters : List ClayLaneRouter
canonicalRouters = ymRouter ∷ rhRouter ∷ nsContinuityRouter ∷ grContinuityRouter ∷ []

------------------------------------------------------------------------
-- MULTIPLE CLOCKS: RESEARCH CUTSET != SOURCE FRONTIER != OPERATOR FRONTIER
------------------------------------------------------------------------

record DatedAnchor : Set where
  constructor dated-anchor
  field
    anchorLane : Lane
    dateBrisbane : String
    commit : String
    owner : String
    object : String
    clock : HistoricalClock
    role : HistoricalRole
    identity : IdentityStatus
    payment : PaymentStatus
    interpretation : String

open DatedAnchor public

anchors : List DatedAnchor
anchors =
  dated-anchor yangMills "2026-05-17"
    "81fc16c11af4f4152410ea9ce9269c68cc223387"
    "BalabanRGMassGapReceiptSurface.agda"
    "finite-depth positive gaps != one cutoff/depth-uniform positive gap"
    firstTypedAppearance terminalConsumer structuralAncestor unpaid
    "The modern uniformity debt was already explicit in May; later routes are attempted payments, not its origin."
  ∷ dated-anchor yangMills "2026-07-20"
    "3933eaa7618e1565580a5ac67aed875dbd850d3f + 16e0a24d5766e93fb9cfee921dc9449dda36426e"
    "uniform cutoff-gap / contraction family"
    "uniform finite-cutoff gap-survival attempted producer"
    formalConsolidation producerTactic structuralAncestor conditionalPayment
    "Strong old route; not automatically the same continuum Schwinger-family construction."
  ∷ dated-anchor yangMills "2026-08-20"
    "f09e953f79933701d59f186629e4ac30e0d0bd3a -> e0038fa05311fdf37462945c9a651bf45c4f16c9"
    "BalabanClayHighestAlphaRound84SixAnalyticLemmaExact.agda"
    "six hard physical lemma-family decomposition"
    cutsetCompression terminalConsumer sameObjectProved unpaid
    "Important historical compression, but superseded as the top research router by the frozen four-row Round87-89 cutset."
  ∷ dated-anchor yangMills "2026-08 (Round87-89)"
    "repository owner BalabanClayHighestAlphaRound87FourAnalyticLemmaExact.agda"
    "BalabanClayHighestAlphaRound87FourAnalyticLemmaExact.agda"
    "shortest literal Jaffe-Witten research cutset frozen at four rows A/B/C/D"
    cutsetCompression terminalConsumer sameObjectProved unpaid
    "Research count decreases only when a whole physical completion row is inhabited or proved from another row."
  ∷ dated-anchor yangMills "2026-09-06 22:57-23:31"
    "0efb7ebcd57863b03f5d675705f5f5d5859465a2 -> c13782014739bbde3f769c9bfef5074e69c687f3"
    "YMOperatorDomainContinuumFrontier2026Exact.agda"
    "operator/domain/continuum trust-boundary audit; Eq119 source cut and Lean/Agda functional-analysis separation"
    operatorContinuumAudit operatorContinuumFrontier sameObjectProved unpaid
    "Separate clock from round-based source fronts. Generic operator/gap compilers are closed, while physical unbounded domain/core, Eq119 source producer, vacuum recovery, OS reconstruction and finite-to-continuum construction remain open."
  ∷ dated-anchor yangMills "2026-09-09 19:10:54"
    "1e7e66e03551aa97718a70d0845f9018a6dc0e60"
    "BalabanPreferredSourceFrontierRound236Exact.agda"
    "dependency-accurate cross-row physical source frontier"
    sourceFrontierCompression sourceFrontier sameObjectProved unpaid
    "Preferred independent first root is literal CMP122 effective-density semantics; regular-E continuation and regular-E->BC1 are already compiler outputs."
  ∷ dated-anchor yangMills "2026-09-09 23:54 -> 2026-09-10 00:51"
    "03c53b64c7b4732a18db5cdd0203b6eb23790de7 -> d6c31a7df3f4ad1e42663fd02023b996da07a2e1"
    "BalabanPreferredRowCFrontierRound259Exact.agda + R260 anchored Hessian"
    "least-privilege Row-C frontier; comparison majorant + reference anchor replace false absolute promotion"
    sourceFrontierCompression liveLevel2Theorem sameObjectProved unpaid
    "Row C now separates same-density Heat realization, marked comparison, anchor, covariance/gradient map, generator/Hessian identity, relaxation, finite speed and geometric envelope."
  ∷ dated-anchor riemannHypothesis "2026-02-23"
    "8bf9e75a159e90c837836a998a43f55680ae66a9"
    "AbelZeta.agda"
    "Abel/contraction zeta analytic technology"
    constructionAncestry diagnostic structuralAncestor notApplicable
    "Analytic ancestry only; not the later pole-response proof."
  ∷ dated-anchor riemannHypothesis "2026-07-19"
    "78bdf33b725596bd0c1bc399a3e5bb78cc9bb14c"
    "RH/Weil programme PR #100"
    "first currently pinned explicit RH proof programme"
    formalConsolidation producerTactic structuralAncestor unpaid
    "First explicit RH programme clock currently pinned by this audit."
  ∷ dated-anchor riemannHypothesis "2026-08-29 13:26 -> 21:06"
    "7979a68d5e5fa230f51ef3709150af0f152e6cb2 -> d5882c70ca02383bc3f39cd49e87ba4468972372"
    "RiemannAristotleWindowSchurCrossProverSyncExact.agda"
    "Lean/Aristotle parity, reflection cancellation and two-zero/three-taper Schur admission"
    crossProverSync crossProverDonor candidateAlias conditionalPayment
    "Machine checked in Lean owner but not transported into Agda. Absolute W(t) majorization is recorded as exhausted; projected far tail remains open in that route."
  ∷ dated-anchor riemannHypothesis "2026-09-08 06:27 -> 07:26"
    "5b60001ba628ef221bcb25a9ad28fa2b7e0ee411 -> 49c680f710cfeb769a6ebcbd3789b7a919bf36b9"
    "RiemannG2FinalPoleNearObserverRefinementExact.agda"
    "final observer refined from scalar/count-envelope to proof-relevant target-relative phase and gap equality"
    consumerRecovery representationWeld sameObjectProved unpaid
    "The next representation subleaf is analytic realization of target translation/modulation on the same universal pole-quotient carrier; a full Weil target-window is stronger than necessary."
  ∷ dated-anchor riemannHypothesis "2026-09-09 22:07:03"
    "a25681a6cf7e8bdc0739b90a1592530cb64bb256"
    "RiemannG2FinalNearLiteralKernelExact.agda"
    "evaluator-independent final literal near kernel; one decisive equality nearResponseAt(J)=finiteNearSum(cellResponse)"
    consumerRecovery liveLevel2Theorem sameObjectProved unpaid
    "Canonical direct representation seam. Certificate evaluation is downstream rather than prerequisite."
  ∷ []

------------------------------------------------------------------------
-- SOURCE / ATTRIBUTION / CLASSIFICATION SNOWBALL
------------------------------------------------------------------------

record SourceCoordinate : Set where
  constructor source-coordinate
  field
    sourceLane : Lane
    authors : String
    title : String
    primaryIdentity : String
    doi : String
    doiStatus : IdentifierStatus
    qid : String
    qidStatus : IdentifierStatus
    dewey : String
    deweyStatus : IdentifierStatus
    oeis : String
    oeisStatus : IdentifierStatus
    repoUse : String
    paymentBoundary : String

open SourceCoordinate public

sources : List SourceCoordinate
sources =
  source-coordinate yangMills
    "Arthur Jaffe; Edward Witten"
    "Quantum Yang-Mills Theory"
    "official Clay Mathematics Institute problem description / The Millennium Prize Problems"
    "not assigned" notApplicableIdentifier
    "Arthur Jaffe Q370094; Edward Witten Q201513" verifiedIdentifier
    "unresolved; do not infer a Dewey number from subject labels" unresolvedIdentifier
    "not applicable" notApplicableIdentifier
    "Terminal problem authority for the four-row completion contract."
    "Problem statement defines the target; it does not supply a DASHI analytic producer."
  ∷ source-coordinate yangMills
    "Tadeusz Balaban"
    "Renormalization Group Approach to Lattice Gauge Field Theories I"
    "Communications in Mathematical Physics 109 (1987), 249-301"
    "10.1007/BF01215223" verifiedIdentifier
    "person QID unresolved in repo atlas" unresolvedIdentifier
    "unresolved" unresolvedIdentifier
    "not applicable" notApplicableIdentifier
    "CMP109 Ward/colour and differentiated beta/Hessian source coordinates."
    "Source-owned formula/reduction != literal physical source instantiation."
  ∷ source-coordinate yangMills
    "Tadeusz Balaban"
    "Renormalization Group Approach to Lattice Gauge Field Theories II. Cluster Expansions"
    "Communications in Mathematical Physics 116 (1988), 1-22"
    "10.1007/BF01239022" verifiedIdentifier
    "person QID unresolved in repo atlas" unresolvedIdentifier
    "unresolved" unresolvedIdentifier
    "not applicable" notApplicableIdentifier
    "CMP116 localized activities, differentiated localization and marked-coordinate source layer."
    "Published localization must still be identified with the literal beta/Hessian/composite/stress marks used by the current construction."
  ∷ source-coordinate yangMills
    "Tadeusz Balaban"
    "Convergent Renormalization Expansions for Lattice Gauge Theories"
    "Communications in Mathematical Physics 119 (1988), 243-285"
    "10.1007/BF01217741" verifiedIdentifier
    "person QID unresolved in repo atlas" unresolvedIdentifier
    "unresolved" unresolvedIdentifier
    "not applicable" notApplicableIdentifier
    "R236/R221 regular-E source projection and normalized local expectation semantics."
    "CMP119 bibliographic identity does not prove that DASHI's source density is the same regular-E object; that weld is conclusion-paying."
  ∷ source-coordinate yangMills
    "Tadeusz Balaban"
    "Large Field Renormalization I: The Basic Step of the R-Operation"
    "Communications in Mathematical Physics 122 (1989), 175-202"
    "10.1007/BF01257412" verifiedIdentifier
    "person QID unresolved in repo atlas" unresolvedIdentifier
    "unresolved" unresolvedIdentifier
    "not applicable" notApplicableIdentifier
    "One CMP122 large-field source family used by current density/source archaeology."
    "Do not identify this automatically with every CMP122 effective-density leaf; exact part/section mapping remains source-local."
  ∷ source-coordinate yangMills
    "Tadeusz Balaban"
    "Large Field Renormalization II: Localization, Exponentiation, and Bounds for the R Operation"
    "Communications in Mathematical Physics 122 (1989), 355-392"
    "10.1007/BF01238433" verifiedIdentifier
    "person QID unresolved in repo atlas" unresolvedIdentifier
    "unresolved" unresolvedIdentifier
    "not applicable" notApplicableIdentifier
    "Boundary reinjection/raw-state/complete-density source owners explicitly cite this object."
    "Acquisition may precede exact section-to-leaf payment; preserve that dependency."
  ∷ source-coordinate yangMills
    "Tosio Kato"
    "Perturbation Theory for Linear Operators"
    "Springer; operator/domain/form calibration source"
    "10.1007/978-3-642-66282-9" verifiedIdentifier
    "Q1335673" verifiedIdentifier
    "unresolved in this audit" unresolvedIdentifier
    "not applicable" notApplicableIdentifier
    "Calibrates genuine closed/unbounded operator domains and forms in YMOperatorDomainContinuumFrontier2026Exact."
    "Kato theory does not prove the selected Yang-Mills Hamiltonian satisfies the required hypotheses."
  ∷ source-coordinate yangMills
    "Umberto Mosco"
    "Convergence of Convex Sets and of Solutions of Variational Inequalities"
    "Advances in Mathematics 3 (1969), 510-585"
    "10.1016/0001-8708(69)90009-7" verifiedIdentifier
    "unresolved" unresolvedIdentifier
    "unresolved" unresolvedIdentifier
    "not applicable" notApplicableIdentifier
    "Calibration for form/Mosco recovery and gap transport."
    "Generic recovery compiler != physical vacuum-orthogonal YM recovery system."
  ∷ source-coordinate yangMills
    "Konrad Osterwalder; Robert Schrader"
    "Axioms for Euclidean Green's Functions I / II"
    "Communications in Mathematical Physics 31 (1973), 83-112; 42 (1975), 281-305"
    "10.1007/BF01645738; 10.1007/BF01608978" verifiedIdentifier
    "unresolved here" unresolvedIdentifier
    "unresolved" unresolvedIdentifier
    "not applicable" notApplicableIdentifier
    "Defines the Euclidean reconstruction/continuum target used by the YM operator frontier."
    "OS reconstruction theorems do not supply the finite-to-continuum Yang-Mills construction or identify its physical Hamiltonian automatically."
  ∷ source-coordinate riemannHypothesis
    "Bernhard Riemann"
    "Ueber die Anzahl der Primzahlen unter einer gegebenen Groesse"
    "1859 memoir; source-family identity retained by RH source owners"
    "not assigned" notApplicableIdentifier
    "Q42299; Riemann hypothesis Q205966" verifiedIdentifier
    "unresolved" unresolvedIdentifier
    "not applicable" notApplicableIdentifier
    "Historical zeta/RH source context."
    "Historical identity does not pay the modern pole-response kernel or strict high margin."
  ∷ source-coordinate riemannHypothesis
    "Errett Bishop; Douglas Bridges; Marc Daumas; David Lester; Cesar Munoz"
    "constructive analysis and verified interval-arithmetic donor family"
    "existing repo arithmetic owners"
    "10.1007/978-3-642-61667-9; 10.1109/TC.2008.213" verifiedIdentifier
    "not required for RH theorem identity" notApplicableIdentifier
    "unresolved" unresolvedIdentifier
    "not applicable" notApplicableIdentifier
    "Proof-producing interval arithmetic for reflection-paired cosine-cell enclosures."
    "Arithmetic soundness cannot manufacture the literal-kernel same-object equality or the strict ClusterResponse margin."
  ∷ []

------------------------------------------------------------------------
-- CROSS-PROVER DONORS: THEOREM-BEARING, BUT OWNERSHIP MATTERS
------------------------------------------------------------------------

record CrossProverDonor : Set where
  constructor cross-prover-donor
  field
    donorLane : Lane
    projectPath : String
    theorem : String
    ownerProver : String
    machineChecked : Bool
    transportedIntoAgda : Bool
    reusableFor : String
    notEnoughFor : String

open CrossProverDonor public

crossProverDonors : List CrossProverDonor
crossProverDonors =
  cross-prover-donor yangMills
    "RequestProject/YangMills/GeneratorUniquenessCore.lean"
    "generator_unique_of_evolution_eq / generator_clm_unique"
    "Lean / Aristotle" true false
    "same-evolution generator uniqueness on common core / continuous-linear-map dense-core equality"
    "formal partial-domain unbounded Hamiltonian, self-adjoint physical YM form"
  ∷ cross-prover-donor yangMills
    "RequestProject/YangMills/GaugeInvariantL2Carrier.lean"
    "hamiltonian_eqOn_core_of_same_evolution / hamiltonian_unique_of_same_evolution_on_dense_core"
    "Lean / Aristotle" true false
    "gauge-invariant L2 carrier and same-evolution uniqueness"
    "physical domain D(H), domain invariance, self-adjoint selected YM Hamiltonian"
  ∷ cross-prover-donor yangMills
    "RequestProject/YangMills/MassGapFormTransport.lean"
    "hasFormGap_of_tendsto / hasFormGap_of_tendsto_of_gap_tendsto"
    "Lean / Aristotle" true false
    "bounded strong-limit quadratic-form gap transport"
    "unbounded form/resolvent/Mosco physical continuum theorem"
  ∷ cross-prover-donor riemannHypothesis
    "separate Lean-4.33 Aristotle Zeta/Weil project"
    "reflection partner cancels target odd channel"
    "Lean / Aristotle" true false
    "one source identity needed by FinalNearLiteralKernel; parity-aware cancellation architecture"
    "Agda literal-kernel inhabitant, final finite-sum equality, strict high margin"
  ∷ cross-prover-donor riemannHypothesis
    "separate Lean-4.33 Aristotle Zeta/Weil project"
    "LiteralWeilThreeWindowNarrowInstance.exists_taper_triple_two_zero_admission"
    "Lean / Aristotle" true false
    "finite selected nuisance-zero elimination before tail majorization"
    "projected unselected far-tail budget or current direct pole-response theorem"
  ∷ []

------------------------------------------------------------------------
-- CURRENT FAIL-CLOSED CUTS
------------------------------------------------------------------------

record CurrentCut : Set where
  constructor current-cut
  field
    cutLane : Lane
    authoritativeView : String
    openPhysicalLeaves : String
    downstreamOwned : String
    nextInvestigation : String
    clayPaid : Bool

open CurrentCut public

currentCuts : List CurrentCut
currentCuts =
  current-cut yangMills
    "Use the frozen four research rows for whole-problem accounting; R236/R259/R260 for least-privilege source work; YMOperatorDomainContinuumFrontier2026Exact for operator/continuum trust boundaries. These are concurrent clocks, not one linear round sequence."
    "R236: literal CMP122 density, CMP119 regular-E projection, CMP116 radius/localization, source Hessian/beta/first-variation identities. R259: eight same-density Row-C leaves. Operator frontier: physical Eq119 package; partial-domain/common-core/self-adjoint Hamiltonian; physical clustering/continuity; vacuum recovery; OS evolution identification; finite-to-continuum and OS/Wightman package."
    "Many finite algebra, geometric summation, Dyson-power, dense-core spectral-exclusion, bounded form-gap transport, generator uniqueness, R184/R187/R189 Eq119 representation compilers."
    "Highest alpha: recover exact source identities that simultaneously pay R236 and operator-frontier leaves. In particular map CMP122 effective density -> CMP119 regular-E -> CMP116 marked Hessian/source coordinates; then test whether the same object supplies Row-C Heat/Doob generator and operator-domain continuum form."
    false
  ∷ current-cut riemannHypothesis
    "Direct route: evaluator-independent literal kernel/equality, then one strict high scalar family. Historical Lean Schur route remains a donor/negative control, not the canonical direct proof."
    "Agda source receipts for checked near finset, multiplicity, horizontal displacement, pole taper, reflection parity, target-relative modulation; decisive finalNear=finiteSum equality; then uniform strict complement<ClusterResponse."
    "Lean owns reflection cancellation and selected finite Schur elimination; Agda owns certificate transport, direct complement compiler, and generic Bishop/Taylor arithmetic."
    "Search semantic aliases for target translation/modulation and exact near-zero decomposition before proving anything new. If an older Weil/window owner supplies those identities on the same universal pole quotient, adapt it thinly into FinalNearLiteralKernel; otherwise the representation theorem is genuinely new."
    false
  ∷ []

------------------------------------------------------------------------
-- METADATA / STATUS FIREWALLS
------------------------------------------------------------------------

record ArchaeologyDiscipline : Set where
  constructor archaeology-discipline
  field
    consumerFirst : Bool
    semanticAliasSearch : Bool
    siblingArchiveSearch : Bool
    datesAreLowerBounds : Bool
    acquisitionNotPayment : Bool
    sameObjectBeforePromotion : Bool
    compilerNotProducer : Bool
    crossProverOwnershipMatters : Bool
    qidNotProof : Bool
    doiNotProof : Bool
    deweyNotProof : Bool
    oeisNotProof : Bool
    attributionNotAuthority : Bool
    compressedNotClayPaid : Bool

canonicalDiscipline : ArchaeologyDiscipline
canonicalDiscipline = archaeology-discipline
  true true true true true true true true true true true true true true

------------------------------------------------------------------------
-- GREP-FIRST DASHBOARD
------------------------------------------------------------------------

record ProofCatalystDashboard : Set where
  constructor dashboard
  field ym rh ns gr warning : String

canonicalDashboard : ProofCatalystDashboard
canonicalDashboard = dashboard
  "YM: whole problem = frozen four rows A/B/C/D. Source attack = R236 plus R259/R260. Separate Sep-06 operator/continuum audit shows generic Lean/Agda compilers are strong but physical partial-domain Hamiltonian, Eq119 source package, recovery/OS/finite->continuum construction remain open. Highest-alpha route is shared literal source identity across those views, not another generic compiler."
  "RH: Aug-29 Lean/Aristotle already owns parity/reflection/finite-Schur donors; Sep-08 observer refinement made target-relative phase proof-relevant; Sep-09 a25681a6 made the final literal kernel evaluator-independent. Current direct debt = exact nearResponseAt(J)=finiteNearSum(cellResponse) on source-paid coordinates + one uniform strict complement<ClusterResponse family."
  "NS retained for continuity only; active archaeology delegated."
  "GR/QFT retained as non-Clay same-object donor context only."
  "Primary/DOI/QID/Dewey/OEIS/date/commit are evidence coordinates, not theorem payment. Unresolved is preferable to invented metadata. Search by theorem output shape and prove same-object transport before decrementing any Clay cutset."
