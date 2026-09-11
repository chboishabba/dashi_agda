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
-- archaeology chronology snowball attribution primary DOI QID Dewey OEIS link
-- date commit same-object source consumer producer compiler Clay
-- YM Yang-Mills Jaffe Witten Balaban CMP98 CMP109 CMP116 CMP119 CMP122
-- CombinedRG density dictionary regular-E Round87 Round236 Round259 Round260
-- operator domain Kato Mosco Osterwalder Schrader Heat Doob clustering
-- RH Riemann Weil Aristotle pole quotient signed-off Gamma nearResponse
-- finiteNearSum reflection parity modulation cluster margin certificate Bishop
--
-- RULES
-- * dates below are first-confirmed repository clocks, never origin claims;
-- * acquisition order may differ from theorem-payment order;
-- * primary source / DOI / QID / Dewey / OEIS / link / commit are distinct;
-- * source identity and source authority do not manufacture theorem payment;
-- * old objects are reused only after same-object transport;
-- * typed theorem state outranks commit-message optimism;
-- * promisingly compressed frontier != Clay-paid theorem.
------------------------------------------------------------------------

data Lane : Set where
  navierStokes yangMills riemannHypothesis grQuantum : Lane

data HistoricalRole : Set where
  terminalConsumer directProducer producerTactic compiler representationWeld
  negativeControl diagnostic crossProverDonor sourceFrontier buriedDonor
  operatorContinuumFrontier liveLevel2Theorem : HistoricalRole

data HistoricalClock : Set where
  constructionAncestry firstTypedAppearance formalConsolidation
  consumerRecovery cutsetCompression sourceFrontierCompression
  crossProverSync operatorContinuumAudit buriedPaymentRecovery : HistoricalClock

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
  "Whole-problem accounting remains the frozen Round87-89 four-row physical cutset A/B/C/D. Source archaeology must be read on parallel clocks: the Aug-13 complete-density->CombinedRG dictionary architecture, Aug-31 ActiveSourceDiscriminator, Sep-09 R236 source recut, Sep-10 R259/R260 Row-C recut, and Sep-06 operator/continuum audit."
  "First literal source bridge: inhabit Balaban1989CompleteDensityToCombinedRGExact.CompleteDensityCombinedRGDictionary, i.e. identify Bałaban Sect.-2 source density conclusions with the existing CombinedRG trajectory's coupling, boundary and polymer-norm admissibility. Then identify the selected source regular-E/effective potential with exact BC1."
  "The transport from a completed dictionary to repository AdmissibleRGState is machine checked. CMP116/119/122 source theorems and regular-E source facts are imported. Round95-100 and the operator-return lane already own many algebraic/functional-analysis compilers: beta response, geometric summation, generator uniqueness, dense-core spectral exclusion and bounded form-gap transport."
  "Recover literal source identities, not another generic RG proof: CMP122/CMP119 density class -> CombinedRG predicates -> selected regular-E -> exact BC1; then reuse CMP116 marked localization/Hessian machinery and test the same physical object against Row-C Heat/Doob and the operator-domain continuum carrier."
  "Published finite-cutoff UV stability is not continuum YM. A source dictionary is not obtained from matching names. Lean total-map/gap theorems are donors, not the physical partial-domain/self-adjoint continuum construction."

rhRouter : ClayLaneRouter
rhRouter = clay-lane-router riemannHypothesis
  "Exclude every high off-line zero on the actual universal pole-quotient response, then combine with the independent low/critical bridge."
  "Current final-cut reconciliation has TWO live analytic leaves after source representation: literal universal-pole-quotient signed off-ordinate control and same-taper Gamma precision. Quantitative cluster-margin mathematics is already checked-Lean-owned; exact final-taper attachment is downstream. The contradiction/allowance compiler is already owned."
  "Representation prerequisite remains the evaluator-independent literal kernel: nearResponseAt(chosen J)=finiteNearSum(cellResponse), with checked near index, multiplicity, horizontal displacement, universal pole taper, reflection pairing and target-relative phase/modulation on the same carrier."
  "Lean Zeta23Bridge owns PoleQuotientClusterMargin.lean and PoleQuotientBudgetCircularity.lean, with an 8889-job aggregate reported by the Agda return. It owns a Gamma bound too, but explicitly says that bound is too coarse. Generic target-translation/modulation and certificate arithmetic are already compiled."
  "First prove/attach the literal pole-quotient representation. For genuinely new analysis, attack the target-normalized signed off-ordinate channel and same-taper Gamma precision against downstream-assigned allowances; then attach the already-owned cluster margin on the exact final taper and feed the existing strict-complement compiler."
  "Do not re-prove cluster-margin existence, rebuild the contradiction compiler, revive absolute-W(t) majorization, or import determinant-taper cancellation as if it were definitionally the final universal pole-quotient carrier. RH remains unproved."

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
  ∷ dated-anchor yangMills "2026-08-13 23:46:52"
    "87710f3cb447fd9e62d48377a4fb6d0de1ca8462"
    "Balaban1989CompleteDensityToCombinedRGExact.agda"
    "complete-density -> repository CombinedRG dictionary and transport architecture"
    buriedPaymentRecovery buriedDonor candidateAlias conditionalPayment
    "The compiler from a literal source dictionary to AdmissibleRGState was already present weeks before R236. The conclusion-paying object is the dictionary identifying source form/bounds with coupling, boundary and polymer-norm predicates; the generic transport is machine checked."
  ∷ dated-anchor yangMills "2026-08-17 17:00 (first-confirmed day)"
    "7119d36..."
    "BalabanCMP122PublishedFourDimensionalUVStabilityExact.agda"
    "published four-dimensional finite-cutoff UV-stability boundary imported with explicit continuum firewalls"
    buriedPaymentRecovery directProducer structuralAncestor conditionalPayment
    "Do not re-prove published finite-cutoff UV stability as the current leaf. It does not by itself construct continuum Schwinger functions, OS/Wightman reconstruction, non-Gaussianity or a physical mass gap."
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
  ∷ dated-anchor yangMills "2026-08-31 21:39:42"
    "c5e3a17442cb440cc9f0d052206129c6e7445234"
    "BalabanActiveSourceDiscriminator2026Exact.agda"
    "active source discriminator over literal recovery seams"
    sourceFrontierCompression sourceFrontier sameObjectProved unpaid
    "Explicitly separates imported source closures from direct physical bridges. Density->repository state and repository-state->BC1 potential are false while the surrounding CMP98/109/116/119/122 source machinery is owned."
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
    "R236 re-selects an older source seam rather than originating it. Preferred independent first root is literal CMP122 effective-density semantics; regular-E continuation and regular-E->BC1 are compiler outputs."
  ∷ dated-anchor yangMills "2026-09-09 23:54 -> 2026-09-10 00:51"
    "03c53b64c7b4732a18db5cdd0203b6eb23790de7 -> d6c31a7df3f4ad1e42663fd02023b996da07a2e1"
    "BalabanPreferredRowCFrontierRound259Exact.agda + R260 anchored Hessian"
    "least-privilege Row-C frontier; comparison majorant + reference anchor replace false absolute promotion"
    sourceFrontierCompression liveLevel2Theorem sameObjectProved unpaid
    "Row C separates same-density Heat realization, marked comparison, anchor, covariance/gradient map, generator/Hessian identity, relaxation, finite speed and geometric envelope."
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
  ∷ dated-anchor riemannHypothesis "2026-09-01"
    "3297c7b0..."
    "RiemannG2PoleQuotientProducerReconciliation8889Exact.agda + RiemannAristotlePoleQuotientLeanReturn8889Exact.agda"
    "checked-Lean quantitative pole-quotient cluster margin; Gamma bound too coarse; signed off-ordinate evaluation first unpaid analytic theorem"
    crossProverSync crossProverDonor candidateAlias conditionalPayment
    "Prunes fresh cluster-margin analysis and combined-budget circularity. Preserve owner-prover distinction: the quantitative margin is Lean-owned, not an Agda proof, and exact final-taper attachment remains downstream."
  ∷ dated-anchor riemannHypothesis "2026-09-08 06:27 -> 07:30"
    "5b60001ba628ef221bcb25a9ad28fa2b7e0ee411 -> 0045a28d1e1e5fd93aab10c83cb7e6cac14ec83e -> ac271d8d197869486c7927bae0b2d9f7cfc229b7"
    "RiemannG2FinalPoleNearObserverRefinementExact.agda + RiemannG2ProofRelevantTargetTranslationModulationExact.agda"
    "target-relative phase/gap and Fourier/Weyl modulation/cosine laws made proof-relevant"
    consumerRecovery representationWeld sameObjectProved conditionalPayment
    "Generic modulation/cosine compiler is closed. Actual universal-pole-quotient analytic instantiation remains open."
  ∷ dated-anchor riemannHypothesis "2026-09-09 22:07:03"
    "a25681a6cf7e8bdc0739b90a1592530cb64bb256"
    "RiemannG2FinalNearLiteralKernelExact.agda"
    "evaluator-independent final literal near kernel; decisive equality nearResponseAt(J)=finiteNearSum(cellResponse)"
    consumerRecovery liveLevel2Theorem sameObjectProved unpaid
    "Canonical direct representation seam. Certificate evaluation is downstream rather than prerequisite."
  ∷ dated-anchor riemannHypothesis "2026-09 current"
    "RiemannG2PoleQuotientFinalCutReconciliationExact.agda"
    "final cut: signed universal-pole-quotient off estimate + same-taper Gamma precision live; cluster attachment downstream; contradiction compiler pruned"
    cutsetCompression liveLevel2Theorem sameObjectProved unpaid
    "Fresh cluster-margin mathematics is explicitly not required. The two forward analytic leaves are channel-specific allowance payments; RH derived=false."
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
    stableLink : String
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
    "https://www.claymath.org/millennium/yang-mills-the-maths-gap/"
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
    "https://doi.org/10.1007/BF01215223"
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
    "https://doi.org/10.1007/BF01239022"
    "Direct cluster-expansion sequel used by the density->CombinedRG dictionary and CMP116 marked/locality layer."
    "Its preservation estimates do not identify the repository predicates automatically."
  ∷ source-coordinate yangMills
    "Tadeusz Balaban"
    "Convergent Renormalization Expansions for Lattice Gauge Theories"
    "Communications in Mathematical Physics 119 (1988), 243-285"
    "10.1007/BF01217741" verifiedIdentifier
    "person QID unresolved in repo atlas" unresolvedIdentifier
    "unresolved" unresolvedIdentifier
    "not applicable" notApplicableIdentifier
    "https://doi.org/10.1007/BF01217741"
    "Sect.-2 complete-density form/bounds and R221 regular-E projection."
    "The literal dictionary must still map source form/bounds to CombinedRG coupling, boundary and polymer predicates; bibliography alone does not pay that map."
  ∷ source-coordinate yangMills
    "Tadeusz Balaban"
    "Large Field Renormalization I: The Basic Step of the R-Operation"
    "Communications in Mathematical Physics 122 (1989), 175-202"
    "10.1007/BF01257412" verifiedIdentifier
    "person QID unresolved in repo atlas" unresolvedIdentifier
    "unresolved" unresolvedIdentifier
    "not applicable" notApplicableIdentifier
    "https://doi.org/10.1007/BF01257412"
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
    "https://doi.org/10.1007/BF01238433"
    "Boundary reinjection/raw-state/complete-density dictionary owners explicitly cite this object."
    "Acquisition may precede exact section-to-predicate payment; preserve that dependency."
  ∷ source-coordinate yangMills
    "Tosio Kato"
    "Perturbation Theory for Linear Operators"
    "Springer; operator/domain/form calibration source"
    "10.1007/978-3-642-66282-9" verifiedIdentifier
    "Q1335673" verifiedIdentifier
    "unresolved in this audit" unresolvedIdentifier
    "not applicable" notApplicableIdentifier
    "https://doi.org/10.1007/978-3-642-66282-9"
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
    "https://doi.org/10.1016/0001-8708(69)90009-7"
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
    "https://doi.org/10.1007/BF01645738 ; https://doi.org/10.1007/BF01608978"
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
    "https://www.claymath.org/millennium/riemann-hypothesis/"
    "Historical zeta/RH source context and official modern problem target."
    "Historical identity does not pay the modern pole-response kernel or strict high margin."
  ∷ source-coordinate riemannHypothesis
    "Lean Zeta23Bridge / Aristotle return"
    "PoleQuotientClusterMargin.lean; PoleQuotientBudgetCircularity.lean"
    "separate Lean project as recorded by RiemannAristotlePoleQuotientLeanReturn8889Exact"
    "not applicable" notApplicableIdentifier
    "not applicable" notApplicableIdentifier
    "not applicable" notApplicableIdentifier
    "not applicable" notApplicableIdentifier
    "repository/cross-prover artifact; exact external project link unresolved in this ledger"
    "Machine-checked owner for quantitative cluster margin, sharp order demand and budget-circularity no-go; reported aggregate 8889 jobs and standard Lean axioms."
    "Not transported into Agda. Does not own signed off-ordinate evaluation; its Gamma bound is too coarse for the final accuracy window."
  ∷ source-coordinate riemannHypothesis
    "Errett Bishop; Douglas Bridges; Marc Daumas; David Lester; Cesar Munoz"
    "constructive analysis and verified interval-arithmetic donor family"
    "existing repo arithmetic owners"
    "10.1007/978-3-642-61667-9; 10.1109/TC.2008.213" verifiedIdentifier
    "not required for RH theorem identity" notApplicableIdentifier
    "unresolved" unresolvedIdentifier
    "not applicable" notApplicableIdentifier
    "https://doi.org/10.1007/978-3-642-61667-9 ; https://doi.org/10.1109/TC.2008.213"
    "Proof-producing interval arithmetic for reflection-paired cosine-cell enclosures."
    "Arithmetic soundness cannot manufacture the literal-kernel same-object equality or the final channel inequalities."
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
    "Zeta23Bridge/PoleQuotientClusterMargin.lean"
    "quantitative pole-quotient cluster margin + sharp O(|t|^-2)-scale order demand"
    "Lean / Aristotle" true false
    "reuse cluster-margin mathematics after exact final-taper same-object attachment"
    "signed universal-pole-quotient off-ordinate evaluation or same-taper Gamma precision"
  ∷ cross-prover-donor riemannHypothesis
    "Zeta23Bridge/PoleQuotientBudgetCircularity.lean"
    "final budgets cannot be obtained circularly from the balance identity"
    "Lean / Aristotle" true false
    "negative control pruning a false final-budget route"
    "independent off/Gamma channel evaluation"
  ∷ cross-prover-donor riemannHypothesis
    "separate Lean-4.33 Aristotle Zeta/Weil project"
    "reflection partner cancels target odd channel"
    "Lean / Aristotle" true false
    "one source identity needed by FinalNearLiteralKernel; parity-aware cancellation architecture"
    "Agda literal-kernel inhabitant, final finite-sum equality, signed off/Gamma allowance payments"
  ∷ cross-prover-donor riemannHypothesis
    "separate Lean-4.33 Aristotle Zeta/Weil project"
    "LiteralWeilThreeWindowNarrowInstance.exists_taper_triple_two_zero_admission"
    "Lean / Aristotle" true false
    "finite selected nuisance-zero elimination before tail majorization"
    "projected unselected far-tail budget or current direct pole-response theorem"
  ∷ []

------------------------------------------------------------------------
-- ATTEMPTED PAYMENTS / ROUTE PRUNING
------------------------------------------------------------------------

record AttemptedPayment : Set where
  constructor attempted-payment
  field
    paymentLane : Lane
    dateOrWindow : String
    route : String
    intendedConsumer : String
    result : String
    reuseDecision : String
    paymentRole : HistoricalRole

open AttemptedPayment public

attemptedPayments : List AttemptedPayment
attemptedPayments =
  attempted-payment yangMills "2026-08-13 -> current"
    "CMP116/119/122 complete-density -> CombinedRG dictionary"
    "literal selected finite-cutoff density/repository state used by BC1 and later same-family rows"
    "transport compiler is machine checked; literal dictionary fields remain conclusion-paying"
    "do not re-prove RG stability; identify source form/bounds with coupling, boundary and polymer predicates, then selected regular-E with exact BC1"
    buriedDonor
  ∷ attempted-payment yangMills "2026-08-31 -> 2026-09-10"
    "ActiveSourceDiscriminator -> R236 -> R259/R260"
    "least-privilege source instantiation of the frozen four-row Clay cutset"
    "later recuts repeatedly rediscover source identity/instantiation rather than new generic analysis"
    "treat Aug-13 dictionary as buried donor and use later owners as dependency routers"
    sourceFrontier
  ∷ attempted-payment riemannHypothesis "2026-08-29 -> 2026-09-01"
    "parity/Schur + PoleQuotientClusterMargin + BudgetCircularity Lean lane"
    "final universal pole-quotient contradiction"
    "cluster-margin math and circularity no-go owned; arbitrary Gamma exists but too coarse; signed off evaluation absent"
    "reuse quantitative margin after same-object final-taper attachment; do not re-prove it"
    crossProverDonor
  ∷ attempted-payment riemannHypothesis "2026-09 current"
    "FinalNearLiteralKernel + FinalCutReconciliation"
    "final high pole-quotient contradiction"
    "representation equality unpaid; after it, only signed-off and Gamma-precision are live analytic leaves; cluster attachment downstream; contradiction compiler owned"
    "solve literal source attachment first, then channel-specific allowance payments"
    liveLevel2Theorem
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
    "Whole problem = frozen four physical rows. Highest-alpha source semantics = ActiveSourceDiscriminator plus the older Aug-13 complete-density->CombinedRG dictionary; R236/R259/R260 are later least-privilege recuts. Operator/continuum owner remains a parallel whole-construction trust boundary."
    "First source leaf: literal CompleteDensityCombinedRGDictionary. Its fields are source trajectory identity plus source-form->coupling, source-bounds->boundary and source-bounds->polymer admissibility. Second: selected regular-E/effective potential = exact BC1. Later physical leaves include Row-C same-density Heat/Doob identities and the unbounded operator/OS/finite->continuum construction."
    "Theorem1/source estimates, CMP116/119/122 source facts, dictionary->AdmissibleRGState transport, regular-E projection compiler, many finite/RG/functional-analysis compilers, generator uniqueness and bounded gap transport."
    "Snowball source sections/equations that directly identify the three dictionary predicates with the existing CombinedRG invariant region. Search source-native names for coupling/small-field class, boundary/R-operation control and polymer norm; only after those are paid move to the BC1 selected-potential weld."
    false
  ∷ current-cut riemannHypothesis
    "Literal representation first; then FinalCutReconciliation is authoritative for new analysis. Cluster-margin mathematics is already Lean-owned, not a fresh analytic leaf."
    "Representation: exact universal-pole-quotient finite kernel/equality. Analytic: PoleQuotientOffAllowancePayment and PoleQuotientGammaAllowancePayment, i.e. signed off-ordinate bound and same-taper Gamma precision against downstream-assigned allowances. Cluster-margin attachment is downstream same-object work."
    "Generic target-gap modulation/cosine identities; reflection-parity/Schur donors; checked-Lean quantitative cluster margin and budget-circularity no-go; allowance compiler and final contradiction compiler; certificate arithmetic."
    "Search the source/Lean/window owners for an actual final-taper pole-quotient instantiation of the modulation/index/multiplicity/taper fields. In parallel mine signed/projected off-ordinate and Gamma-asymptotic donors by exact output shape. Do not spend proof effort on fresh cluster-margin analysis."
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
    linkNotProof : Bool
    attributionNotAuthority : Bool
    compressedNotClayPaid : Bool

canonicalDiscipline : ArchaeologyDiscipline
canonicalDiscipline = archaeology-discipline
  true true true true true true true true true true true true true true true

------------------------------------------------------------------------
-- GREP-FIRST DASHBOARD
------------------------------------------------------------------------

record ProofCatalystDashboard : Set where
  constructor dashboard
  field ym rh ns gr warning : String

canonicalDashboard : ProofCatalystDashboard
canonicalDashboard = dashboard
  "YM: strongest buried donor is Aug-13 Balaban1989CompleteDensityToCombinedRGExact. Its transport is machine checked; the literal source dictionary remains open. Aug-31 ActiveSourceDiscriminator and Sep R236/R259 merely expose that source bridge more sharply. Highest alpha: pay source form/bounds -> CombinedRG coupling/boundary/polymer predicates, then selected regular-E -> exact BC1; only then attack later Row-C/operator leaves."
  "RH: representation prerequisite = exact final universal-pole-quotient finite kernel. After that, FinalCutReconciliation says only two forward analytic leaves remain: signed universal-pole-quotient off-ordinate allowance and same-taper Gamma allowance. Quantitative cluster-margin math is already checked-Lean-owned and needs downstream exact-taper attachment, not fresh derivation."
  "NS retained for continuity only; active archaeology delegated."
  "GR/QFT retained as non-Clay same-object donor context only."
  "Primary/DOI/QID/Dewey/OEIS/link/date/commit are provenance coordinates, not theorem payment. Unresolved is preferable to invented metadata. Search by theorem output shape, preserve prover ownership, and prove same-object transport before decrementing any Clay cutset."