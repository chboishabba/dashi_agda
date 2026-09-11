module DASHI.Interop.CrossLaneProofArchaeologyLedgerExact where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.String using (String)
open import Agda.Builtin.List using (List; []; _∷_)

------------------------------------------------------------------------
-- CROSS-LANE PROOF ARCHAEOLOGY LEDGER
------------------------------------------------------------------------
-- Canonical grep-first owner for CURRENT proof search.
-- Active archaeology focus: Yang-Mills + Riemann Hypothesis.
-- NS / GR-QFT remain as continuity coordinates only.
--
-- RULES
-- * dates are first-confirmed repository clocks, never origin claims;
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
  sameObjectProved structuralAncestor candidateAlias notSameObject
  unresolvedIdentity : IdentityStatus

data PaymentStatus : Set where
  paid conditionalPayment unpaid notApplicable : PaymentStatus

data IdentifierStatus : Set where
  verifiedIdentifier unresolvedIdentifier notApplicableIdentifier : IdentifierStatus

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
  "Whole-problem accounting remains the frozen Round87-89 four-row physical cutset A/B/C/D. Source archaeology runs on parallel clocks: Aug-13 complete-density->CombinedRG dictionary, Aug-17 published UV-stability boundary, Aug-31 ActiveSourceDiscriminator, Sep-08 R213 source-fixed semantics, Sep-09 R221/R236/R237, Sep-10 R259/R260, plus the Sep-06 operator/continuum audit."
  "FIRST SOURCE LEAF: instantiate the literal CMP119 Sect.-2 source-native state and its selected finite-scale semantics, then prove the source-native E/R/B/background quantitative projections imply the existing CombinedRG coupling/boundary/polymer predicates. SECOND: selected CMP119 regular-E/effective potential = exact BC1."
  "CMP119 Sect.2 source-native carrier, Eq.(2.23) action decomposition, regular-E/R/B sector identities, CMP122-II conditional four-dimensional finite-cutoff UV-stability theorem, dictionary->AdmissibleRGState transport, selected-semantics compiler and regular-E compiler are already represented. Many later algebraic/functional-analysis compilers are also owned."
  "Snowball exact CMP119 source clauses/equations for E/R/B/background norm implications into the repository predicates. The preferred consumer only requires selected scale-indexed density semantics, not an arbitrary total Density->potential interpreter. Only after those identities are paid should proof search move to BC1/Row-C/operator-continuum leaves."
  "Published finite-cutoff UV stability is not continuum YM. CMP119/CMP122 source authority does not identify repository norms automatically. Lean total-map/gap theorems are donors, not the physical partial-domain/self-adjoint continuum construction."

rhRouter : ClayLaneRouter
rhRouter = clay-lane-router riemannHypothesis
  "Exclude every high off-line zero on the actual universal pole-quotient response, then combine with the independent low/critical bridge."
  "REPRESENTATION FIRST: inhabit the exact final universal-pole-quotient finite kernel/equality nearResponseAt(chosen J)=finiteNearSum(cellResponse). FIRST NEW ANALYTIC LEAF AFTER THAT: target-normalized signed universal-pole-quotient finite-near/off evaluation strongly enough for the actual ClusterResponse consumer. SECOND LIVE CHANNEL LEAF: same-taper Gamma precision."
  "Generic target translation/modulation and pole-cosine equalities are proof-bearing compiler output. Reflection-pair parity exists as a Lean donor. A quantitative pole-quotient cluster margin is checked-Lean-owned but is only an OPTIONAL same-object lower-envelope donor in the current direct route; the newest direct frontier prunes intermediate cluster margin as a primitive."
  "Zeta23Bridge owns PoleQuotientClusterMargin.lean and PoleQuotientBudgetCircularity.lean; the Agda return reports an 8889-job build and a Gamma upper that is too coarse. FinalNearLiteralKernel / DirectFiniteNearAttack already fix the canonical near index, multiplicity, off-real displacement and target gap once the final literal problem is attached."
  "Search source/window/Lean owners for the actual universal-pole-quotient analytic instantiation and final nearResponseAt=literal finite-sum equality. In parallel mine signed finite-near/off evaluation and Gamma-precision donors by exact output shape. Reuse 8889 cluster margin only if it shortens the actual-ClusterResponse proof through a proof-relevant same-object lower-envelope transport."
  "Do not re-prove generic modulation/cosine, cluster positivity, or the final contradiction compiler; do not revive absolute-W(t) majorization; do not make the optional intermediate cluster-margin architecture mandatory again. RH remains unproved."

nsContinuityRouter : ClayLaneRouter
nsContinuityRouter = clay-lane-router navierStokes "Continuity only: NS active archaeology delegated elsewhere." "Current live signed/direct-companion spacetime payment remains external to this YM/RH pass." "See dedicated NS forensic owners/PRs." "Historical signed/coherence, Galerkin and downstream continuation architecture retained elsewhere." "No new NS archaeology performed here." "Do not infer NS completion from this ledger."

grContinuityRouter : ClayLaneRouter
grContinuityRouter = clay-lane-router grQuantum "Non-Clay continuity coordinate." "Same-action/metric/stress carrier then anomaly/UV/semiclassical recovery." "Literal-sector variation inhabitants." "Common-action/common-stress weld already represented." "Reuse same-object variational patterns where helpful." "Do not confuse GR/QFT compatibility with Clay YM completion."

canonicalRouters : List ClayLaneRouter
canonicalRouters = ymRouter ∷ rhRouter ∷ nsContinuityRouter ∷ grContinuityRouter ∷ []

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
  dated-anchor yangMills "2026-05-17" "81fc16c11af4f4152410ea9ce9269c68cc223387" "BalabanRGMassGapReceiptSurface.agda" "finite-depth positive gaps != one cutoff/depth-uniform positive gap" firstTypedAppearance terminalConsumer structuralAncestor unpaid "Modern uniformity debt already explicit; later routes are attempted payments."
  ∷ dated-anchor yangMills "2026-07-20" "3933eaa7618e1565580a5ac67aed875dbd850d3f + 16e0a24d5766e93fb9cfee921dc9449dda36426e" "uniform cutoff-gap / contraction family" "uniform finite-cutoff gap-survival attempted producer" formalConsolidation producerTactic structuralAncestor conditionalPayment "Strong old route; not automatically the same continuum Schwinger-family construction."
  ∷ dated-anchor yangMills "2026-08-13 23:46:52" "87710f3cb447fd9e62d48377a4fb6d0de1ca8462" "Balaban1989CompleteDensityToCombinedRGExact.agda" "complete-density -> repository CombinedRG dictionary and transport architecture" buriedPaymentRecovery buriedDonor candidateAlias conditionalPayment "Compiler from literal source dictionary to AdmissibleRGState predates R236. Conclusion-paying object is the dictionary identifying source form/bounds with coupling, boundary and polymer-norm predicates."
  ∷ dated-anchor yangMills "2026-08-17 17:00:10" "7119d36de7ab306fbfb30ea11b1c8edf0858ff97" "BalabanCMP122PublishedFourDimensionalUVStabilityExact.agda" "published four-dimensional finite-cutoff UV-stability boundary with explicit continuum firewalls" buriedPaymentRecovery directProducer structuralAncestor conditionalPayment "Do not re-prove finite-cutoff UV stability. It does not by itself construct continuum Schwinger functions, OS/Wightman reconstruction, non-Gaussianity or a physical mass gap."
  ∷ dated-anchor yangMills "2026-08-20" "f09e953f79933701d59f186629e4ac30e0d0bd3a -> e0038fa05311fdf37462945c9a651bf45c4f16c9" "BalabanClayHighestAlphaRound84SixAnalyticLemmaExact.agda" "six hard physical lemma-family decomposition" cutsetCompression terminalConsumer sameObjectProved unpaid "Historical compression; later frozen four-row cutset is the top whole-problem router."
  ∷ dated-anchor yangMills "2026-08 (Round87-89)" "repository owner BalabanClayHighestAlphaRound87FourAnalyticLemmaExact.agda" "BalabanClayHighestAlphaRound87FourAnalyticLemmaExact.agda" "shortest literal Jaffe-Witten research cutset frozen at four rows A/B/C/D" cutsetCompression terminalConsumer sameObjectProved unpaid "Count decreases only when a whole physical row is inhabited or derived."
  ∷ dated-anchor yangMills "2026-08-31 21:39:42" "c5e3a17442cb440cc9f0d052206129c6e7445234" "BalabanActiveSourceDiscriminator2026Exact.agda" "active source discriminator over literal recovery seams" sourceFrontierCompression sourceFrontier sameObjectProved unpaid "Imported source closures are separated from false direct bridges: density->repository state and repository-state->BC1 remain open."
  ∷ dated-anchor yangMills "2026-09-06 22:57-23:31" "0efb7ebcd57863b03f5d675705f5f5d5859465a2 -> c13782014739bbde3f769c9bfef5074e69c687f3" "YMOperatorDomainContinuumFrontier2026Exact.agda" "operator/domain/continuum trust-boundary audit" operatorContinuumAudit operatorContinuumFrontier sameObjectProved unpaid "Generic operator/gap compilers closed; physical unbounded domain/core, Eq119 source producer, vacuum recovery, OS reconstruction and finite-to-continuum construction remain open."
  ∷ dated-anchor yangMills "2026-09-08 07:31:05" "3376f78dd74068ac47038cbfd4f5a7c6e683b8f2" "BalabanSourceFixedR108EffectiveActionFamilyRound213Exact.agda" "source-fix density semantics before localized R108/BC1 construction" sourceFrontierCompression sourceFrontier sameObjectProved unpaid "Eliminates post-hoc choice of potentialOfDensity; literal CMP122 density semantics and CMP116 localization/radius remain physical leaves."
  ∷ dated-anchor yangMills "2026-09-09 16:01-16:03" "488337947782673a60d7aba8cd5696da6c0035c7 -> d0b2f8ba60ede59ff0723531788d6b932f264445" "BalabanCMP119RegularESourceProjectionRound221Exact.agda" "selected regular-E carrier isolated as preferred BC1 source fibre" sourceFrontierCompression sourceFrontier sameObjectProved unpaid "CMP119 Sect.2 regular-E source authority imported; literal binding of beta-driven density carrier to that projection remains conditional."
  ∷ dated-anchor yangMills "2026-09-09 19:10:54" "1e7e66e03551aa97718a70d0845f9018a6dc0e60" "BalabanPreferredSourceFrontierRound236Exact.agda" "dependency-accurate cross-row physical source frontier" sourceFrontierCompression sourceFrontier sameObjectProved unpaid "R236 re-selects an older source seam rather than originating it."
  ∷ dated-anchor yangMills "2026-09-09 19:11:45" "9742746d8915a87cd1209ba25038456a816a7697" "BalabanSelectedDensitySemanticsRound237Exact.agda" "least-privilege selected scale-indexed density semantics" sourceFrontierCompression sourceFrontier sameObjectProved unpaid "Preferred consumer does not require semantics for arbitrary unconsumed Density values; only selectedPotential(scale) with independent source-authority predicate."
  ∷ dated-anchor yangMills "2026-09-09 23:54 -> 2026-09-10 00:51" "03c53b64c7b4732a18db5cdd0203b6eb23790de7 -> d6c31a7df3f4ad1e42663fd02023b996da07a2e1" "BalabanPreferredRowCFrontierRound259Exact.agda + R260" "least-privilege Row-C frontier; comparison+reference anchor replaces false absolute promotion" sourceFrontierCompression liveLevel2Theorem sameObjectProved unpaid "Row C separates same-density Heat, marked comparison, anchor, covariance/gradient, generator/Hessian, relaxation, finite speed and geometric envelope."
  ∷ dated-anchor riemannHypothesis "2026-02-23" "8bf9e75a159e90c837836a998a43f55680ae66a9" "AbelZeta.agda" "Abel/contraction zeta analytic technology" constructionAncestry diagnostic structuralAncestor notApplicable "Analytic ancestry only."
  ∷ dated-anchor riemannHypothesis "2026-07-19" "78bdf33b725596bd0c1bc399a3e5bb78cc9bb14c" "RH/Weil programme PR #100" "first currently pinned explicit RH proof programme" formalConsolidation producerTactic structuralAncestor unpaid "First explicit RH programme clock pinned by this audit."
  ∷ dated-anchor riemannHypothesis "2026-08-29 13:26 -> 21:06" "7979a68d5e5fa230f51ef3709150af0f152e6cb2 -> d5882c70ca02383bc3f39cd49e87ba4468972372" "RiemannAristotleWindowSchurCrossProverSyncExact.agda" "Lean parity/reflection/two-zero-three-taper Schur" crossProverSync crossProverDonor candidateAlias conditionalPayment "Machine checked in Lean, not transported into Agda; absolute W(t) route exhausted."
  ∷ dated-anchor riemannHypothesis "2026-09-01 01:23:47" "3297c7b0766dcafb4ecf4e0ffaafbdc4167bf0d3" "RiemannG2PoleQuotientProducerReconciliation8889Exact.agda + LeanReturn8889" "checked-Lean quantitative cluster margin; Gamma too coarse; signed off first unpaid analytic theorem" crossProverSync crossProverDonor candidateAlias conditionalPayment "Preserve as optional same-object lower-envelope donor. Current direct route does not require intermediate cluster margin as a primitive."
  ∷ dated-anchor riemannHypothesis "2026-09-08 06:27 -> 07:30" "5b60001ba628ef221bcb25a9ad28fa2b7e0ee411 -> 0045a28d1e1e5fd93aab10c83cb7e6cac14ec83e -> ac271d8d197869486c7927bae0b2d9f7cfc229b7" "FinalPoleNearObserverRefinement + ProofRelevantTargetTranslationModulation" "target-relative phase/gap and modulation/cosine laws made proof-relevant" consumerRecovery representationWeld sameObjectProved conditionalPayment "Generic compiler closed; actual universal-pole-quotient analytic instantiation open."
  ∷ dated-anchor riemannHypothesis "2026-09-09 22:07:03" "a25681a6cf7e8bdc0739b90a1592530cb64bb256" "RiemannG2FinalNearLiteralKernelExact.agda" "evaluator-independent literal near kernel; nearResponseAt(J)=finiteNearSum(cellResponse)" consumerRecovery liveLevel2Theorem sameObjectProved unpaid "Canonical direct representation seam."
  ∷ dated-anchor riemannHypothesis "2026-09 current" "RiemannG2CurrentDirectOneLeafFrontierExact.agda" "RiemannG2CurrentDirectOneLeafFrontierExact.agda" "one representation equality then one primitive high scalar family targeting actual ClusterResponse" cutsetCompression liveLevel2Theorem sameObjectProved unpaid "Intermediate quantitative cluster margin, separate near/Gamma envelopes and final balance as analytic input are pruned in the preferred direct route."
  ∷ []

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
  source-coordinate yangMills "Arthur Jaffe; Edward Witten" "Quantum Yang-Mills Theory" "official Clay Mathematics Institute problem description" "not assigned" notApplicableIdentifier "Arthur Jaffe Q370094; Edward Witten Q201513" verifiedIdentifier "unresolved; do not infer from subject" unresolvedIdentifier "not applicable" notApplicableIdentifier "https://www.claymath.org/millennium/yang-mills-the-maths-gap/" "Terminal target authority." "Problem statement does not supply a DASHI producer."
  ∷ source-coordinate yangMills "Tadeusz Balaban" "Renormalization Group Approach to Lattice Gauge Field Theories I" "CMP 109 (1987), 249-301" "10.1007/BF01215223" verifiedIdentifier "person QID unresolved" unresolvedIdentifier "unresolved" unresolvedIdentifier "not applicable" notApplicableIdentifier "https://doi.org/10.1007/BF01215223" "Ward/colour and differentiated beta/Hessian coordinates." "Source formula != literal physical instantiation."
  ∷ source-coordinate yangMills "Tadeusz Balaban" "Renormalization Group Approach to Lattice Gauge Field Theories II. Cluster Expansions" "CMP 116 (1988), 1-22; source abstract says exponentiated fluctuation-field cluster expansion preserves inductive assumptions" "10.1007/BF01239022" verifiedIdentifier "person QID unresolved" unresolvedIdentifier "unresolved" unresolvedIdentifier "not applicable" notApplicableIdentifier "https://doi.org/10.1007/BF01239022" "Cluster-expansion sequel and density-dictionary/localization source bridge." "Preservation estimates do not identify repository predicates automatically."
  ∷ source-coordinate yangMills "Tadeusz Balaban" "Convergent Renormalization Expansions for Lattice Gauge Theories" "CMP 119 (1988), 243-285; Sect.2 especially (2.18)-(2.23), (2.25)-(2.33), (2.40)-(2.42)" "10.1007/BF01217741" verifiedIdentifier "person QID unresolved" unresolvedIdentifier "unresolved" unresolvedIdentifier "not applicable" notApplicableIdentifier "https://doi.org/10.1007/BF01217741" "Source-native rho_k/U_k(V)/E_k/R_k/B_k/vacuum/coupling/action carrier; Eq.(2.23); regular-E/R/B/background quantitative projections." "Literal source-native instantiation and sector norm implications remain conclusion-paying; six scalar coordinates are projections, not source identity."
  ∷ source-coordinate yangMills "Tadeusz Balaban" "Large Field Renormalization I: The Basic Step of the R-Operation" "CMP 122 (1989), 175-202" "10.1007/BF01257412" verifiedIdentifier "person QID unresolved" unresolvedIdentifier "unresolved" unresolvedIdentifier "not applicable" notApplicableIdentifier "https://doi.org/10.1007/BF01257412" "Large-field source family." "Exact part/section-to-leaf mapping remains source-local."
  ∷ source-coordinate yangMills "Tadeusz Balaban" "Large Field Renormalization II: Localization, Exponentiation, and Bounds for the R Operation" "CMP 122 (1989), 355-392; Theorem 1 conditionally completes four-dimensional pure-gauge finite-cutoff UV stability" "10.1007/BF01238433" verifiedIdentifier "person QID unresolved" unresolvedIdentifier "unresolved" unresolvedIdentifier "not applicable" notApplicableIdentifier "https://doi.org/10.1007/BF01238433" "Published Theorem-1 UV-stability authority and large-field/boundary reinjection source." "Does not construct continuum Schwinger functions, OS axioms, non-Gaussianity or cutoff-uniform physical mass gap; exact source/repo dictionary still required."
  ∷ source-coordinate yangMills "Tosio Kato" "Perturbation Theory for Linear Operators" "Springer operator/domain/form calibration" "10.1007/978-3-642-66282-9" verifiedIdentifier "Q1335673" verifiedIdentifier "unresolved in this audit" unresolvedIdentifier "not applicable" notApplicableIdentifier "https://doi.org/10.1007/978-3-642-66282-9" "Calibrates genuine unbounded domains/forms." "Does not prove selected YM Hamiltonian hypotheses."
  ∷ source-coordinate yangMills "Umberto Mosco" "Convergence of Convex Sets and of Solutions of Variational Inequalities" "Advances in Mathematics 3 (1969), 510-585" "10.1016/0001-8708(69)90009-7" verifiedIdentifier "unresolved" unresolvedIdentifier "unresolved" unresolvedIdentifier "not applicable" notApplicableIdentifier "https://doi.org/10.1016/0001-8708(69)90009-7" "Form/Mosco recovery calibration." "Generic compiler != physical YM recovery system."
  ∷ source-coordinate yangMills "Konrad Osterwalder; Robert Schrader" "Axioms for Euclidean Green's Functions I / II" "CMP 31 (1973), 83-112; 42 (1975), 281-305" "10.1007/BF01645738; 10.1007/BF01608978" verifiedIdentifier "unresolved here" unresolvedIdentifier "unresolved" unresolvedIdentifier "not applicable" notApplicableIdentifier "https://doi.org/10.1007/BF01645738 ; https://doi.org/10.1007/BF01608978" "Euclidean reconstruction target." "Does not supply finite-to-continuum YM."
  ∷ source-coordinate riemannHypothesis "Bernhard Riemann" "Ueber die Anzahl der Primzahlen unter einer gegebenen Groesse" "1859 memoir / official RH target" "not assigned" notApplicableIdentifier "Q42299; RH Q205966" verifiedIdentifier "unresolved" unresolvedIdentifier "not applicable" notApplicableIdentifier "https://www.claymath.org/millennium/riemann-hypothesis/" "Historical source context / modern target." "Does not pay pole-response kernel or channel inequalities."
  ∷ source-coordinate riemannHypothesis "Lean Zeta23Bridge / Aristotle return" "PoleQuotientClusterMargin.lean; PoleQuotientBudgetCircularity.lean" "cross-prover artifact recorded by RiemannAristotlePoleQuotientLeanReturn8889Exact" "not applicable" notApplicableIdentifier "not applicable" notApplicableIdentifier "not applicable" notApplicableIdentifier "not applicable" notApplicableIdentifier "repository/cross-prover artifact; exact external project link unresolved" "Machine-checked quantitative cluster margin, sharp order demand, budget-circularity no-go; reported 8889 jobs." "Not transported into Agda; signed off absent; Gamma too coarse. In current direct frontier this margin is optional, not primitive."
  ∷ source-coordinate riemannHypothesis "Errett Bishop; Douglas Bridges; Marc Daumas; David Lester; Cesar Munoz" "constructive analysis and verified interval-arithmetic donor family" "existing repo arithmetic owners" "10.1007/978-3-642-61667-9; 10.1109/TC.2008.213" verifiedIdentifier "not required" notApplicableIdentifier "unresolved" unresolvedIdentifier "not applicable" notApplicableIdentifier "https://doi.org/10.1007/978-3-642-61667-9 ; https://doi.org/10.1109/TC.2008.213" "Proof-producing interval arithmetic." "Cannot manufacture literal-kernel identity or final channel inequalities."
  ∷ []

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
  cross-prover-donor yangMills "RequestProject/YangMills/GeneratorUniquenessCore.lean" "generator_unique_of_evolution_eq / generator_clm_unique" "Lean / Aristotle" true false "same-evolution generator uniqueness" "partial-domain self-adjoint physical YM Hamiltonian"
  ∷ cross-prover-donor yangMills "RequestProject/YangMills/GaugeInvariantL2Carrier.lean" "hamiltonian_eqOn_core_of_same_evolution / hamiltonian_unique_of_same_evolution_on_dense_core" "Lean / Aristotle" true false "gauge-invariant L2 carrier and same-evolution uniqueness" "domain D(H), domain invariance, self-adjoint YM Hamiltonian"
  ∷ cross-prover-donor yangMills "RequestProject/YangMills/MassGapFormTransport.lean" "hasFormGap_of_tendsto / hasFormGap_of_tendsto_of_gap_tendsto" "Lean / Aristotle" true false "bounded strong-limit quadratic-form gap transport" "unbounded form/resolvent/Mosco continuum theorem"
  ∷ cross-prover-donor riemannHypothesis "Zeta23Bridge/PoleQuotientClusterMargin.lean" "quantitative pole-quotient cluster margin + sharp O(|t|^-2) demand" "Lean / Aristotle" true false "optional same-object cluster lower-envelope route" "current direct actual-ClusterResponse theorem, signed off-ordinate or Gamma precision"
  ∷ cross-prover-donor riemannHypothesis "Zeta23Bridge/PoleQuotientBudgetCircularity.lean" "budgets cannot come circularly from balance identity" "Lean / Aristotle" true false "negative control" "independent off/Gamma evaluation"
  ∷ cross-prover-donor riemannHypothesis "separate Lean-4.33 Aristotle Zeta/Weil project" "reflection partner cancels target odd channel" "Lean / Aristotle" true false "literal-kernel parity identity donor" "Agda kernel inhabitant or off/Gamma payments"
  ∷ cross-prover-donor riemannHypothesis "separate Lean-4.33 Aristotle Zeta/Weil project" "LiteralWeilThreeWindowNarrowInstance.exists_taper_triple_two_zero_admission" "Lean / Aristotle" true false "finite selected nuisance elimination" "current direct pole-response channel estimates"
  ∷ []

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
  attempted-payment yangMills "2026-08-13 -> current" "CMP116/119/122 complete-density -> CombinedRG dictionary" "literal selected finite-cutoff density/repository state used by BC1 and later same-family rows" "transport compiler machine checked; literal source-native state and E/R/B/background norm implications remain conclusion-paying" "do not re-prove RG stability; instantiate source-native CMP119 carrier and map its actual sector bounds to coupling/boundary/polymer predicates" buriedDonor
  ∷ attempted-payment yangMills "2026-09-08 -> 2026-09-09" "R213 total source-fixed density semantics -> R221 regular-E projection -> R237 selected-scale semantics" "exact BC1 effective potential on the same source density sequence" "post-hoc potential choice removed; consumer contract minimized from total Density semantics to selected scale-indexed source potential" "pay only literal selected CMP119/CMP122 semantics and regular-E binding; do not reconstruct unused density interpretations" sourceFrontier
  ∷ attempted-payment yangMills "2026-08-31 -> 2026-09-10" "ActiveSourceDiscriminator -> R236 -> R259/R260" "least-privilege source instantiation of frozen four-row cutset" "later recuts repeatedly rediscover source identity/instantiation rather than generic analysis" "use Aug-13/R213/R221 buried donors and later owners as dependency routers" sourceFrontier
  ∷ attempted-payment riemannHypothesis "2026-08-29 -> 2026-09-01" "parity/Schur + PoleQuotientClusterMargin + BudgetCircularity Lean lane" "final universal pole-quotient contradiction" "cluster-margin math and circularity no-go owned; Gamma too coarse; signed off absent" "retain margin only as optional lower-envelope donor after exact-taper attachment; do not reintroduce it as mandatory current primitive" crossProverDonor
  ∷ attempted-payment riemannHypothesis "2026-09-08 -> current" "proof-relevant target translation/modulation -> FinalNearLiteralKernel -> DirectFiniteNearAttack" "final high pole-quotient contradiction" "generic phase compiler and canonical literal field routing owned; final nearResponseAt=finiteNearSum identity and consumer-sufficient signed evaluation remain unpaid" "instantiate actual universal pole quotient, then target actual ClusterResponse directly or use a proof-relevant lower-envelope donor if genuinely shorter" liveLevel2Theorem
  ∷ []

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
    "Whole problem=frozen four rows. Highest-alpha source semantics=source-native CMP119 Sect.-2 carrier + Aug-13 density->CombinedRG dictionary + R237 selected density semantics; R236/R259/R260 are later least-privilege routers; operator/continuum owner is parallel."
    "First: literal CMP119/122 source-native state and selected density semantics, including E/R/B/background quantitative norm implications -> existing coupling/boundary/polymer predicates. Second: selected regular-E/effective potential=exact BC1. Later: Row-C same-density Heat/Doob identities and unbounded operator/OS/finite->continuum construction."
    "CMP116/119/122 source theorems; CMP122-II conditional finite-cutoff UV stability; source-native state/selected-semantics/regular-E compilers; dictionary->AdmissibleRGState transport; finite/RG/functional-analysis compilers; generator uniqueness; bounded gap transport."
    "Snowball exact CMP119 equations (2.23), (2.25)-(2.33), (2.40)-(2.42) and their source bounds into the actual repository norm predicates. Prefer R237 selected-scale semantics over a stronger total interpreter."
    false
  ∷ current-cut riemannHypothesis
    "Literal representation first; then current DirectOneLeaf frontier governs new analysis. 8889 cluster-margin math is an optional donor, not a required intermediate primitive."
    "Representation: actual universal-pole-quotient instantiation + final nearResponseAt(J)=finiteNearSum(cellResponse). Analytic: consumer-sufficient signed finite-near/off evaluation and same-taper Gamma precision, ultimately below actual ClusterResponse."
    "Proof-relevant target-gap modulation/cosine; canonical near index/multiplicity/displacement/gap routing; reflection/Schur donors; checked-Lean cluster margin and circularity no-go; allowance/final contradiction compilers; certificate arithmetic."
    "First recover the actual final pole-quotient carrier attachment. Then evaluate the signed finite near sum without erasing phase. Use 8889 cluster lower only if proof-relevant same-object transport shortens the actual-ClusterResponse inequality; otherwise stay direct."
    false
  ∷ []

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
canonicalDiscipline = archaeology-discipline true true true true true true true true true true true true true true true

record ProofCatalystDashboard : Set where
  constructor dashboard
  field
    ym : String
    rh : String
    ns : String
    gr : String
    warning : String

canonicalDashboard : ProofCatalystDashboard
canonicalDashboard = dashboard
  "YM: FIRST = literal CMP119/122 source-native selected density semantics and E/R/B/background norm implications -> existing CombinedRG coupling/boundary/polymer predicates. Published finite-cutoff UV stability and the transport compiler are already owned. SECOND = selected regular-E/effective potential -> exact BC1."
  "RH: FIRST representation = actual universal-pole-quotient instantiation + final nearResponseAt=literal finite sum. Generic modulation/cosine and canonical field routing are already compiled. FIRST new analysis = phase-preserving signed finite-near/off evaluation against actual ClusterResponse; SECOND = same-taper Gamma precision. 8889 cluster margin is optional, not primitive."
  "NS retained for continuity only; active archaeology delegated."
  "GR/QFT retained as non-Clay same-object donor context only."
  "Primary/DOI/QID/Dewey/OEIS/link/date/commit are provenance coordinates, not theorem payment. Unresolved is preferable to invented metadata. Search by theorem output shape, preserve prover ownership, and prove same-object transport before decrementing any Clay cutset."