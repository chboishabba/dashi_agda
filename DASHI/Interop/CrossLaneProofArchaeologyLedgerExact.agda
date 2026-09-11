module DASHI.Interop.CrossLaneProofArchaeologyLedgerExact where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.String using (String)
open import Agda.Builtin.List using (List; []; _∷_)

------------------------------------------------------------------------
-- CROSS-LANE PROOF ARCHAEOLOGY LEDGER
------------------------------------------------------------------------
-- Canonical grep-first owner for current proof search.
-- Active lanes: Yang-Mills + Riemann Hypothesis.
-- NS / GR-QFT remain continuity coordinates only.
--
-- The current search policy is the repo-native Ibrahim traversal policy:
-- explicit formulation owner -> typed dependency -> typed generalisation.
-- Source/QID/Dewey/link coordinates may support or identify a node but never
-- replace the formulation owner or manufacture theorem payment.
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

data IbrahimEdgeKind : Set where
  formulatedBy dependsOn generalisesTo supportedBy crossPollinatesWith externallyIdentifiedBy : IbrahimEdgeKind

record IbrahimPolicy : Set where
  constructor ibrahim-policy
  field
    preferExplicitFormulationOwner : Bool
    preferTypedDependency : Bool
    preferTypedGeneralisation : Bool
    sourceIdentityCoordinateOnly : Bool
    qidCoordinateOnly : Bool
    deweyCoordinateOnly : Bool
    lexicalFallbackAllowed : Bool
    firstLinkCreatesTheoremImplication : Bool
    funnelRankCreatesAuthority : Bool

canonicalIbrahimPolicy : IbrahimPolicy
canonicalIbrahimPolicy = ibrahim-policy true true true true true true false false false

record ClayLaneRouter : Set where
  constructor clay-lane-router
  field
    lane : Lane
    mission : String
    wholeProblemCutset : String
    firstLiveLeaf : String
    alreadyOwned : String
    nextTraversal : String
    firewall : String
open ClayLaneRouter public

ymRouter : ClayLaneRouter
ymRouter = clay-lane-router yangMills
  "Finish the Jaffe-Witten existence + mass-gap problem on one literal compact-simple continuum construction."
  "Whole problem remains the frozen four physical rows A/B/C/D. Source, operator/continuum and row-local clocks are kept separate."
  "FIRST SOURCE COORDINATE: literal CMP119 raw source objects over the existing finite beta history. SECOND, blocked by the first: the literal Section-2 predicate vocabulary indexed by that exact raw state. The same-coupling weld and CMP122 active Section-2 transport are already machine checked."
  "Round58 constructs runningCoupling=History.couplingAt definitionally and specializes CMP122 Theorem 1 to the raw CMP119 state. Round217 splits raw objects from predicate vocabulary. CMP119 regular-E -> CMP109/116 and regular-E -> BC1 continuations are already compiler-closed after source realization."
  "Follow the CMP119 primary source from Eq.(2.23) into the actual rho_k/background/fluctuation/Wilson/E/R/B/vacuum objects, then bind the source Section-2 E/R/B/background predicates and quantitative norm meanings to those SAME objects. Only then continue to selected semantics / CombinedRG / BC1."
  "Published finite-cutoff UV stability is not continuum YM. A source citation is not a literal raw object; six scalar projections are not the source state; QID/DOI/Dewey are not proof."

rhRouter : ClayLaneRouter
rhRouter = clay-lane-router riemannHypothesis
  "Exclude every high off-line zero on the actual universal pole-quotient response, then combine with the independent low/critical bridge."
  "Preferred route: transport the already checked every-cutoff near/far + far-shell theorem onto the exact Agda carrier; attach the actual universal-pole-quotient finite-near representation; then prove the phase-preserving signed near/off payment and same-taper Gamma precision below actual ClusterResponse."
  "Lean already owns the every-J split, explicit far-shell modulus, finite near carrier and literal D_off cutoff transport; generic target translation/modulation/cosine is compiler output. The 8889 cluster margin is an optional lower-envelope donor, not a primitive in the newest direct route."
  "Follow FinalNearLiteralKernel -> ExplicitCutoffNearFarAgdaTransport -> ExplicitCutoffCarrierLeanReturn before searching new analysis. After same-object transport, the fresh zero-side analytic field is the signed finite near payment. Search the pole-taper construction and Gamma response only by exact carrier/output shape."
  "The Agda Lean-return receipt is provenance, not transported proof. Do not resurrect absolute-W(t), an intermediate cluster margin, a selected Weil window, or determinant-q payment as mandatory architecture. RH remains unproved."

nsContinuityRouter : ClayLaneRouter
nsContinuityRouter = clay-lane-router navierStokes "Continuity only; active NS archaeology delegated." "NS completion tracked elsewhere." "No new NS work here." "See dedicated NS forensic owners." "No traversal scheduled." "Do not infer NS completion from this file."

grContinuityRouter : ClayLaneRouter
grContinuityRouter = clay-lane-router grQuantum "Non-Clay continuity coordinate." "Common action/metric/stress plus anomaly/UV/semiclassical recovery." "Literal sector inhabitants." "Common variational compilers exist." "Reuse only by explicit same-object transport." "Do not confuse GR/QFT compatibility with Clay YM completion."

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
  dated-anchor yangMills "2026-05-17" "81fc16c11af4f4152410ea9ce9269c68cc223387" "BalabanRGMassGapReceiptSurface.agda" "finite-depth gaps do not imply one cutoff-uniform positive gap" firstTypedAppearance terminalConsumer structuralAncestor unpaid "Uniformity debt already explicit."
  ∷ dated-anchor yangMills "2026-07-20" "3933eaa7618e1565580a5ac67aed875dbd850d3f + 16e0a24d5766e93fb9cfee921dc9449dda36426e" "uniform cutoff-gap / contraction family" "old uniform-gap attempted producer" formalConsolidation producerTactic structuralAncestor conditionalPayment "Potential donor only after same-family transport."
  ∷ dated-anchor yangMills "2026-08-13 23:46:52" "87710f3cb447fd9e62d48377a4fb6d0de1ca8462" "Balaban1989CompleteDensityToCombinedRGExact.agda" "complete-density -> CombinedRG transport compiler" buriedPaymentRecovery buriedDonor candidateAlias conditionalPayment "Transport is closed once a literal dictionary is supplied."
  ∷ dated-anchor yangMills "2026-08-16 18:29:32" "120e84195d504b2f07736a80006404e9daa87cc0" "BalabanCMP119Section2SourceNativeStateExact.agda" "CMP119 Section-2 state made source-native" buriedPaymentRecovery sourceFrontier candidateAlias conditionalPayment "rho_k/U_k/E_k/R_k/B_k/vacuum/coupling/action are separated from later scalar projections."
  ∷ dated-anchor yangMills "2026-08-17 16:24:06" "3890018d97bc0e10ac41e12244095e3b4de16fa3" "BalabanCMP119SourceNativeRawStateActiveBoundsExact.agda" "raw CMP119 state separated from active Section-2 theorem" buriedPaymentRecovery sourceFrontier sameObjectProved conditionalPayment "Prevents all-scale preservation from being smuggled into source data."
  ∷ dated-anchor yangMills "2026-08-17 16:30:18" "16ac4fcd53cca985c74cf01eefa93f87da1285e2" "BalabanCMP122Theorem1ToRawCMP119ActiveExact.agda" "CMP122 Theorem 1 specialized to same raw CMP119 state" buriedPaymentRecovery compiler sameObjectProved paid "Active E/R/B/background/complete-density predicates compile from published theorem once the raw state is supplied."
  ∷ dated-anchor yangMills "2026-08-17 16:35:26 -> 16:37:00" "dc44d87de8fe72ea9a2aac4969c34513642efcfa -> fd07fe06a857e9b815e19042b37aa4b5bb7a20d9" "BalabanCMP119RawStateFromFiniteBetaHistoryExact.agda" "raw CMP119 state constructed over finite beta history" buriedPaymentRecovery representationWeld sameObjectProved paid "runningCoupling k = History.couplingAt k definitionally; coupling equality is not a live leaf."
  ∷ dated-anchor yangMills "2026-08-17 17:00:10" "7119d36de7ab306fbfb30ea11b1c8edf0858ff97" "BalabanCMP122PublishedFourDimensionalUVStabilityExact.agda" "published finite-cutoff four-dimensional UV stability" buriedPaymentRecovery directProducer structuralAncestor conditionalPayment "Does not construct continuum Schwinger/OS/non-Gaussianity/mass gap."
  ∷ dated-anchor yangMills "2026-08 Round87-89" "BalabanClayHighestAlphaRound87FourAnalyticLemmaExact.agda" "four frozen physical rows A/B/C/D" "whole Clay accounting surface" cutsetCompression terminalConsumer sameObjectProved unpaid "Do not decrement without whole-row payment."
  ∷ dated-anchor yangMills "2026-09-06 22:57-23:31" "0efb7ebcd57863b03f5d675705f5f5d5859465a2 -> c13782014739bbde3f769c9bfef5074e69c687f3" "YMOperatorDomainContinuumFrontier2026Exact.agda" "physical unbounded/operator/continuum audit" operatorContinuumAudit operatorContinuumFrontier sameObjectProved unpaid "Generic operator facts separated from physical YM construction."
  ∷ dated-anchor yangMills "2026-09-08 07:47:09 -> 07:48:19" "e5c137347026f96c06533bcc26e2a1b36f562aaa -> ce6699fa7396a7f61ea8ad4b0b34c3a0942419bf -> 1dfbab5ffb001fcbdc1d79a2d66b3c05fc5219bd" "BalabanCMP119RawSourceRealizationSplitRound217Exact + PreferredRawSourceFrontierRound217Exact" "literal raw objects split from state-indexed predicate vocabulary" sourceFrontierCompression sourceFrontier sameObjectProved unpaid "First open coordinate = literal raw objects; predicate vocabulary is blocked by it; coupling and active Section-2 are closed."
  ∷ dated-anchor yangMills "2026-09-09 19:10:54 -> 19:11:45" "1e7e66e03551aa97718a70d0845f9018a6dc0e60 -> 9742746d8915a87cd1209ba25038456a816a7697" "R236/R237" "later least-privilege source recut" sourceFrontierCompression sourceFrontier sameObjectProved unpaid "Useful router, but Ibrahim traversal recovers the earlier Round58/217 explanatory parent."
  ∷ dated-anchor yangMills "2026-09-09/10" "03c53b64c7b4732a18db5cdd0203b6eb23790de7 -> d6c31a7df3f4ad1e42663fd02023b996da07a2e1" "R259/R260" "Row-C comparison+anchor correction" sourceFrontierCompression liveLevel2Theorem sameObjectProved unpaid "Comparison difference is not an absolute Hessian bound."
  ∷ dated-anchor riemannHypothesis "2026-02-23" "8bf9e75a159e90c837836a998a43f55680ae66a9" "AbelZeta.agda" "Abel/contraction zeta technology" constructionAncestry diagnostic structuralAncestor notApplicable "Analytic ancestry only."
  ∷ dated-anchor riemannHypothesis "2026-07-19" "78bdf33b725596bd0c1bc399a3e5bb78cc9bb14c" "RH/Weil programme PR #100" "first currently pinned explicit RH programme" formalConsolidation producerTactic structuralAncestor unpaid "Programme clock, not final route identity."
  ∷ dated-anchor riemannHypothesis "2026-08-29 13:26 -> 21:06" "7979a68d5e5fa230f51ef3709150af0f152e6cb2 -> d5882c70ca02383bc3f39cd49e87ba4468972372" "RiemannAristotleWindowSchurCrossProverSyncExact.agda" "Lean parity/reflection/Schur donors" crossProverSync crossProverDonor candidateAlias conditionalPayment "Checked Lean, not transported Agda; absolute W(t) route exhausted."
  ∷ dated-anchor riemannHypothesis "2026-08-30 01:45:19" "39b05cd6f249927603d414c44817e7e0524264ef" "RiemannAristotleExplicitCutoffCarrierLeanReturnExact.agda" "Lean every-cutoff near/far split + explicit far-shell modulus + literal D_off cutoff" crossProverSync crossProverDonor candidateAlias conditionalPayment "8883-job return: FarShellCutoffTailBound.lean, NearFarCarrierSplit.lean, OffOrdinateCutoffCarrier.lean. Proof not transported into Agda."
  ∷ dated-anchor riemannHypothesis "2026-09-01 01:23:47" "3297c7b0766dcafb4ecf4e0ffaafbdc4167bf0d3" "RiemannG2PoleQuotientProducerReconciliation8889Exact.agda" "Lean quantitative cluster margin; Gamma too coarse; signed off unpaid" crossProverSync crossProverDonor candidateAlias conditionalPayment "Cluster margin retained only as optional lower-envelope donor in current route."
  ∷ dated-anchor riemannHypothesis "2026-09-08 06:27 -> 07:30" "5b60001ba628ef221bcb25a9ad28fa2b7e0ee411 -> 0045a28d1e1e5fd93aab10c83cb7e6cac14ec83e -> ac271d8d197869486c7927bae0b2d9f7cfc229b7" "Observer refinement + target modulation" "target-relative gap and cosine phase made proof relevant" consumerRecovery representationWeld sameObjectProved conditionalPayment "Generic modulation mathematics is compiler output."
  ∷ dated-anchor riemannHypothesis "2026-09-09 22:07:03" "a25681a6cf7e8bdc0739b90a1592530cb64bb256" "RiemannG2FinalNearLiteralKernelExact.agda" "evaluator-independent final finite-near kernel" consumerRecovery liveLevel2Theorem sameObjectProved unpaid "One nearResponseAt = finiteNearSum equality remains after exact carrier attachment."
  ∷ dated-anchor riemannHypothesis "2026-09 current" "RiemannG2CurrentDirectOneLeafFrontierExact.agda" "current direct route" "representation then one primitive high scalar family against actual ClusterResponse" cutsetCompression liveLevel2Theorem sameObjectProved unpaid "Intermediate cluster margin is pruned as primitive."
  ∷ []

record IbrahimTraversalEdge : Set where
  constructor ibrahim-edge
  field
    edgeLane : Lane
    fromNode : String
    toNode : String
    kind : IbrahimEdgeKind
    rationale : String
    identity : IdentityStatus
    payment : PaymentStatus
open IbrahimTraversalEdge public

ibrahimEdges : List IbrahimTraversalEdge
ibrahimEdges =
  ibrahim-edge yangMills "Round237 selected density semantics" "Round217 literal CMP119 raw objects" dependsOn "Later selected semantics requires a source family; Round217 identifies the first raw source coordinate." sameObjectProved unpaid
  ∷ ibrahim-edge yangMills "literal CMP119 raw objects" "CMP119 Eq.(2.23) rho/U/E/R/B/vacuum/action source family" supportedBy "Primary-source object identity, not a scalar surrogate." unresolvedIdentity unpaid
  ∷ ibrahim-edge yangMills "raw CMP119 state" "finite beta history" dependsOn "Round58 constructs running coupling from History.couplingAt definitionally." sameObjectProved paid
  ∷ ibrahim-edge yangMills "raw CMP119 state + predicate vocabulary" "CMP122 Theorem 1 active Section-2 witness" dependsOn "Published theorem supplies active E/R/B/background/complete-density predicates once the exact source realization is supplied." sameObjectProved paid
  ∷ ibrahim-edge yangMills "source-realized regular E sector" "CMP109/116 differentiated carrier + exact BC1" generalisesTo "Continuation compilers are closed; source realization remains upstream." sameObjectProved conditionalPayment
  ∷ ibrahim-edge riemannHypothesis "FinalNearLiteralKernel" "ExplicitCutoffNearFarAgdaTransport" dependsOn "Final nearResponseAt is the transported near carrier at the chosen crossing cutoff." sameObjectProved conditionalPayment
  ∷ ibrahim-edge riemannHypothesis "ExplicitCutoffNearFarAgdaTransport" "2026-08-30 Lean explicit cutoff return" supportedBy "Lean owns every-J split, finite-near carrier and far-shell formula; Agda proof transport remains explicit." candidateAlias conditionalPayment
  ∷ ibrahim-edge riemannHypothesis "final finite-near representation" "proof-relevant target translation/modulation" dependsOn "Generic target gap/cosine law is already compiler output." sameObjectProved paid
  ∷ ibrahim-edge riemannHypothesis "signed finite-near payment" "actual ClusterResponse" formulatedBy "Newest direct consumer targets actual ClusterResponse; 8889 intermediate margin is optional." sameObjectProved unpaid
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
  source-coordinate yangMills "Arthur Jaffe; Edward Witten" "Quantum Yang-Mills Theory" "official Clay Mathematics Institute problem description" "not assigned" notApplicableIdentifier "Arthur Jaffe Q370094; Edward Witten Q201513; Yang-Mills theory Q1192873" verifiedIdentifier "unresolved" unresolvedIdentifier "not applicable" notApplicableIdentifier "https://www.claymath.org/millennium/yang-mills-the-maths-gap/" "Terminal target / external identity coordinates." "Problem statement does not supply a DASHI producer."
  ∷ source-coordinate yangMills "Tadeusz Balaban" "Renormalization Group Approach to Lattice Gauge Field Theories I" "CMP 109 (1987), 249-301" "10.1007/BF01215223" verifiedIdentifier "person QID unresolved" unresolvedIdentifier "unresolved" unresolvedIdentifier "not applicable" notApplicableIdentifier "https://doi.org/10.1007/BF01215223" "Ward/colour/differentiated coordinates." "Formula identity != literal physical instantiation."
  ∷ source-coordinate yangMills "Tadeusz Balaban" "Renormalization Group Approach to Lattice Gauge Field Theories II. Cluster Expansions" "CMP 116 (1988), 1-22" "10.1007/BF01239022" verifiedIdentifier "person QID unresolved" unresolvedIdentifier "unresolved" unresolvedIdentifier "not applicable" notApplicableIdentifier "https://doi.org/10.1007/BF01239022" "Cluster/localization source bridge." "Preservation does not identify repo predicates automatically."
  ∷ source-coordinate yangMills "Tadeusz Balaban" "Convergent Renormalization Expansions for Lattice Gauge Theories" "CMP 119 (1988), 243-285; Sect.2 Eq.(2.23), (2.25)-(2.33), (2.40)-(2.42)" "10.1007/BF01217741" verifiedIdentifier "person QID unresolved" unresolvedIdentifier "unresolved" unresolvedIdentifier "not applicable" notApplicableIdentifier "https://doi.org/10.1007/BF01217741" "Primary source for literal rho/U/E/R/B/vacuum/action objects and Section-2 predicates." "Literal raw objects and state-indexed predicate/norm instantiation remain the first source payment."
  ∷ source-coordinate yangMills "Tadeusz Balaban" "Large Field Renormalization I: The Basic Step of the R-Operation" "CMP 122 (1989), 175-202" "10.1007/BF01257412" verifiedIdentifier "person QID unresolved" unresolvedIdentifier "unresolved" unresolvedIdentifier "not applicable" notApplicableIdentifier "https://doi.org/10.1007/BF01257412" "Large-field source family." "Exact source-local mapping remains explicit."
  ∷ source-coordinate yangMills "Tadeusz Balaban" "Large Field Renormalization II: Localization, Exponentiation, and Bounds for the R Operation" "CMP 122 (1989), 355-392; Theorem 1" "10.1007/BF01238433" verifiedIdentifier "person QID unresolved" unresolvedIdentifier "unresolved" unresolvedIdentifier "not applicable" notApplicableIdentifier "https://doi.org/10.1007/BF01238433" "Published conditional completion of four-dimensional finite-cutoff UV stability." "Not continuum Schwinger/OS/non-Gaussianity/mass gap."
  ∷ source-coordinate riemannHypothesis "Mark Ibrahim; Christopher M. Danforth; Peter Sheridan Dodds" "Connecting every bit of knowledge: The structure of Wikipedia's First Link Network" "Journal of Computational Science 19 (2017), 21-30; arXiv:1605.00309" "10.1016/j.jocs.2016.12.001" verifiedIdentifier "not required" notApplicableIdentifier "not applicable" notApplicableIdentifier "not applicable" notApplicableIdentifier "https://doi.org/10.1016/j.jocs.2016.12.001" "Search/traversal policy donor only." "Navigation topology does not create theorem implication or source authority."
  ∷ source-coordinate riemannHypothesis "Bernhard Riemann" "Ueber die Anzahl der Primzahlen unter einer gegebenen Groesse" "1859 memoir / official RH target" "not assigned" notApplicableIdentifier "Bernhard Riemann Q42299; RH Q205966; Riemann zeta function Q187235" verifiedIdentifier "Riemann zeta function 515.56" verifiedIdentifier "not applicable" notApplicableIdentifier "https://www.claymath.org/millennium/riemann-hypothesis/" "Historical/source identity coordinates." "Does not pay the pole-response kernel or channel inequality."
  ∷ source-coordinate riemannHypothesis "Aristotle / Zeta23Bridge Lean return" "FarShellCutoffTailBound.lean; NearFarCarrierSplit.lean; OffOrdinateCutoffCarrier.lean" "2026-08-30 checked-Lean session recorded by Agda owner; aggregate 8883 jobs" "not applicable" notApplicableIdentifier "not applicable" notApplicableIdentifier "not applicable" notApplicableIdentifier "not applicable" notApplicableIdentifier "repository return; exact external Zeta23Bridge repository path unresolved" "Every-cutoff split; finite-near carrier; farShellBound=18*A*log(|t|+4)/J+72*A/sqrt(J); literal D_off cutoff theorem." "Proof term not transported to Agda; finite signed cancellation remains open."
  ∷ source-coordinate riemannHypothesis "Lean Zeta23Bridge / Aristotle return" "PoleQuotientClusterMargin.lean; PoleQuotientBudgetCircularity.lean" "8889-job cross-prover return" "not applicable" notApplicableIdentifier "not applicable" notApplicableIdentifier "not applicable" notApplicableIdentifier "not applicable" notApplicableIdentifier "repository return; exact external project path unresolved" "Optional quantitative cluster lower-envelope donor + circularity no-go." "Not transported; Gamma too coarse; signed off unpaid; not mandatory in current direct route."
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
    "Whole problem=frozen four rows; Ibrahim traversal selects Round217/58 as the explanatory source parent beneath later R236/R237 routers."
    "1) literal CMP119 raw objects over finite beta history; 2) exact Section-2 predicate vocabulary/norm meanings indexed by those same objects; then selected semantics / CombinedRG / BC1."
    "running-coupling same-object identity; active CMP122 Section-2 transport; finite-cutoff UV stability; regular-E continuation compilers; many later functional-analysis compilers."
    "Primary-source snowball from CMP119 Eq.(2.23) and E/R/B/background clauses into the literal raw-object constructors and quantitative predicate definitions. Do not search generic RG theorems."
    false
  ∷ current-cut riemannHypothesis
    "Ibrahim traversal selects FinalNearLiteralKernel -> ExplicitCutoffNearFarAgdaTransport -> checked Lean cutoff return before fresh analysis."
    "Representation: proof-relevant Lean->Agda same-object split/far transport plus actual universal-pole-quotient finite-near equality. Analysis: phase-preserving signed finite-near/off payment and sharp same-taper Gamma, ultimately below actual ClusterResponse."
    "Lean every-J split/far modulus/finite near carrier; target modulation/cosine; reflection/parity donors; optional 8889 cluster margin; final contradiction/certificate compilers."
    "Recover the exact Zeta23Bridge theorem artifacts or prove their statements on the same Agda carrier; then trace the construction of the final universal pole taper and evaluate only the literal signed finite near carrier."
    false
  ∷ []

record ArchaeologyDiscipline : Set where
  constructor archaeology-discipline
  field
    consumerFirst : Bool
    ibrahimTypedFirstLink : Bool
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
canonicalDiscipline = archaeology-discipline true true true true true true true true true true true true true true true true

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
  "YM: Ibrahim path = later source router -> Round217 first raw coordinate -> Round58 raw-over-history carrier -> CMP119 Eq.(2.23) literal objects. Coupling and active CMP122 preservation are already paid. FIRST = literal raw objects; SECOND = state-indexed Section-2 predicate/norm vocabulary."
  "RH: Ibrahim path = FinalNearLiteralKernel -> ExplicitCutoffNearFarAgdaTransport -> Aug-30 checked Lean cutoff return. FIRST representation job includes proof-relevant same-object transport of the already-checked split/far theorem plus actual final pole-quotient finite-near equality. Fresh analysis begins at signed finite-near payment; Gamma precision follows."
  "NS retained for continuity only; active archaeology delegated."
  "GR/QFT retained as non-Clay same-object donor context only."
  "Primary/DOI/QID/Dewey/OEIS/link/date/commit/prover are provenance coordinates, not theorem payment. Ibrahim first-link/funnel centrality is navigation evidence only. Unresolved is preferable to invented metadata."
