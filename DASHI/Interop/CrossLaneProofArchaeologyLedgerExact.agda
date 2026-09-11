module DASHI.Interop.CrossLaneProofArchaeologyLedgerExact where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.String using (String)
open import Agda.Builtin.List using (List; []; _∷_)

------------------------------------------------------------------------
-- CROSS-LANE PROOF ARCHAEOLOGY LEDGER
------------------------------------------------------------------------
-- Canonical grep-first owner for current proof search.
-- Active lanes: Navier-Stokes + Yang-Mills + Riemann Hypothesis.
-- GR-QFT remains a continuity coordinate only.
--
-- The current search policy is the repo-native Ibrahim traversal policy:
-- explicit formulation owner -> typed dependency -> typed generalisation.
-- Source/QID/Dewey/OEIS/link/date coordinates may support or identify a node
-- but never replace the formulation owner or manufacture theorem payment.
--
-- NS correction (2026-09-11): C_direct is fully constructed as a live
-- pair/fibre/global/trajectory/integrated observable.  The unpaid authority is
-- its producer, minimized to the live R568 commutator-only spacetime budget.
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

nsRouter : ClayLaneRouter
nsRouter = clay-lane-router navierStokes
  "Finish periodic 3D NS arbitrary-data critical control on the literal live Galerkin trajectory without replacing the signed carrier by a premature positive majorant."
  "C_direct exists and is same-object welded: old R104 remainder F_N = literal R406 remainder integral = 4 * integratedDirectCompanion. R503 is the terminal consumer; R568 is the nearest new PDE producer interface."
  "Construct CommutatorOnlySpacetimeBudget568. Highest-alpha local splice: R573/R574 literal weighted nested four-helicity multiplier-difference carrier -> existing paired centered second-moment/six-three donor, while preserving signed cancellation before norms."
  "R310 closes a<->b inner-fibre swap pairing; R571 expands arbitrary raw velocity pairs into four exact R106 multiplier-difference channels; R573 carries the actual R294 weight through the outer slot before norms; R574 gives each channel the low-output bound; R575 collapses four scalar component majorants with no factor four; R572 compiles the R568 budget into the existing R503 DirectOffDiagonalBudget."
  "First test the exact Fourier/LP same-object transport needed to instantiate the old paired centered-kernel theorem on the literal R571/R573 carrier. Reuse the old paired second-order identity, second-moment bound, six-three arithmetic, and R89 two-derivative payment before falling back to R577 positive nested Schur."
  "Do not say C_direct is missing. Do not identify Fourier-leg swap a<->b with physical/kernel displacement y<->-y without a typed Fourier/LP transport. Do not replace the signed R294 weight by its positive envelope before swap/centering. Do not claim 369 proves the Gram/Rayleigh or R568 theorem."

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

grContinuityRouter : ClayLaneRouter
grContinuityRouter = clay-lane-router grQuantum "Non-Clay continuity coordinate." "Common action/metric/stress plus anomaly/UV/semiclassical recovery." "Literal sector inhabitants." "Common variational compilers exist." "Reuse only by explicit same-object transport." "Do not confuse GR/QFT compatibility with Clay YM completion."

canonicalRouters : List ClayLaneRouter
canonicalRouters = nsRouter ∷ ymRouter ∷ rhRouter ∷ grContinuityRouter ∷ []

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
  dated-anchor navierStokes "2026-06-25" "commit unresolved in this ledger" "docs/ns_triad_kn_369_high_high_gram_bridge.md" "369 finite triad/sign/profile classification + admissible high-high amplitude-profile packaging" constructionAncestry diagnostic structuralAncestor notApplicable "369 is a finite classification/support donor for the historical Gram lane. It does not prove the Rayleigh lower bound, cutoff-uniform R568 payment, or Clay completion."
  ∷ dated-anchor navierStokes "2026-07-20 -> 2026-07-25" "exact commits retained in source history" "NSPeriodicFarLowEnergyPairingCancellation + NSPeriodicFarLowExactCommutatorIdentity + NSPeriodicFarLowMultiplierDifferenceKernel" "tested shell cancellation -> exact signed multiplier-difference commutator K_diff" constructionAncestry directProducer sameObjectProved paid "Primitive signed commutator ancestry; later R26 imports these July owners directly."
  ∷ dated-anchor navierStokes "2026-08-05 -> 2026-08-06" "exact commits retained in source history" "NSTriadKNLuoFinitePairedCommutatorSecondOrderExact + NSTriadKNLuoFinitePairedCommutatorSecondMomentBoundExact + NSTriadKNLuoFiniteSixThreeCommutatorBudgetExact" "derivative-variation-aware paired second moment and six-three finite aggregation" constructionAncestry directProducer structuralAncestor paid "Existing theorem technology: signed paired identity, legitimate second-moment gain, and strong/weak shell arithmetic. Literal modern carrier transport is separate."
  ∷ dated-anchor navierStokes "2026-08 Round46-65" "source chronology retained in round owners" "R46/R47/R49/R62/R63/R64/R65 Com owners" "width-one support -> same/adjacent constants -> literal odd-P/Q commutator -> annular/common-hat -> factorized six-three Gram -> 133/256 bandwidth-one endpoint" formalConsolidation representationWeld structuralAncestor conditionalPayment "Physical re-realization of the commutator/six-three strategy. Old one-layer 133/256 endpoint is not the modern R568 spacetime theorem."
  ∷ dated-anchor navierStokes "2026-08 Round89" "source chronology retained in owner" "NSTriadKNStrongSixThreeWeightedCellRound89Exact.agda" "strong six-three branch pays two separation powers into weak envelope" buriedPaymentRecovery buriedDonor structuralAncestor paid "No cutoff-dependent constant; file explicitly leaves literal physical transfer -> firstBranchSquared same-object identification open."
  ∷ dated-anchor navierStokes "2026-08 Round92-106" "6afff8ef... -> later R106 tranche" "R92/R104/R105/R106 integrated signed architectures" "integrated signed danger/Waleffe accounting" constructionAncestry compiler structuralAncestor conditionalPayment "Multiple signed integration compilers existed before Gram/resolvent route; physical cutoff-uniform coverage/network-forcing payment remained input."
  ∷ dated-anchor navierStokes "2026-08 Round120/123" "7ba2a203e355f4cbb2b4888f6ae408f4c17ef58b -> 1ccc381d..." "NSTriadKNExternalPureCommutatorPartnerRound120Exact + NSTriadKNExternalPureCommutatorBonyWeldRound123Exact" "literal external Waleffe pair -> pure multiplier-difference commutator -> signed Bony classes" formalConsolidation representationWeld sameObjectProved paid "Representation and cancellation carrier closed; critical spacetime payment remained open."
  ∷ dated-anchor navierStokes "2026-08 Round290-304" "source chronology retained in owners" "R290-R304 resolvent/signed Gram owners" "resolvent-weighted signed Gram algebra and FAIL-CLOSED physical frontier" cutsetCompression compiler sameObjectProved conditionalPayment "R304 explicitly classifies physical signed integrated Gram as open after downstream algebraic plumbing closes."
  ∷ dated-anchor navierStokes "2026-08/09 R310 -> R325" "9061964646c8066488d546ee8a5a4ef1a9b25c23 for R325" "NSTriadKNNestedInnerSwapCommutatorRound310Exact + R325" "inner a/b output-fibre swap -> pure commutator fold; later same-object raw-kernel weld" buriedPaymentRecovery representationWeld sameObjectProved paid "R310 proves the literal a<->b involution on the physical inner fibre with no orbit quotient or division by two. This is not yet the same coordinate as kernel displacement y<->-y."
  ∷ dated-anchor navierStokes "2026-09-08 04:53 -> 05:03" "R496-R503 commit sequence in source history" "R496/R497/R498/R499/R500/R501/R503" "C_direct pair -> fibre -> global -> live trajectory -> integration -> terminal DirectOffDiagonalBudget consumer" consumerRecovery liveLevel2Theorem sameObjectProved conditionalPayment "C_direct is constructed. The only missing authority is an independent cutoff-uniform analytic budget."
  ∷ dated-anchor navierStokes "2026-09 current R568/R572/R577" "source chronology retained in owners" "NSTriadKNLiveCommutatorOnlyLeafABoundaryRound568Exact + NSTriadKNDirectLeafACompilerRound572Exact + NSTriadKNModernNestedSchurToCommutatorBidiRound577Exact" "nearest direct analytic producer -> compiler to R503; nested Schur remains sufficient fallback" cutsetCompression liveLevel2Theorem sameObjectProved unpaid "Live analytic leaf is CommutatorOnlySpacetimeBudget568. R572 compiles it to R503; R577 introduces no new estimate and requires row/column/signed-response/uniform-envelope receipts."
  ∷ dated-anchor navierStokes "2026-09 current R571-R575" "source chronology retained in owners" "R571/R573/R574/R575" "four exact helical multiplier-difference channels on the actual weighted nested carrier; local low-output bounds; scalar component majorants collapse without factor four" buriedPaymentRecovery representationWeld sameObjectProved conditionalPayment "Highest-alpha transplant point is before generic channel recombination: retain fixed helicity channels through centered pairing, then reuse old paired second-moment/six-three theorems if exact Fourier/LP transport is supplied."
  ∷ dated-anchor yangMills "2026-05-17" "81fc16c11af4f4152410ea9ce9269c68cc223387" "BalabanRGMassGapReceiptSurface.agda" "finite-depth gaps do not imply one cutoff-uniform positive gap" firstTypedAppearance terminalConsumer structuralAncestor unpaid "Uniformity debt already explicit."
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
  ∷ dated-anchor riemannHypothesis "2026-08-30 01:45:19" "39b05cd6f249927603d414c44817e7e0524264ef" "RiemannAristotleExplicitCutoffCarrierLeanReturnExact.agda" "Lean every-cutoff near/far split + explicit far-shell modulus + literal D_off cutoff" crossProverSync crossProverDonor candidateAlias conditionalPayment "8883-job return: FarShellCutoffTailBound.lean, NearFarCarrierSplit.lean, OffOrdinateCutoffCarrier.lean. Proof not transported to Agda."
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
  ibrahim-edge navierStokes "R503 DirectOffDiagonalBudget" "R568 CommutatorOnlySpacetimeBudget568" dependsOn "R572 proves the conditional compiler R568-style commutator budget -> literal R406 integral bound -> exact 4*C_direct budget -> R503." sameObjectProved unpaid
  ∷ ibrahim-edge navierStokes "R568 global forcing square" "R545/R567 weighted forcing/commutator full square" dependsOn "R567 collapses the amplitude half by transpose symmetry; R545 factors spectator rows through the weighted R294 commutator." sameObjectProved paid
  ∷ ibrahim-edge navierStokes "R294 weighted commutator" "R573 nested four-sign inner carrier" generalisesTo "R573 proves the actual weighted outer cell is exactly the nested fold of four R106 multiplier-difference channels before norms." sameObjectProved paid
  ∷ ibrahim-edge navierStokes "R573/R574 literal inner channels" "old paired centered second-moment + six-three donor" crossPollinatesWith "R310 supplies the a<->b physical-fibre involution, but the old y<->-y theorem lives in kernel/physical displacement coordinates. A typed Fourier/LP same-object transport is still required before instantiation." unresolvedIdentity unpaid
  ∷ ibrahim-edge navierStokes "old centered kernel displacement" "NSTriadKNLuoFiniteLittlewoodPaleyMomentIdentificationExact" supportedBy "Finite three-point bandpass prototype has mass=0, first moment=0, second moment=4^-q and exact centered second-difference action." sameObjectProved paid
  ∷ ibrahim-edge navierStokes "finite LP bandpass prototype" "selected smooth continuum LP kernel on official torus carrier" dependsOn "The old owner explicitly leaves Fourier support, scaling and moment-integral identification to the selected continuum kernel." unresolvedIdentity unpaid
  ∷ ibrahim-edge navierStokes "369 finite triad/sign/profile classifier" "historical high-high Gram/Rayleigh lane" crossPollinatesWith "369 packages finite dangerous-cell/sign/profile information only after the analytic margin carrier is fixed; it is a donor/diagnostic, not the theorem engine." structuralAncestor notApplicable
  ∷ ibrahim-edge yangMills "Round237 selected density semantics" "Round217 literal CMP119 raw objects" dependsOn "Later selected semantics requires a source family; Round217 identifies the first raw source coordinate." sameObjectProved unpaid
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
  source-coordinate navierStokes "Tosio Kato; Gustavo Ponce" "Commutator Estimates and the Euler and Navier-Stokes Equations" "Communications on Pure and Applied Mathematics 41 (1988), 891-907" "10.1002/cpa.3160410704" verifiedIdentifier "unresolved" unresolvedIdentifier "unresolved" unresolvedIdentifier "not applicable" notApplicableIdentifier "https://doi.org/10.1002/cpa.3160410704" "Primary classical donor for paired/commutator estimates." "Classical theorem does not identify the modern R571/R573 literal carrier automatically."
  ∷ source-coordinate navierStokes "Peter Constantin; Weinan E; Edriss S. Titi" "Onsager's Conjecture on the Energy Conservation for Solutions of Euler's Equation" "Communications in Mathematical Physics 165 (1994), 207-209" "10.1007/BF02099744" verifiedIdentifier "unresolved" unresolvedIdentifier "unresolved" unresolvedIdentifier "not applicable" notApplicableIdentifier "https://doi.org/10.1007/BF02099744" "Centered-kernel / commutator moment donor." "Moment theorem requires same-object LP/kernel transport before promotion to the modern physical carrier."
  ∷ source-coordinate navierStokes "Hajer Bahouri; Jean-Yves Chemin; Raphael Danchin" "Fourier Analysis and Nonlinear Partial Differential Equations" "Springer Grundlehren 343 (2011)" "10.1007/978-3-642-16830-7" verifiedIdentifier "unresolved" unresolvedIdentifier "unresolved" unresolvedIdentifier "not applicable" notApplicableIdentifier "https://doi.org/10.1007/978-3-642-16830-7" "LP/Bony/moment scaling donor." "Source authority does not replace literal torus-kernel realization."
  ∷ source-coordinate yangMills "Arthur Jaffe; Edward Witten" "Quantum Yang-Mills Theory" "official Clay Mathematics Institute problem description" "not assigned" notApplicableIdentifier "Arthur Jaffe Q370094; Edward Witten Q201513; Yang-Mills theory Q1192873" verifiedIdentifier "unresolved" unresolvedIdentifier "not applicable" notApplicableIdentifier "https://www.claymath.org/millennium/yang-mills-the-maths-gap/" "Terminal target / external identity coordinates." "Problem statement does not supply a DASHI producer."
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
  current-cut navierStokes
    "C_direct is fully constructed and same-object welded to the live R406 remainder; R568 is the nearest new PDE producer. The old signed/centered/six-three technology survives as donor mathematics and in several literal descendant representations."
    "Primary analytic leaf: CommutatorOnlySpacetimeBudget568. Immediate representation seam: literal R571/R573 fixed-helicity inner multiplier-difference channels -> old paired centered second-moment/six-three carrier on the SAME physical object. Exact a<->b fibre swap is paid; Fourier-leg swap -> kernel displacement y<->-y transport is not yet recovered."
    "R310 a/b swap; R571 four exact R106 channels; R573 weighted nested same-object weld; R574 low-output cell bounds; R575 no-factor-four scalar component-majorant collapse; R572 compiler to R503; R577 Schur fallback compiler. Historical paired second-order and second-moment theorems plus R89 two-derivative payment are already theorem-bearing."
    "Search the existing Fourier/LP bridge that maps the literal R571 multiplier-difference carrier to the selected continuum/torus centered-kernel displacement and branch data. Preserve fixed helicity channels and signed swap before applying R333 positive envelopes or any class-norm/Schur majorant. Keep 369 as finite classification/Gram donor only."
    false
  ∷ current-cut yangMills
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
  "NS: C_direct constructed and same-object welded; R568 is the live analytic leaf. Preserve the exact R294/R573 signed weighted commutator and fixed helicity channels. R310 pays a<->b fibre pairing; the next same-object seam is Fourier-leg swap -> selected LP/kernel y<->-y centered-displacement transport. Reuse paired second-order/second-moment/six-three/R89 donors before R577 positive Schur. 369 remains a finite classification/Gram donor, never theorem payment."
  "GR/QFT retained as non-Clay same-object donor context only."
  "Primary/DOI/QID/Dewey/OEIS/link/date/commit/prover are provenance coordinates, not theorem payment. Ibrahim first-link/funnel centrality is navigation evidence only. Unresolved is preferable to invented metadata."
