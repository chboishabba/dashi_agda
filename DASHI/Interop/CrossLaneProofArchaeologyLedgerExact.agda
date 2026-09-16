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
--
-- NS scheduling correction (2026-09-16): the authoritative four-lane control
-- routes B_comm/R568 as recovery+certification under an explicit recovery
-- assumption, while B_phase S2b2 is the strict current PDE-discovery frontier.
-- The R568 archaeology remains append-only donor/provenance for the SAME R406
-- remainder currency and must not be rewritten as a completed theorem.
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
  "Finish periodic 3D NS arbitrary-data critical control on the literal live Galerkin trajectory without replacing signed physical carriers by premature positive majorants."
  "C_direct exists and is same-object welded: old R104 remainder F_N = literal R406 remainder integral = 4 * integratedDirectCompanion. B_comm retains R568 -> R572 -> R503 as the minimal direct commutator producer chain, but the authoritative four-lane coordinator currently routes B_comm as recovery/certification and B_phase as active discovery."
  "Strict discovery leaf: B_phase S2b2, namely N_N(T) <= a D_N(T) + literalR406RemainderIntegral(N,T), equivalently a quantitative signed estimate on the SAME physical R98 packet layer-cake. PR #957 further recuts this as exact-shell collar plus genuinely separated remote packet flux."
  "B_phase S0/S1a/S2a are source-written; PR #948 source-writes the complete S2b0/S2b1 projected-pairing -> physical suffix/packet/layer-cake representation. B_comm owns R310/R571/R573/R574, the R294 weighted carrier, R545/R567 full-square factorization, C_direct, and R572/R503 compilers. PR #920 source-writes R571 -> opposite shifts -> Aug-5 paired second order -> absolute-magnitude sample -> scoped second-moment compiler. PR #945 records theorem-bearing Lean A1/A2 radial receipts and closes local Hermitian G0' while keeping Agda sample transport and G2/G1 state envelopes separate."
  "Follow PR #957's S2b2 collar/remote split first; do not reopen packet representation. For B_comm reconstruction, recover L0-L6 and certification receipts before inventing mathematics: the modern-to-Aug-5 scalarization is already source-written, A1/A2 radial mathematics has external Lean receipts, local A2 rational curvature geometry is source-written, and remaining Gate-A transport/state envelopes must be searched by exact object shape. Keep R577 positive Schur as fallback only."
  "Do not say C_direct is missing. Do not infer B from forced C/D. External PDE body force is WrongType for the internal R406/R568 state-dependent companion. Do not promote Lean theorem receipts into Agda sample/kernel receipts. Do not identify Fourier-leg swap a<->b with kernel displacement y<->-y without typed realization. Do not replace signed R294 weights by positive envelopes before swap/centering. Do not claim 369 proves the Gram/Rayleigh, S2b2 or R568 theorem."

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
  dated-anchor navierStokes "2026-06-25" "commit unresolved in this ledger" "docs/ns_triad_kn_369_high_high_gram_bridge.md" "369 finite triad/sign/profile classification + admissible high-high amplitude-profile packaging" constructionAncestry diagnostic structuralAncestor notApplicable "369 is a finite classification/support donor for the historical Gram lane. It does not prove the Rayleigh lower bound, cutoff-uniform R568 payment, S2b2, or Clay completion."
  ∷ dated-anchor navierStokes "2026-07-20 -> 2026-07-25" "exact commits retained in source history" "NSPeriodicFarLowEnergyPairingCancellation + NSPeriodicFarLowExactCommutatorIdentity + NSPeriodicFarLowMultiplierDifferenceKernel" "tested shell cancellation -> exact signed multiplier-difference commutator K_diff" constructionAncestry directProducer sameObjectProved paid "Primitive signed commutator ancestry; later R26 imports these July owners directly."
  ∷ dated-anchor navierStokes "2026-08-05 -> 2026-08-06" "exact commits retained in source history" "NSTriadKNLuoFinitePairedCommutatorSecondOrderExact + NSTriadKNLuoFinitePairedCommutatorSecondMomentBoundExact + NSTriadKNLuoFiniteSixThreeCommutatorBudgetExact" "derivative-variation-aware paired second moment and six-three finite aggregation" constructionAncestry directProducer structuralAncestor paid "Existing theorem technology: signed paired identity, legitimate second-moment gain, and strong/weak shell arithmetic. Literal modern carrier transport is separate."
  ∷ dated-anchor navierStokes "2026-08 Round46-65" "source chronology retained in round owners" "R46/R47/R49/R62/R63/R64/R65 Com owners" "width-one support -> same/adjacent constants -> literal odd-P/Q commutator -> annular/common-hat -> factorized six-three Gram -> 133/256 bandwidth-one endpoint" formalConsolidation representationWeld structuralAncestor conditionalPayment "Physical re-realization of the commutator/six-three strategy. Old one-layer 133/256 endpoint is not the modern R568 spacetime theorem."
  ∷ dated-anchor navierStokes "2026-08 Round89" "source chronology retained in owner" "NSTriadKNStrongSixThreeWeightedCellRound89Exact.agda" "strong six-three branch pays two separation powers into weak envelope" buriedPaymentRecovery buriedDonor structuralAncestor paid "No cutoff-dependent constant; file explicitly leaves literal physical transfer -> firstBranchSquared same-object identification open."
  ∷ dated-anchor navierStokes "2026-08 Round92-106" "6afff8ef... -> later R106 tranche" "R92/R104/R105/R106 integrated signed architectures" "integrated signed danger/Waleffe accounting" constructionAncestry compiler structuralAncestor conditionalPayment "Multiple signed integration compilers existed before Gram/resolvent route; physical cutoff-uniform coverage/network-forcing payment remained input."
  ∷ dated-anchor navierStokes "2026-08 Round120/123" "7ba2a203e355f4cbb2b4888f6ae408f4c17ef58b -> 1ccc381d..." "NSTriadKNExternalPureCommutatorPartnerRound120Exact + NSTriadKNExternalPureCommutatorBonyWeldRound123Exact" "literal external Waleffe pair -> pure multiplier-difference commutator -> signed Bony classes" formalConsolidation representationWeld sameObjectProved paid "Representation and cancellation carrier closed; critical spacetime payment remained open."
  ∷ dated-anchor navierStokes "2026-08 Round290-304" "source chronology retained in owners" "R290-R304 resolvent/signed Gram owners" "resolvent-weighted signed Gram algebra and FAIL-CLOSED physical frontier" cutsetCompression compiler sameObjectProved conditionalPayment "R304 explicitly classifies physical signed integrated Gram as open after downstream algebraic plumbing closes."
  ∷ dated-anchor navierStokes "2026-08/09 R310 -> R325" "9061964646c8066488d546ee8a5a4ef1a9b25c23 for R325" "NSTriadKNNestedInnerSwapCommutatorRound310Exact + R325" "inner a/b output-fibre swap -> pure commutator fold; later same-object raw-kernel weld" buriedPaymentRecovery representationWeld sameObjectProved paid "R310 proves the literal a<->b involution on the physical inner fibre with no orbit quotient or division by two. This is not yet the same coordinate as kernel displacement y<->-y."
  ∷ dated-anchor navierStokes "2026-09-08 04:53 -> 05:03" "R496-R503 commit sequence in source history" "R496/R497/R498/R499/R500/R501/R503" "C_direct pair -> fibre -> global -> live trajectory -> integration -> terminal DirectOffDiagonalBudget consumer" consumerRecovery liveLevel2Theorem sameObjectProved conditionalPayment "C_direct is constructed. The only missing authority on that direct route is an independent cutoff-uniform analytic budget."
  ∷ dated-anchor navierStokes "2026-09 current R568/R572/R577" "source chronology retained in owners" "NSTriadKNLiveCommutatorOnlyLeafABoundaryRound568Exact + NSTriadKNDirectLeafACompilerRound572Exact + NSTriadKNModernNestedSchurToCommutatorBidiRound577Exact" "nearest direct analytic producer -> compiler to R503; nested Schur remains sufficient fallback" cutsetCompression liveLevel2Theorem sameObjectProved unpaid "CommutatorOnlySpacetimeBudget568 is the minimal B_comm analytic leaf; current four-lane control routes B_comm as recovery/certification rather than the strict discovery queue. R572 compiles R568 to R503; R577 introduces no new estimate."
  ∷ dated-anchor navierStokes "2026-09 current R571-R576" "source chronology retained in owners" "R571/R573/R574/R575/R576" "four exact helical multiplier-difference channels on the actual weighted nested carrier; local low-output bounds; channelwise majorant collapse; fixed-four vector recombination fallback" buriedPaymentRecovery representationWeld sameObjectProved conditionalPayment "Preserve fixed helicity channels through signed pairing before generic positive recombination. R576 pays only fixed-four recombination, not variable inner-fibre aggregation or R568."
  ∷ dated-anchor navierStokes "2026-09-11 20:46 AEST" "ac999027b1a0da2ac193525e898ad870be3be92f -> 01551ab768a8f36fccb4d63a3661b1441568a2f6 -> 7753f9ce9976f75d520fb623f8f12c9eded826d0" "NSTriadKNOfficialPeriodicTorusCharacterIntegralExact + NSTriadKNR571HomochiralRadialIncrementSpecializationExact + R569 aggregate" "Seam A official torus-character authority boundary plus Seam B rational R571 homochiral radial same-object weld" formalConsolidation representationWeld sameObjectProved conditionalPayment "Seam B is source-written plumbing: R571 ++/-- curl gaps -> R311 signed radial difference -> Round27 radial multiplier commutator. Seam A constructs the existing TorusCharacterIntegral from explicit standard-imported normalized Haar/exponential-character authority and reuses machine-checked finite character algebra."
  ∷ dated-anchor navierStokes "2026-09-14 11:03 -> 2026-09-15 09:02 AEST" "PR #920 head 1d458fb1bc5503e67e5e7923474d4e1b88e40716; merge 3833c652ae2291f48f00210d55773e10ecb8f384" "NSTriadKNR571OppositeShiftSecondMomentRealizationExact + NSTriadKNR571CanonicalSecondMomentMagnitudeAdapterExact + NSTriadKNLuoScopedPairedSecondMomentBudgetExact" "R571 literal +y/-y carrier -> Aug-5 signed second-order defect -> post-cancellation absolute-magnitude sample -> finite-family scoped second-moment compiler" buriedPaymentRecovery representationWeld sameObjectProved conditionalPayment "The modern-to-Aug-5 scalarization splice is source-written. No physical A1/A2/G2/G1 envelope constants, inner-fibre gain, R568 or Clay theorem are manufactured. No exact-head Agda receipt was claimed by PR #920."
  ∷ dated-anchor navierStokes "2026-09-15" "PR #945 merge ce7e68a514b088ddd6850f50eb66ef52eb7c302a; dashi_lean4 receipt commit 7f60fa116f59a8f3f860fe53c13782ffc0d67ed6" "NSTriadKNR571LeanGateAEnvelopeReceiptExact + NSTriadKNR571HermitianScalarizedOppositePairExact" "Lean radial A1/A2 theorem receipts plus local Hermitian G0' vector->scalar same-object weld" crossProverSync crossProverDonor candidateAlias conditionalPayment "Lean proves radial A1/A2 on the periodic-B real carrier, but the receipt creates neither an Agda kernel receipt nor Agda sample transport. G0' is source-written locally; G2/G1 and R568 remain open."
  ∷ dated-anchor navierStokes "2026-09-15" "PR #937 merge 20ddc053cc7d98be40cb60c9dafcdccf43bca695" "Docs/roadmaps/NSProofControl20260915.md + FourLaneProofProgramExact" "authoritative A/B/C/D coordinator: B_comm recovery/certification; B_phase strict discovery" sourceFrontierCompression liveLevel2Theorem sameObjectProved conditionalPayment "Scheduling authority changed without deleting R568 archaeology. B_phase S0/S1a/S2a are source-written; S1b remains conditional on ordinary calculus."
  ∷ dated-anchor navierStokes "2026-09-16" "current proof-control receipt on live control baseline" "NSProofControlABCD20260916ReceiptExact + NSProofControlABCD20260916ReceiptRegression" "typed A/B/C/D control receipt: mission implemented, any-one Clay criterion separated, B leaf recut to S2b2d1b2, C/D source alignment closed, no internal all-four or prize promotion" sourceFrontierCompression diagnostic sameObjectProved conditionalPayment "Bookkeeping receipt only. It synchronizes the prose control plane with imported typed status owners; it does not add a PDE estimate, does not transport C/D into B, and keeps released field/forcing -> DASHI Fourier/R406 reconstruction open."
  ∷ dated-anchor navierStokes "2026-09-15 -> 2026-09-16" "PR #948 head 779cc3f40b43ceb076b3e2f1dfeb400b3396e041" "NSTriadKNR104GlobalLayerCakePhysicalPacketWeldExact + S2b adapter tranche" "literal critical production -> exact R104 BandTransfer -> radially sorted support -> canonical suffix -> SAME normalized R98 upper-shell packet layer-cake" sourceFrontierCompression representationWeld sameObjectProved paid "S2b0/S2b1 representation is source-written without absolute majorant, Schur/Wiener loss or R406 estimate. The remaining nonlinear theorem is S2b2 quantitative signed packet-flux payment. Source-written only; no exact-head Agda receipt asserted."
  ∷ dated-anchor navierStokes "2026-09-16 current" "PR #957" "NSTriadKNPacketBoundaryFluxComplementRound98Exact + adjacent-shell spectral-gap no-go" "same R98 complement-flux antisymmetry; exact-shell collar + remote upper packet recut" sourceFrontierCompression producerTactic sameObjectProved unpaid "F(selected)+F(complement selected)=0 is source-written finite sign geometry. Adjacent shellIndex does not imply positive Euclidean spectral gap; S2b2 remains open. Next route is signed exact-shell collar plus genuinely separated remote packet. No Agda compiler receipt observed."
  ∷ dated-anchor navierStokes "2026-09 current P1/P2/P3" "source owners on current baseline" "NSTriadKNFixedOutputPairDifferenceDebtExact + NSTriadKNFixedOutputPairDifferenceAggregateExact + NSTriadKNFixedOutputPairDifferencePaymentExact + NSTriadKNCenteredPartnerDifferenceAdapterExact + NSTriadKNCenteredPartnerSlotDefectExact + R128 + PR916 collision witness" "finite Complex3 complete-graph pair-difference identity, literal fixed-output R574 pair-norm aggregate, lower-separation -> same-output Gram-debt compiler, exact amplitude-increment branch donor, norm-four slot-defect identity, and radial/Pluecker guardrails" buriedPaymentRecovery representationWeld sameObjectProved conditionalPayment "Finite algebra, same-object R574 aggregate, conditional payment compiler, R205/R574 amplitude-increment same-object adapter, and ||B_alpha-B_beta||^2=4 slot-defect normalization are closed. R128 polynomial Pluecker identity is closed but ordered drop/payment is false. PR916 closes a concrete same-slot collision witness, so incidence-label-only radial/Pluecker coercivity is not a safe lower weld. Physical radial/Pluecker-to-slot-defect payment remains false."
  ∷ dated-anchor navierStokes "2026-09-15 current A2" "source owners on merged control baseline" "NSTriadKNR571CenteredRadialProductBridgeExact + NSTriadKNR571RadialCurvatureBoundaryExact" "division-free centered Euclidean-radius curvature payment for homochiral R571 Taylor remainder" buriedPaymentRecovery directProducer sameObjectProved conditionalPayment "Local rational A2 geometry and ordered radial-denominator payment are source-written; exact sign/absolute-value/stepMagnitude transport into the Gate-A minusRemainderCurvatureBound sample remains open."
  ∷ dated-anchor navierStokes "2026-09 released C/D BIDI" "PR #922 dependency atlas; later C/D integration surfaces" "NSClayFourAlternativeReleasedProofBidiExact + released-proof dependency atlas" "released forced C/D proofs as source/external theorem authority and structural donors" crossProverSync crossProverDonor structuralAncestor conditionalPayment "Forced body force is WrongType for unforced B's internal R406/R568 companion. First DASHI released-proof representation seam remains literal released field/candidate -> DASHI Fourier coefficients. Signed-component, zero-mask, exact physical recombination and equality-transport patterns are donor technology only."
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
  ibrahim-edge navierStokes "B_phase S2b1 exact physical packet layer-cake" "B_phase S2b2 quantitative signed packet-flux / literal-R406 payment" dependsOn "PR #948 closes the representation chain. PR #957 adds complement-flux antisymmetry and recuts S2b2 into exact-shell collar plus genuinely separated remote packet; the quantitative estimate remains new analysis." sameObjectProved unpaid
  ∷ ibrahim-edge navierStokes "R503 DirectOffDiagonalBudget" "R568 CommutatorOnlySpacetimeBudget568" dependsOn "R572 proves the conditional compiler R568-style commutator budget -> literal R406 integral bound -> exact 4*C_direct budget -> R503. Current coordinator schedules this B_comm lane as recovery/certification." sameObjectProved unpaid
  ∷ ibrahim-edge navierStokes "R568 global forcing square" "R545/R567 weighted forcing/commutator full square" dependsOn "R567 collapses the amplitude half by transpose symmetry; R545 factors spectator rows through the weighted R294 commutator." sameObjectProved paid
  ∷ ibrahim-edge navierStokes "R294 weighted commutator" "R573 nested four-sign inner carrier" generalisesTo "R573 proves the actual weighted outer cell is exactly the nested fold of four R106 multiplier-difference channels before norms." sameObjectProved paid
  ∷ ibrahim-edge navierStokes "R573/R571 opposite-shift carrier" "Aug-5 paired second-order defect" generalisesTo "PR #920 source-writes the exact +y/-y Taylor carrier and identifies the signed R571 scalar with the historical paired second-order defect." sameObjectProved paid
  ∷ ibrahim-edge navierStokes "Aug-5 signed paired second-order defect" "absolute-magnitude PairedSecondMomentSample" generalisesTo "NSTriadKNLuoPairedSecondOrderAbsoluteMagnitudeBridgeExact takes absolute values only after the signed second-order identity; no physical envelope is introduced." sameObjectProved paid
  ∷ ibrahim-edge navierStokes "absolute-magnitude R571 sample family" "scoped finite paired-second-moment compiler" generalisesTo "NSTriadKNLuoScopedPairedSecondMomentBudgetExact repairs the historical quantifier shape: envelope bounds are required only on samples in the declared finite family." sameObjectProved conditionalPayment
  ∷ ibrahim-edge navierStokes "Lean Gate-A A1/A2 radial theorems" "Agda R571 physical sample envelope" externallyIdentifiedBy "dashi_lean4 commit 7f60fa... contains theorem-bearing A1/A2 proofs, but the Agda receipt explicitly records sample transport=false and kernel receipt=false." candidateAlias unpaid
  ∷ ibrahim-edge navierStokes "R571 local centered radial curvature geometry" "Gate-A minusRemainderCurvatureBound sample" dependsOn "Division-free A2 product/denominator payment is source-written; exact sign/absolute-value/stepMagnitude transport into the sample record remains open on the current baseline." sameObjectProved unpaid
  ∷ ibrahim-edge navierStokes "G2 finite path-difference donor + G1 modal-energy donor" "R571 state-derivative envelope" crossPollinatesWith "Gate-A crosswalk locates the donors but explicitly keeps G2 physical gradient crosswalk, G1 shifted coefficient envelope and complete state envelope false." structuralAncestor unpaid
  ∷ ibrahim-edge navierStokes "official periodic Haar/exponential-character authority" "TorusCharacterIntegral + finite weighted-increment multiplier carrier" generalisesTo "OfficialPeriodicTorusCharacterIntegralExact constructs the existing torus character record from explicit standard-imported analytic authority and reuses the finite character multiplier bridge instead of restating Fourier algebra." sameObjectProved conditionalPayment
  ∷ ibrahim-edge navierStokes "R571 homochiral signedEigenvalue gap" "R311/Round27 signed radial multiplier commutator" generalisesTo "R571HomochiralRadialIncrementSpecializationExact closes the rational ++/-- same-object carrier weld; no gain estimate or heterochiral promotion is introduced." sameObjectProved paid
  ∷ ibrahim-edge navierStokes "old centered kernel displacement" "NSTriadKNLuoFiniteLittlewoodPaleyMomentIdentificationExact" supportedBy "Finite three-point bandpass prototype has mass=0, first moment=0, second moment=4^-q and exact centered second-difference action." sameObjectProved paid
  ∷ ibrahim-edge navierStokes "finite LP bandpass prototype" "selected smooth continuum LP kernel on official torus carrier" dependsOn "The old owner explicitly leaves Fourier support, scaling and moment-integral identification to the selected continuum kernel; current official torus adaptor records the analytic authority as standardImported rather than machine checked." unresolvedIdentity conditionalPayment
  ∷ ibrahim-edge navierStokes "released forced periodic D construction" "unforced periodic B internal R406/R568/S2b2 carrier" crossPollinatesWith "D supplies signed-component, zero-mask, physical recombination, exact differential identity and EqOn-transport proof-design donors. Its external PDE body force is a different equation class and does not pay B." notSameObject notApplicable
  ∷ ibrahim-edge navierStokes "dashifine/dashiCFD Fourier implementations" "official periodic Fourier convention regression" crossPollinatesWith "Executable phase/convolution/curl semantics are regression/provenance donors only; they do not supply the Haar/Bochner theorem, R571 multiplier identity, radial gain, S2b2 or R568 payment." structuralAncestor notApplicable
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
    "Authoritative current coordinator is the four-lane B-phase/B-comm split. C_direct remains fully constructed and same-object welded to R406; R568 remains the minimal direct B_comm analytic leaf, but B_comm is scheduled as recovery/certification. B_phase is the strict current discovery lane."
    "Primary nonlinear leaf: S2b2 quantitative signed physical packet-flux estimate N_N(T) <= a D_N(T) + literalR406RemainderIntegral(N,T). PR #957 recuts it into an exact-shell signed collar plus a genuinely separated remote packet after disproving naive adjacent-shell Euclidean coercivity. Then S3 initial-critical ceiling and S4 retained-viscosity calibration. Parallel B_comm recovery still lacks observed certification and, on the merged baseline, Gate-A Agda sample/state envelopes remain fail-closed despite radial Lean receipts."
    "B_phase S0/S1a/S2a plus PR #948 S2b0/S2b1 exact packet/suffix/layer-cake representation; R104/R98 finite sign and packet-flux algebra. B_comm owns C_direct, R568/R572/R503 compiler chain, R310/R571/R573/R574, R545/R567, PR #920 exact modern-to-Aug-5 paired-second-moment scalarization, #945 local Hermitian G0' and Lean A1/A2 receipts, and local A2 division-free curvature geometry. R577 positive Schur remains fallback."
    "Discovery: follow PR #957 collar/remote S2b2 route and search only SAME-object quantitative producers for those two pieces. Recovery: reconstruct/certify B_comm L0-L6 before reopening analysis; search exact Agda A1/A2 sample transport and G2/G1 vector/state envelopes by object shape. Keep released C/D as typed donor/BIDI lanes and preserve forced/unforced WrongType boundaries."
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
  "NS: current authority = four-lane coordinator. B_phase is strict discovery: S2b0/S2b1 representation is source-written through the SAME R98 packet layer-cake; S2b2 is open and PR #957 recuts it into signed exact-shell collar + separated remote packet after an explicit adjacent-shell spectral-gap no-go. B_comm retains C_direct/R568 ancestry as recovery/certification: PR #920 source-writes R571 -> Aug-5 paired second moment, PR #945 records Lean A1/A2 receipts + local G0', and local A2 rational curvature geometry is source-written, but Agda sample/state envelopes and R568 remain fail-closed unless recovered/certified. Preserve signed components before positive majorization; released forced C/D are donors, not B payment."
  "GR/QFT retained as non-Clay same-object donor context only."
  "Primary/DOI/QID/Dewey/OEIS/link/date/commit/prover are provenance coordinates, not theorem payment. Cross-prover theorem receipts are not local kernel receipts. Ibrahim first-link/funnel centrality is navigation evidence only. Unresolved is preferable to invented metadata."
