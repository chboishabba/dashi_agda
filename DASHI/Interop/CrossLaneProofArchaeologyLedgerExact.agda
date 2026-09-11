module DASHI.Interop.CrossLaneProofArchaeologyLedgerExact where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.String using (String)
open import Agda.Builtin.List using (List; []; _∷_)

------------------------------------------------------------------------
-- CROSS-LANE PROOF ARCHAEOLOGY LEDGER
--
-- ONE easy-to-find/search/read owner for the proof archaeology that matters
-- to CURRENT completion work.
--
-- Search handles intentionally live here:
--   archaeology chronology date snowball attribution DOI QID OEIS source
--   same-object attempted-payment buried-donor Clay NS Navier-Stokes
--   YM Yang-Mills RH Riemann GR QFT R503 R504 R568 R573 R584
--   Round82 A1 B1 B2 C1 C2 certificate Bishop Bony Luo CMP109 CMP116 CMP119
--
-- RULE OF USE
--   * archaeology exists to reduce current proof debt, not to celebrate age;
--   * dates are repository lower bounds, never origin claims;
--   * old theorem names are searched by OUTPUT SHAPE, not round number;
--   * same-object transport is mandatory before historical reuse;
--   * source/QID/OEIS/status metadata never manufacture theorem payment;
--   * promisingly compressed frontier != Clay-paid theorem.
------------------------------------------------------------------------

data Lane : Set where
  navierStokes yangMills riemannHypothesis grQuantum : Lane

data HistoricalRole : Set where
  terminalConsumer directProducer producerTactic compiler representationWeld
  negativeControl diagnostic supersededOverpayment sourceTranscriptionDebt
  liveLevel2Theorem : HistoricalRole

data HistoricalClock : Set where
  constructionAncestry firstTypedAppearance formalConsolidation
  canonicalConsumerRecovery liveCutsetCompression : HistoricalClock

data HistoricalIdentityStatus : Set where
  sameObjectProved structuralAncestorOnly candidateAlias notSameObject : HistoricalIdentityStatus

data PaymentStatus : Set where
  paid conditionalPayment unpaid notApplicable : PaymentStatus

------------------------------------------------------------------------
-- START HERE: CURRENT CLAY-COMPLETION ROUTER.
------------------------------------------------------------------------

record ClayLaneRouter : Set where
  constructor clay-lane-router
  field
    routerLane : Lane
    mission currentWholeProblemCutset currentFirstLeaf : String
    alreadyOwned : String
    archaeologyDonor : String
    exactBridgeToTest : String
    doNotConfuseWithProof : String

open ClayLaneRouter public

nsClayRouter : ClayLaneRouter
nsClayRouter = clay-lane-router navierStokes
  "Finish unforced Clay A/B; forced C/D remains separate same-object/source reconstruction."
  "R503/R504 terminal chain with the direct R568 commutator-only reformulation; after standard scalar FTC and endpoint calibration, the new PDE leaf is a cutoff-uniform spacetime upper bound for the live global forcing/commutator full square."
  "R568 missingCutoffUniformLiveCommutatorSpacetimeBudget568; R504 still exposes missingLiteralR406SignedCrossPayment as the global first residual."
  "R567 exact transpose reduction collapses factoredFull to 4 * forcingFull; R573 exact weighted nested four-sign commutator; R580-R584 exact Bony routing and class-norm-to-Gram compilers."
  "2026-08-06 Luo/Bony annular four-class continuation: low-high, high-low and growing-annulus high-high are already analytically bounded on the older envelope carrier; comparable-shell remains explicit input."
  "Prove same-object/majorization transport from the old LH/HL/HH envelopes to R584 nested-slot class cells, then solve the surviving comparable class and outer spectator/spacetime aggregation."
  "Old Bony estimates are not automatically R584 payments; R584 currently says no live nested-slot class-norm payment is constructed and outer-weight/spectator spacetime remains open."

yangMillsClayRouter : ClayLaneRouter
yangMillsClayRouter = clay-lane-router yangMills
  "Finish the Jaffe-Witten existence + mass-gap problem on one literal compact-simple construction; do not optimize only the mass-gap subproblem."
  "Latest archaeology-recovered shortest NEW-analysis cutset is Round82 five leaves: A1 LiteralCompactSimplePositiveBeta; B1 UniformHeatHessianDebt; B2 UniformCovariantFiniteSpeed; C1 SameFamilyCompositeOPERemainder; C2 SameFamilyStressWardHamiltonian."
  "A1 source-facing determinant-first beta route is currently the sharpest finite/source leaf: positive Gaussian betaZ, finite-g interaction debt, and summable history-response debt on the same trajectory."
  "CMP116/CMP119 make the formerly separate summable continuum increment downstream of A1 plus published analysis; CMP109 already owns differentiated marked E^(2)/Pi exponential decay; finite orbit/Walsh/interval compilers are largely machine-checked."
  "2026-08-20 Round82 cut six independent new leaves to five; 2026-08-27 commit 85eb86c... recut A1 to determinant-first beta. Earlier Round77 five-job view is historical, not the sharpest current cutset."
  "For A1: identify the constrained-Gaussian D^2 log det / Ward trace scalar exactly, prove betaZ_j >= b_Z > 0, bound finite-g betaInt_j, and prove summable source-native history response. For B1/B2: use the SAME density/Hessian carrier; for C1/C2: SAME continuum family and reconstructed H."
  "Quantitative clustering is the hottest mass-gap Level-2 subproblem but is not the whole Clay cutset. Old gap=>clustering or clustering=>gap compilers cannot erase A1/C1/C2."

rhClayRouter : ClayLaneRouter
rhClayRouter = clay-lane-router riemannHypothesis
  "Finish RH by excluding every high off-line zero on the actual universal pole-quotient response; low/critical bridge remains independently required."
  "Final certificate plumbing is already owned: literal finite near fold -> proof-carrying finite upper -> actual nearResponseAt(J) -> source-order off-budget -> certified complement envelope."
  "Only strict high-side theorem remains on the balance-free context: cast(U + B_far(J)) + cast(D_Gamma(g_pole)) < cast(ClusterResponse(g_pole)), or the direct literal-near equivalent."
  "RiemannG2FinalCarrierFiniteSumCertificateExact and RiemannG2CertifiedNearUpperClusterResponseCompilerExact already transport finite certificates to the final scalar. Repository Bishop interval semantics already prove +,-,negation,multiplication and positive division soundly; four-corner multiplication handles two sign-straddling intervals constructively."
  "The reusable interval stack was built in the YM lane but is generic: Bishop four-corner multiplication, compositional expression intervals, and exact sine/cosine alternating-series enclosures."
  "Instantiate a thin RH atom/expression adapter for the literal oscillatory cosine cells and use existing proof-carrying finite-sum enclosure; then test/prove the strict certified envelope margin."
  "A finite certificate alone is not RH; the compiler itself records strictCertifiedEnvelopeBelowClusterStillRequired=true and finiteCertificateAloneProvesRH=false."

grQuantumRouter : ClayLaneRouter
grQuantumRouter = clay-lane-router grQuantum
  "Non-Clay cross-lane frontier retained because its variational/same-object machinery can donate proof patterns."
  "Literal sectors + Einstein variation on one common metric/action/stress carrier, then anomaly/UV/semiclassical recovery."
  "Same-action/common-stress sector inhabitants."
  "2026-05 matter/stress seam and 2026-08 common-action/common-total-stress weld."
  "Older Noether/action/stress owners and literal Maxwell/scalar/spinor/Higgs/YM sector variations."
  "Feed literal sector first variations into the common weld before inventing broader QG architecture."
  "Shared names, QIDs or flat compatibility do not prove same action/metric/stress or quantum gravity."

canonicalClayRouters : List ClayLaneRouter
canonicalClayRouters =
  nsClayRouter ∷ yangMillsClayRouter ∷ rhClayRouter ∷ grQuantumRouter ∷ []

------------------------------------------------------------------------
-- CANONICAL CURRENT CUTSETS.
------------------------------------------------------------------------

record CurrentCutset : Set where
  constructor current-cutset
  field
    cutsetLane : Lane
    cutsetDateBrisbane cutsetOwner cutsetShape : String
    cutsetStatus : PaymentStatus
    nextDecrement : String

open CurrentCutset public

currentCutsets : List CurrentCutset
currentCutsets =
  current-cutset navierStokes "2026-09-11"
    "NSTriadKNLiveCommutatorOnlyLeafABoundaryRound568Exact + R584 Bony bidi"
    "one live commutator spacetime budget; Bony route may reduce its nested class debt to old LH/HL/HH donors + comparable + outer aggregation"
    unpaid
    "test exact transport old annular LH/HL/HH -> R584 nested-slot classNormBudget; only then attack comparable/outer residual"
  ∷ current-cutset yangMills "2026-08-27"
    "BalabanClayHighestAlphaRound82FiveAnalyticLeafExact; commit 85eb86c2476e566bce0ebbba051629d94fb64d24"
    "A1 positive beta; B1 heat-Hessian debt; B2 covariant finite speed; C1 composite OPE remainder; C2 stress/Ward/Hamiltonian"
    unpaid
    "5->4 only by proving or rigorously eliminating one of A1/B1/B2/C1/C2; A1 determinant-first route is presently sharpest"
  ∷ current-cutset riemannHypothesis "2026-09-11"
    "RiemannG2CertifiedNearUpperClusterResponseCompilerExact"
    "proof-bearing finite upper already transports to final near scalar; strict certified envelope below ClusterResponse remains"
    unpaid
    "reuse Bishop/Taylor interval semantics to generate literal cell uppers, then prove the one strict aggregate margin"
  ∷ current-cutset grQuantum "2026-08-30"
    "endpoint-only common metric/action/total-stress weld"
    "same source carrier first, then post-weld quantum/semiclassical obligations"
    conditionalPayment
    "materialize literal sector inhabitants"
  ∷ []

------------------------------------------------------------------------
-- DATED ARCHAEOLOGY: LOWER BOUNDS, NOT ORIGIN CLAIMS.
------------------------------------------------------------------------

record DatedAnchor : Set where
  constructor dated-anchor
  field
    anchorLane : Lane
    dateBrisbane reference object : String
    clock : HistoricalClock
    role : HistoricalRole
    identity : HistoricalIdentityStatus
    interpretation : String

open DatedAnchor public

canonicalDatedAnchors : List DatedAnchor
canonicalDatedAnchors =
  dated-anchor navierStokes "2026-01-24"
    "dashiCFD 1cb1bb612c4061676a06e615f69bf282462c25cc"
    "initial vorticity/residual CFD carrier"
    constructionAncestry diagnostic candidateAlias
    "physical/computational NS ancestry; not automatically later Agda theorem identity"
  ∷ dated-anchor navierStokes "2026-01-28"
    "dashiCFD 7938f8282541b142e93cb2a7dadf32d83ca553b3"
    "signed support x sign x coherence x scale persistence before annihilation"
    constructionAncestry producerTactic candidateAlias
    "retain sign/coherence before destructive coarse-graining; later exact carrier requires a bridge"
  ∷ dated-anchor riemannHypothesis "2026-02-23"
    "AbelZeta.agda 8bf9e75a159e90c837836a998a43f55680ae66a9"
    "Abel contraction/limit zeta machinery"
    constructionAncestry diagnostic structuralAncestorOnly
    "analytic technology, not the later pole-response theorem"
  ∷ dated-anchor riemannHypothesis "2026-04-17"
    "ZetaVisualization.agda d59286c1eed63a1441b9243af031dbcf50f0edc5"
    "phase/zero-spacing visualization"
    constructionAncestry diagnostic notSameObject
    "phase-visible ancestry with explicit no-RH boundary"
  ∷ dated-anchor grQuantum "2026-05-12"
    "W4MatterStressEnergyInterfaceReceipt.agda 78c96a5c27795f3c3f7500bad71d4db72f53755e"
    "physical calibration -> MatterField -> T_mu_nu -> Einstein-law seam"
    firstTypedAppearance representationWeld structuralAncestorOnly
    "stress-energy seam predates later common-action normalization"
  ∷ dated-anchor yangMills "2026-05-17"
    "BalabanRGMassGapReceiptSurface.agda 81fc16c11af4f4152410ea9ce9269c68cc223387"
    "finite-depth positive gaps do not imply one positive depth-uniform epsilon"
    firstTypedAppearance terminalConsumer structuralAncestorOnly
    "modern YM uniformity debt already explicit in May"
  ∷ dated-anchor yangMills "2026-05-27"
    "YangMillsMassGapBoundary.agda 6e423ec962cc43ee1e678b490d253abb61ed8ef0"
    "physical gap boundary / continuum / spectrum transport"
    firstTypedAppearance terminalConsumer structuralAncestorOnly
    "July is refinement, not origin"
  ∷ dated-anchor navierStokes "2026-05-29"
    "NavierStokesRegularityTowerReceipt.agda bdd0801cc7e544304c52412ea1ccd0164904d12f"
    "finite-depth vorticity/enstrophy with BKM/nonlinear continuum wall"
    firstTypedAppearance terminalConsumer structuralAncestorOnly
    "finite-depth control is explicitly not continuum regularity"
  ∷ dated-anchor navierStokes "2026-05-30"
    "NSVorticityNoMechanismReceipt.agda f4320249ab968dc02331e6722cd722fd6744da64"
    "typed no-vorticity-mechanism / BKM still open"
    firstTypedAppearance negativeControl structuralAncestorOnly
    "typed theorem state outranks the loose commit message 'NS vorticity honestly closed'"
  ∷ dated-anchor riemannHypothesis "2026-07-19"
    "PR #100 / 78bdf33b725596bd0c1bc399a3e5bb78cc9bb14c"
    "first currently pinned explicit RH/Weil programme"
    formalConsolidation producerTactic structuralAncestorOnly
    "first explicit RH attack currently confirmed in this audit"
  ∷ dated-anchor yangMills "2026-07-20"
    "3933eaa7618e1565580a5ac67aed875dbd850d3f + 16e0a24d5766e93fb9cfee921dc9449dda36426e"
    "uniform cutoff-gap survival / uniform contraction chain"
    formalConsolidation producerTactic structuralAncestorOnly
    "strong attempted payment, not proof of same-family continuum clustering"
  ∷ dated-anchor navierStokes "2026-08-06"
    "NSTriadKNLuoAnnularFourClassContinuationExact / 2dc4c4af909fd83360cb039c6685f77f7b48ab45"
    "LH + HL + growing-annulus HH bounds; comparable supplied as explicit input"
    formalConsolidation producerTactic candidateAlias
    "high-value donor for R584 if exact slot/envelope majorization can be proved"
  ∷ dated-anchor yangMills "2026-08-20"
    "Round82 be702a432236171d115b9bc2b4ea1f8dc81d530c"
    "shortest new-analysis cutset 6 -> 5"
    liveCutsetCompression terminalConsumer sameObjectProved
    "A2 summable continuum increment removed as independent new theorem via CMP116/CMP119 source route"
  ∷ dated-anchor yangMills "2026-08-27"
    "Round82 85eb86c2476e566bce0ebbba051629d94fb64d24"
    "A1 recut to determinant-first positive-beta source route"
    liveCutsetCompression liveLevel2Theorem sameObjectProved
    "global Wilson/FP/Haar near/far route becomes fallback rather than mandatory first gate"
  ∷ dated-anchor grQuantum "2026-08-30"
    "PR #639 family"
    "common metric/action/total-QFT-stress weld"
    canonicalConsumerRecovery directProducer sameObjectProved
    "sharp live bridge; post-weld work remains"
  ∷ dated-anchor riemannHypothesis "2026-09-10"
    "PR #855"
    "generic high contradiction / certified-upper normalization"
    canonicalConsumerRecovery terminalConsumer sameObjectProved
    "certificate architecture compressed to the literal final high consumer"
  ∷ []

------------------------------------------------------------------------
-- ATTEMPTED PAYMENTS AND ROUTE PRUNING.
------------------------------------------------------------------------

record AttemptedPayment : Set where
  constructor attempted-payment
  field
    paymentLane : Lane
    dateOrWindow route intendedConsumer status reuseDecision : String
    paymentRole : HistoricalRole

open AttemptedPayment public

attemptedPayments : List AttemptedPayment
attemptedPayments =
  attempted-payment navierStokes "2026-01 -> current"
    "signed filament; shell/theta; gamma-gap; Schur/resolvent; nested commutator; Bony classes"
    "cutoff-uniform live physical spacetime payment"
    "many exact finite/representation reductions; live PDE bound remains unpaid"
    "prefer R584 old-donor transport and R568 live carrier; do not revive unrelated norm architecture"
    producerTactic
  ∷ attempted-payment navierStokes "2026-08-06"
    "Luo/Bony annular four-class continuation"
    "R584 nested slot class-norm payments"
    "LH/HL/HH paid only on older interaction/envelope carrier; comparable explicit; same-object bridge absent"
    "test three class bridges first; this is the most plausible hidden NS payment found"
    producerTactic
  ∷ attempted-payment yangMills "2026-07-20 -> 2026-08-19"
    "uniform gap survival; gap/clustering compilers; physical-gap master"
    "Clay mass-gap role"
    "downstream compilers strong, but not a substitute for same-family analytic construction"
    "reuse compilers only after B1/B2 or another accepted same-family producer pays clustering/gap"
    compiler
  ∷ attempted-payment yangMills "2026-08-20/27"
    "Round82 source-accepting five-leaf recut"
    "full Clay existence+mass-gap package"
    "current archaeology-recovered shortest honest NEW-analysis cutset"
    "use Round82, not Round73/77 counts, as current top-level search router"
    terminalConsumer
  ∷ attempted-payment riemannHypothesis "2026-02 -> 2026-08"
    "Abel; Weil; Hermitian; H_X->...->H_E"
    "high off-line contradiction"
    "useful diagnostics/producers but current representation debt is already compressed"
    "mine local phase inequalities only; final strict certified envelope is the load-bearing theorem"
    producerTactic
  ∷ attempted-payment riemannHypothesis "current"
    "final finite-sum certificate + certified upper compiler"
    "actual nearResponseAt(J) and ClusterResponse strict margin"
    "same-object certificate transport paid; strict margin unpaid"
    "reuse generic Bishop interval/taylor stack instead of creating another certificate arithmetic"
    directProducer
  ∷ []

------------------------------------------------------------------------
-- CROSS-LANE DONORS THAT SHOULD BE REUSED, NOT FORKED.
------------------------------------------------------------------------

record CrossLaneDonor : Set where
  constructor cross-lane-donor
  field
    donorFrom donorTo donorObject reusableContent requiredAdapter firewall : String

open CrossLaneDonor public

canonicalCrossLaneDonors : List CrossLaneDonor
canonicalCrossLaneDonors =
  cross-lane-donor
    "NS Luo/Bony lane"
    "NS R584/R568 Clay lane"
    "NSTriadKNLuoAnnularFourClassContinuationExact"
    "low-high, high-low and growing-annulus high-high square bounds under one shared critical/output envelope"
    "same-object/majorization from older interactions/envelopes to R584 nestedSlotCells584 classNormBudget582"
    "class-label similarity does not prove cell identity; comparable-shell and outer spectator/spacetime remain"
  ∷ cross-lane-donor
    "YM interval/certificate lane"
    "RH literal finite-cell certificate lane"
    "BalabanClayT4BishopFourCornerIntervalExact + BalabanClayT4BishopExpressionIntervalSemanticsExact + RealElementaryFunctionsAlternatingSeriesExact"
    "constructive sign-aware multiplication, compositional Bishop-real interval semantics, sine/cosine Taylor enclosures"
    "RH atom environment for literal phase/cosine cells plus exact fold attachment to FinalCarrierFiniteSumCertificate"
    "interval arithmetic proves enclosure, not the final strict ClusterResponse margin"
  ∷ cross-lane-donor
    "YM CMP109/CMP116/CMP119 source owners"
    "YM Round82 A1/B1/B2 construction"
    "published differentiated marked decay and normalized local expectation mechanisms"
    "source-owned E^(2)/Pi decay and compatible local normalized-response summability"
    "same-object identify source coordinates with the literal unified RG state and preserve the common small-coupling history"
    "source theorem import != physical instantiation; no circular gap/clustering premise"
  ∷ []

------------------------------------------------------------------------
-- ATTRIBUTION / DOI / QID / OEIS / SNOWBALL COORDINATES.
------------------------------------------------------------------------

record AttributionCoordinate : Set where
  constructor attribution-coordinate
  field
    attributionLane : Lane
    authorOrOwner titleOrObject primaryIdentity doi qid oeis : String
    relationship snowballState : String

open AttributionCoordinate public

canonicalAttribution : List AttributionCoordinate
canonicalAttribution =
  attribution-coordinate navierStokes
    "Jean-Michel Bony; Hajer Bahouri; Jean-Yves Chemin; Raphael Danchin"
    "Bony/paraproduct and Fourier-analysis source family"
    "source-local bibliography in NS Luo/Bony owners"
    "Bony 10.24033/asens.1404; BCD 10.1007/978-3-642-16830-7"
    "use authoritative source/QID owners; not guessed here"
    "notApplicable"
    "supports frequency-class estimates; does not by citation become R584 same-object payment"
    "acquire source first; pay exact nested-slot bridge separately"
  ∷ attribution-coordinate yangMills
    "Tadeusz Balaban"
    "CMP109/CMP116/CMP119/CMP122 lattice gauge RG source family"
    "DOI/source-local owners remain bibliographic authority"
    "CMP109 10.1007/BF01215223; other exact DOI coordinates remain source-local"
    "unresolved person QID retained unresolved; do not guess"
    "notApplicable"
    "source mathematical authority for RG-locality/decay mechanisms, not automatic Clay inhabitant"
    "source acquisition may precede same-object construction payment"
  ∷ attribution-coordinate riemannHypothesis
    "Bernhard Riemann / Polymath and DASHI source owners"
    "zeta/RH and de Bruijn-Newman source family"
    "Riemann source owners + scientific QID atlas"
    "Polymath heat-flow paper 10.1007/s40687-019-0193-1"
    "Q42299; Q205966; related verified identities remain metadata only"
    "notApplicable"
    "historical/source context; not final pole-response proof"
    "retain evidence append-only; same-carrier strict inequality pays conclusion"
  ∷ attribution-coordinate riemannHypothesis
    "Errett Bishop; Douglas Bridges; Marc Daumas; David Lester; Cesar Munoz"
    "constructive analysis / verified interval arithmetic donor"
    "generic arithmetic source, imported through existing repo owners"
    "10.1007/978-3-642-61667-9; 10.1109/TC.2008.213"
    "source-local; not needed for theorem identity"
    "notApplicable"
    "supports proof-producing interval arithmetic reused by RH"
    "arithmetic soundness is reusable; RH object identity and strict margin remain separate"
  ∷ attribution-coordinate grQuantum
    "DASHI W4 / GR-QFT closure owners"
    "matter/stress/common-action lineage"
    "repository commit/file identity"
    "notApplicable"
    "unresolved/source-local"
    "notApplicable"
    "repository representation/consumer ancestry"
    "same action/metric/stress transport remains conclusion-paying coordinate"
  ∷ []

------------------------------------------------------------------------
-- METADATA / STATUS FIREWALLS.
------------------------------------------------------------------------

record ArchaeologyDiscipline : Set where
  constructor archaeology-discipline
  field
    consumerFirst searchSemanticAliases searchSiblingRepos datesAreLowerBounds
      acquisitionOrderMayDifferFromPaymentOrder sameObjectBeforePromotion
      attemptedPaymentNotSuccessfulPayment compilerNotAnalyticProducer
      typedStateOutranksCommitMessage qidNotProof doiNotProof oeisNotProof
      attributionNotAuthority clayCompressedNotClayPaid : Bool

canonicalDiscipline : ArchaeologyDiscipline
canonicalDiscipline = archaeology-discipline
  true true true true true true true true true true true true true true

record HistoricalStatusMismatch : Set where
  constructor status-mismatch
  field mismatchLane : Lane
        mismatchDate looseLanguage typedState : String

canonicalStatusMismatches : List HistoricalStatusMismatch
canonicalStatusMismatches =
  status-mismatch navierStokes "2026-05-30"
    "commit message: NS vorticity honestly closed"
    "typed owner: vorticity mechanism absent; BKM control open; global regularity false; Clay promotion false"
  ∷ []

------------------------------------------------------------------------
-- GREP-FIRST PROOF CATALYST DASHBOARD.
------------------------------------------------------------------------

record ProofCatalystDashboard : Set where
  constructor dashboard
  field ns ym rh gr warning : String

canonicalDashboard : ProofCatalystDashboard
canonicalDashboard = dashboard
  "NS: R567 exact transpose collapse -> R568 one live commutator spacetime budget; R584 exact nested Bony routing; test Aug-06 Luo LH/HL/HH donor transport, then comparable + outer spectator/spacetime."
  "YM: current full Clay router = Round82 A1/B1/B2/C1/C2. A1 determinant-first positive beta is sharpest source-facing leaf; B1/B2 carry mass-gap/clustering; C1/C2 preserve local/OPE/stress/Hamiltonian submission requirements."
  "RH: final finite certificate -> actual nearResponse transport is already owned. Reuse generic Bishop four-corner + expression intervals + sin/cos alternating series; remaining theorem is the strict certified envelope below actual ClusterResponse."
  "GR/QFT: same action/metric/total-stress weld first; literal sectors next; anomaly/UV/semiclassical recovery afterwards."
  "Dates are lower bounds. QID/OEIS/DOI/attribution are provenance coordinates. Search old outputs by shape, prove same-object transport, and count Clay payment only when the exact live theorem is inhabited."
