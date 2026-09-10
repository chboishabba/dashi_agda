module DASHI.Interop.CrossLaneProofArchaeologyLedgerExact where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.String using (String)
open import Agda.Builtin.List using (List; []; _∷_)

------------------------------------------------------------------------
-- CROSS-LANE PROOF ARCHAEOLOGY LEDGER
--
-- ONE easy-to-find/search/read navigation and proof-search owner for
-- Navier-Stokes, Yang-Mills, Riemann Hypothesis, and GR/QFT unification.
--
-- Search handles intentionally live in this one file:
--   archaeology / chronology / date / snowball / attribution / DOI / QID /
--   OEIS / source / same-object / consumer / producer / compiler / frontier /
--   NS / Navier-Stokes / YM / Yang-Mills / RH / Riemann / GR / QFT.
--
-- Dates are evidenced repository LOWER BOUNDS, never origin claims.
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

data IdentifierStatus : Set where
  verifiedIdentifier unresolvedIdentifier notApplicableIdentifier : IdentifierStatus

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
  clocked-anchor navierStokes "2026-01-24" constructionAncestry exactCommitDate
    "chboishabba/dashiCFD commit 1cb1bb612c4061676a06e615f69bf282462c25cc"
    "initial CFD/DASHI vorticity, residual-closure, codec, and sandbox carrier"
    diagnostic candidateAlias
    "Physical/computational NS ancestry exists from the initial dashiCFD commit; this is not automatically the later Agda signed-transfer theorem carrier."
  ∷ clocked-anchor navierStokes "2026-01-28" constructionAncestry exactCommitDate
    "chboishabba/dashiCFD commit 7938f8282541b142e93cb2a7dadf32d83ca553b3; docs/signed_filament_annihilation.md; authored 2026-01-27 UTC"
    "signed support x sign x coherence x scale-persistence annihilation/coarse-graining operator"
    producerTactic candidateAlias
    "The signed/coherence-before-coarse-graining design predates later NS round labels by months. It is structural ancestry unless exact same-object transport is separately proved."
  ∷ clocked-anchor riemannHypothesis "2026-02-23" constructionAncestry exactCommitDate
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
    "physical calibration -> MatterField -> T_mu_nu -> discrete Einstein-law obligation"
    representationWeld structuralAncestorOnly
    "The stress-energy seam that later becomes the common-action/common-stress consumer is already typed by 12 May."
  ∷ clocked-anchor grQuantum "2026-05-17" firstTypedAppearance exactCommitDate
    "dashi_agda commit 81fc16c11af4f4152410ea9ce9269c68cc223387; file history DASHI/Physics/Closure/GRQFTTerminalCompositionBoundary.agda"
    "GR/QFT terminal composition: discrete-to-smooth, AQFT, stress-energy bridge, receipt composition"
    terminalConsumer structuralAncestorOnly
    "The broad terminal programme therefore predates the July QG cutset and August common-action normalization."
  ∷ clocked-anchor yangMills "2026-05-17" firstTypedAppearance exactCommitDate
    "dashi_agda commit 81fc16c11af4f4152410ea9ce9269c68cc223387; file history DASHI/Physics/Closure/BalabanRGMassGapReceiptSurface.agda"
    "Balaban RG -> finite gap / mass-gap receipt surface with explicit uniform-in-depth gap debt"
    producerTactic structuralAncestorOnly
    "The May surface already distinguishes pointwise finite-depth positivity from one positive depth-uniform lower bound. Later clustering machinery is a candidate payment route for that older uniformity debt."
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
  ∷ clocked-anchor navierStokes "2026-05-30" firstTypedAppearance exactCommitDate
    "dashi_agda commit f4320249ab968dc02331e6722cd722fd6744da64; NSVorticityNoMechanismReceipt.agda"
    "explicit no-vorticity-mechanism / BKM-still-open theorem state"
    negativeControl structuralAncestorOnly
    "Typed theorem state keeps carrier-native vorticity mechanism, uniform BKM control, global regularity and Clay promotion false despite looser historical commit-message language."
  ∷ clocked-anchor navierStokes "2026-06-04" constructionAncestry exactCommitDate
    "chboishabba/dashiCFD commit 125e52e04bed4042890d95db5d5371104ba1aafe and descendants"
    "3D periodic incompressible truth + Leray/vorticity shells + shell-enstrophy + flux/dissipation theta diagnostics"
    diagnostic candidateAlias
    "The physical NS carrier and flux/dissipation barrier were tested before later Agda rounds; absolute-flux theta is not silently identified with the later signed theorem."
  ∷ []

------------------------------------------------------------------------
-- REPOSITORY ANCESTRY LOWER BOUNDS.
------------------------------------------------------------------------

record RepositoryAncestryLowerBound : Set where
  constructor repository-lower-bound
  field
    repository earliestConfirmedDateBrisbane evidenceReference relevance : String
    originClaim : Bool

open RepositoryAncestryLowerBound public

repositoryAncestryLowerBounds : List RepositoryAncestryLowerBound
repositoryAncestryLowerBounds =
  repository-lower-bound "chboishabba/dashiCFD" "2026-01-24"
    "commit 1cb1bb612c4061676a06e615f69bf282462c25cc; January signed-filament refinement at 7938f8282541b142e93cb2a7dadf32d83ca553b3"
    "Earliest currently pinned NS physical/computational ancestry in this audit; exact later theorem identity is not inferred." false
  ∷ repository-lower-bound "chboishabba/dashi_agda" "2026-02-23"
    "AbelZeta file history 8bf9e75a159e90c837836a998a43f55680ae66a9"
    "Earliest currently pinned lane-specific dashi_agda mathematical ancestor in this audit; not an origin claim." false
  ∷ repository-lower-bound "chboishabba/dashiCORE" "2026-03-05"
    "commit 684b899b3b05b4fbbf6799fe368c5da6551f0c13 and descendants"
    "Cross-programme sibling-repo ancestry; lane-specific same-object lineage still requires file-level recovery." false
  ∷ []

------------------------------------------------------------------------
-- ATTRIBUTION / DOI / QID / OEIS COORDINATES.
--
-- Identity coordinates are intentionally non-promoting:
-- QID != DOI != theorem identity != source authority != proof payment.
-- OEIS is carried as a first-class slot because cross-programme snowballs use
-- it, but these four Clay/unification lane anchors generally do not require an
-- OEIS sequence. 'not applicable' is stronger than inventing one.
------------------------------------------------------------------------

record AttributionCoordinate : Set where
  constructor attribution-coordinate
  field
    attributionLane : Lane
    sourceAuthorOrOwner sourceTitleOrObject primarySourceIdentity : String
    doi doiStatus qid qidStatus oeis oeisStatus : String
    sourceRole attributionRelationship snowballPaymentState : String

open AttributionCoordinate public

canonicalAttributionCoordinates : List AttributionCoordinate
canonicalAttributionCoordinates =
  attribution-coordinate navierStokes
    "Johl Brown / chboishabba"
    "dashiCFD docs/signed_filament_annihilation.md"
    "repository commit 7938f8282541b142e93cb2a7dadf32d83ca553b3"
    "not applicable" "notApplicable"
    "Q201321" "verified related concept: Navier-Stokes equations; not publication identity"
    "not applicable" "notApplicable"
    "repository construction ancestry"
    "candidate structural ancestor of later signed/coherence NS work"
    "retain evidence; do not pay exact same-object theorem identity without transport"
  ∷ attribution-coordinate navierStokes
    "Jean Leray / Eberhard Hopf / Beale-Kato-Majda source families"
    "Leray-Hopf weak-solution and BKM regularity ancestry"
    "exact consuming bibliography remains primary"
    "varies by exact publication" "source-local"
    "Q441143; Q86070; Q1335673; Q506133; Q201321" "verified related identities per in-repo scientific QID atlas"
    "not applicable" "notApplicable"
    "external mathematical ancestry"
    "theorem/source context for May typed NS wall"
    "citation does not manufacture the missing uniform continuum estimate"
  ∷ attribution-coordinate yangMills
    "Tadeusz Balaban"
    "Averaging Operations for Lattice Gauge Theories"
    "Communications in Mathematical Physics 98 (1985), 17-51"
    "10.1007/BF01211042" "verified in-repo bibliography"
    "unresolved" "unresolved person QID; deliberately not guessed"
    "not applicable" "notApplicable"
    "primary mathematical source"
    "source family for literal lattice-gauge/RG constructions"
    "source identity may be acquired before same-family continuum-clustering payment; acquisition order != conclusion-payment order"
  ∷ attribution-coordinate yangMills
    "Arthur Jaffe / Edward Witten"
    "Quantum Yang-Mills Theory / Clay Millennium problem statement"
    "official Clay Mathematics Institute problem statement"
    "not applicable" "notApplicable"
    "Q370094; Q201513; Q727000" "verified related identities per in-repo scientific QID atlas"
    "not applicable" "notApplicable"
    "terminal problem authority"
    "defines the physical/mathematical target, not a DASHI producer"
    "terminal authority cannot fill missing continuum clustering or physical-spectrum identification"
  ∷ attribution-coordinate riemannHypothesis
    "Bernhard Riemann"
    "Ueber die Anzahl der Primzahlen unter einer gegebenen Groesse / 1859 zeta source"
    "original 1859 publication identity"
    "not applicable" "historical publication without DOI coordinate here"
    "Q42299; Q205966" "verified related identities: Riemann and Riemann hypothesis"
    "not applicable" "notApplicable"
    "primary historical source ancestry"
    "zeta/RH identity context"
    "does not pay the later universal pole-quotient strict response theorem"
  ∷ attribution-coordinate riemannHypothesis
    "DASHI internal Abel-zeta owner"
    "DASHI/Analysis/AbelZeta.agda"
    "commit 8bf9e75a159e90c837836a998a43f55680ae66a9"
    "not applicable" "notApplicable"
    "Q205966" "related RH concept only"
    "not applicable" "notApplicable"
    "repository analytic ancestry"
    "regularisation/limit methodology; structural ancestor only"
    "retain as donor vocabulary; do not promote to same-object pole-response proof"
  ∷ attribution-coordinate grQuantum
    "DASHI W4 / GR-QFT closure owners"
    "W4MatterStressEnergyInterfaceReceipt -> GRQFTTerminalCompositionBoundary"
    "dashi_agda commits 78c96a5c27795f3c3f7500bad71d4db72f53755e and 81fc16c11af4f4152410ea9ce9269c68cc223387"
    "not applicable" "repository-object coordinate"
    "unresolved" "GR/QFT expansion explicitly remained next work in the in-repo scientific QID atlas"
    "not applicable" "notApplicable"
    "repository representation/consumer ancestry"
    "physical carrier -> matter -> stress-energy -> Einstein consumer ancestry"
    "later common-action/common-stress weld still requires exact shared metric/action transport"
  ∷ []

------------------------------------------------------------------------
-- HISTORICAL ALIAS / SAME-OBJECT BRIDGES.
------------------------------------------------------------------------

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
    "January dashiCFD signed filament/support/coherence family + June shell flux/theta family"
    "dashi_agda signed physical transfer -> uniform critical-cone payment"
    "candidate signed/coherence physical ancestry; neither January projector semantics nor absolute-flux theta is definitionally the later signed analytic carrier" candidateAlias
  ∷ historical-alias riemannHypothesis
    "February AbelZeta + April phase/spacing visualization"
    "September universal pole-quotient literal response"
    "analytic/phase ancestry exists, but carrier identity and final strict theorem are not inherited" structuralAncestorOnly
  ∷ historical-alias yangMills
    "May Balaban RG finite-depth mass-gap receipt + physical gap boundary"
    "September same-family quantitative continuum clustering consumer"
    "same programme and terminal target; old finite/RG gap route explicitly exposes uniformity debt but does not itself inhabit continuum clustering" structuralAncestorOnly
  ∷ historical-alias grQuantum
    "May physical matter/stress-energy interface + GRQFT terminal composition"
    "August endpoint-only common action/metric/stress weld"
    "later route sharpens an old stress-energy target to one common variational carrier" structuralAncestorOnly
  ∷ []

------------------------------------------------------------------------
-- STATUS-LANGUAGE ARCHAEOLOGY.
-- Historical prose/commit messages are evidence, not theorem state.
------------------------------------------------------------------------

record HistoricalStatusMismatch : Set where
  constructor status-mismatch
  field
    mismatchLane : Lane
    mismatchDateBrisbane repositoryReference historicalLanguage typedState rule : String

open HistoricalStatusMismatch public

canonicalHistoricalStatusMismatches : List HistoricalStatusMismatch
canonicalHistoricalStatusMismatches =
  status-mismatch navierStokes "2026-05-30"
    "commit f4320249ab968dc02331e6722cd722fd6744da64"
    "commit message includes 'NS vorticity honestly closed'"
    "NSVorticityNoMechanismReceipt keeps carrier-native vorticity mechanism absent, BKM control open, uniform vorticity control false, global smooth regularity false, Clay promotion false"
    "typed theorem state outranks loose historical status language"
  ∷ []

------------------------------------------------------------------------
-- DATED FORMAL CONSOLIDATION / RECOVERY CHRONOLOGY.
------------------------------------------------------------------------

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
    "First currently confirmed explicit RH programme boundary; February ancestry is analytic technology, not yet this RH route."
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

------------------------------------------------------------------------
-- BURIED-DONOR WINDOWS: SEARCH BY OUTPUT SHAPE, NOT ROUND NUMBER.
------------------------------------------------------------------------

record BuriedDonorWindow : Set where
  constructor donor-window
  field
    donorLane : Lane
    fromDate toDate searchByOutputShape whyThisWindow : String

open BuriedDonorWindow public

canonicalBuriedDonorWindows : List BuriedDonorWindow
canonicalBuriedDonorWindows =
  donor-window yangMills "2026-05-17" "2026-08-20"
    "uniform / infimum / refinement-stable / correlation-decay / transfer-semigroup-decay / physical-gap / coercivity theorem transportable to SAME continuum Schwinger family"
    "The May Balaban/RG surface already names the finite-depth-to-uniform-gap quantifier debt; search attempted payments before paying later Row-C machinery again."
  ∷ donor-window riemannHypothesis "2026-02-23" "2026-08-31"
    "phase-sensitive zeta response / reflection-paired oscillatory inequality / one-sided target-centred upper bound / Abel or contraction limit transport"
    "February Abel-zeta machinery is analytic ancestry, while the first explicit RH programme boundary currently pinned is 19 July. Search donors without pretending those carriers are already identical."
  ∷ donor-window grQuantum "2026-05-12" "2026-08-30"
    "same action variation / metric perturbation / stress-energy identity across literal sectors"
    "Stress-energy interface predates the terminal composition and the August common-action weld."
  ∷ donor-window navierStokes "2026-01-24" "current"
    "signed physical production/transfer retained before absolute value or destructive coarse-graining -> cutoff-uniform spacetime/potential payment"
    "January dashiCFD already has signed/coherence construction ancestry; May explicitly types the continuum BKM/nonlinear wall; later exact Agda rounds should be searched as refinements/compositions, not assumed origin."
  ∷ []

------------------------------------------------------------------------
-- LIVE FRONTIERS.
------------------------------------------------------------------------

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
  "January signed/coherence ancestry; May enstrophy/vorticity tower; Abel/telescope/Gram/resolvent/critical-cone transports"
  "dashiCFD signed filament/truth/theta; signed commutator; spectator resolvent; packet/danger"
  "do not destroy sign/coherence before payment; historical similarity does not prove exact R294/R541/R573 identity"
  "search January-current sibling-repo and pre-round aliases for signed transfer + dissipation/potential comparison in the correct order"

yangMillsFrontier : LiveFrontier
yangMillsFrontier = live-frontier yangMills
  "same reconstructed continuum family: quantitative connected-correlation decay -> positive physical spectral gap"
  "quantitative continuum clustering on SAME Schwinger family; separately identify candidate decay rate with physical spectrum"
  "May finite-depth uniformity wall and gap boundary; OS reconstruction; clustering-to-gap; dense-core; lattice-to-physical exponent transport"
  "May Balaban RG; coercivity/reflection positivity; CMP109/CMP116 influence; Langevin/Dyson; cluster expansion; polymer norm"
  "finite/RG decay or generic Clustered is not same-family continuum clustering"
  "search May-August history for attempted quantifier exchange/uniformisation before paying Row-C again"

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

------------------------------------------------------------------------
-- SNOWBALL / ARCHAEOLOGY DISCIPLINE.
------------------------------------------------------------------------

record ArchaeologyDiscipline : Set where
  constructor archaeology-discipline
  field
    consumerFirst roundNumbersAreOnlyOneIndex searchSemanticAliases
      searchSiblingRepositories distinguishHistoricalClocks
      earliestConfirmedDateIsOnlyLowerBound compilerDoesNotCreateAnalyticContent
      producerTacticIsNotMandatoryRoute sameObjectBeforePromotion
      negativeResultsPruneRoutes datesRemainProvenanceNotProof
      acquisitionOrderMayDifferFromPaymentOrder
      attributionDoesNotManufactureAuthority
      qidDoesNotManufactureBibliographicIdentity
      oeisDoesNotManufactureTheoremIdentity
      typedTheoremStateOutranksLooseStatusLanguage : Bool

canonicalArchaeologyDiscipline : ArchaeologyDiscipline
canonicalArchaeologyDiscipline = archaeology-discipline
  true true true true true true true true true true true true true true true true

------------------------------------------------------------------------
-- COMPACT PROOF-CATALYST DASHBOARD.
------------------------------------------------------------------------

record ProofCatalystDashboard : Set where
  constructor proof-catalyst-dashboard
  field nsTarget ymTarget rhTarget grQuantumTarget historicalWarning : String

canonicalProofCatalystDashboard : ProofCatalystDashboard
canonicalProofCatalystDashboard = proof-catalyst-dashboard
  "NS: January signed/coherence physical ancestry -> May explicit continuum wall -> signed physical transfer -> uniform spacetime/potential payment"
  "YM: May finite-depth gap/uniformity wall -> continuum physical Schwinger family -> quantitative clustering -> physical spectrum"
  "RH: February analytic ancestry -> July first explicit RH programme -> literal oscillatory zero response -> uniform strict high margin"
  "GR/QFT: May physical matter/stress seam -> literal sector + Einstein variations -> same action/metric/stress weld -> anomaly/UV/semiclassical QG recovery"
  "Dates are lower bounds. QID/OEIS/DOI are identity/provenance coordinates, not proof. Acquisition may snowball out of dependency order; theorem payment may not. Typed theorem state outranks loose commit-message status. Search old outputs by shape and prove same-object transport before reuse."
