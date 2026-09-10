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
-- START HERE.  Search handles intentionally live in this one file:
--   archaeology / chronology / date / snowball / attribution / DOI / QID /
--   OEIS / source / same-object / consumer / producer / compiler / frontier /
--   attempted-payment / buried-donor / NS / Navier-Stokes / YM / Yang-Mills /
--   RH / Riemann / GR / QFT.
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

------------------------------------------------------------------------
-- START-HERE FOUR-ROW INDEX.
--
-- This is the intended first read/search surface.  It gives one compact row
-- per lane: earliest ancestry, first typed wall, route history, current
-- consumer, and the exact next proof-search output shape.
------------------------------------------------------------------------

record CanonicalLaneIndex : Set where
  constructor lane-index
  field
    indexedLane : Lane
    earliestConfirmedAncestry firstTypedWall historicalRouteSummary : String
    currentCanonicalConsumer currentLevel2Target exactNextSearch : String
    sourceMetadataOwners : String

open CanonicalLaneIndex public

nsIndex : CanonicalLaneIndex
nsIndex = lane-index navierStokes
  "2026-01-24 dashiCFD initial vorticity/residual carrier; 2026-01-28 signed support x sign x coherence x scale-persistence operator"
  "2026-05-29/30 finite-depth vorticity/enstrophy tower plus explicit BKM/nonlinear continuum wall"
  "January signed/coherence experiments -> May typed uniformity wall -> July profile/cross-shell uniform routes -> August signed triad/commutator/refinement -> September spectator-resolvent/nested signed composition"
  "critical-cone / physical high-frequency regularity consumer"
  "cutoff-uniform signed physical transfer/production -> spacetime or potential-budget payment"
  "find a same-object signed production/transfer inequality that survives before absolute value/coarse-graining and pays the uniform spacetime/potential consumer"
  "DASHI/Physics/Closure/NavierStokesSourceEntityQidBindingsExact.agda; DASHI/Physics/Closure/NavierStokesCitationIdentityAuditExact.agda; Docs/support/live/ScientificReferenceQidAtlas.md"

yangMillsIndex : CanonicalLaneIndex
yangMillsIndex = lane-index yangMills
  "2026-05-17 BalabanRGMassGapReceiptSurface: finite-depth positive gaps do not imply one positive depth-uniform lower bound"
  "2026-05-27 YangMillsMassGapBoundary: reflection/transfer positivity, spectral isolation, continuum stability, physical-spectrum transport"
  "May uniform-gap debt -> May 30 4D Balaban reframe -> July finite/RG and uniform-contraction routes -> July/Aug clustering compilers and producer families -> August uniform physical-gap master -> September quantitative-clustering consumer recovery"
  "same reconstructed continuum Schwinger family: quantitative connected-correlation decay -> positive physical spectral gap"
  "quantitative continuum clustering on SAME Schwinger family, then candidate decay-rate -> physical-spectrum identification"
  "search old uniform/infimum/refinement-stable/correlation/transfer-semigroup/coercivity outputs for a theorem already landing on the same reconstructed continuum family before paying Row-C machinery again"
  "DASHI/Physics/YangMills/SourceEntityQidBindingsExact.agda; DASHI/Wikimedia/ScientificCitationQidBindingsExact.agda; Docs/support/live/ScientificReferenceQidAtlas.md"

rhIndex : CanonicalLaneIndex
rhIndex = lane-index riemannHypothesis
  "2026-02-23 AbelZeta analytic contraction/limit machinery; 2026-04-17 phase/zero-spacing visualization ancestry"
  "2026-07-19 first currently confirmed explicit Riemann/Weil/explicit-formula programme boundary"
  "February analytic regularisation -> April phase diagnostics -> July Weil/explicit formula -> August Hermitian/interference and pole-quotient families -> September direct/certified high contradiction normalization"
  "forall high off-line zero: contradiction on the actual universal pole-quotient response"
  "uniform strict bound on the literal reflection-paired oscillatory response; executable form is proof-bearing one-sided finite-cell upper certificates"
  "find a phase-sensitive one-sided literal integral/sum bound that lands exactly on cellResponse/nearResponse; do not revive scalar/absolute-envelope/determinant routes unless they transport to this carrier"
  "DASHI/Analysis/RiemannSourceEntityQidBindingsExact.agda; DASHI/Analysis/RiemannExtendedSourceEntityQidBindingsExact.agda; Docs/support/live/ScientificReferenceQidAtlas.md"

grQuantumIndex : CanonicalLaneIndex
grQuantumIndex = lane-index grQuantum
  "2026-05-12 W4 physical calibration -> MatterField -> T_mu_nu -> Einstein-law obligation seam"
  "2026-05-17 GRQFTTerminalCompositionBoundary broad discrete-to-smooth/AQFT/stress-energy terminal consumer"
  "May physical matter/stress seam -> July conditional Einstein-Hilbert/shared-action/authority cutset -> August total-QFT-stress correction and endpoint-only common metric/action/stress weld"
  "one common physical metric/action language whose QFT and Einstein variations yield the SAME stress-energy source"
  "literal sector same-action/same-stress inhabitants, then anomaly-free quantum dynamics + renormalized continuum amplitudes + semiclassical GR/backreaction"
  "search existing Maxwell/scalar/spinor/Higgs/YM/Noether/action/stress owners for literal sector first-variation inhabitants on the common metric before broad quantum-gravity construction"
  "DASHI/Physics/Closure/GRQFTTerminalCompositionBoundary.agda; DASHI/Physics/Closure/EinsteinHilbertVariationConditional.agda; DASHI/Physics/QFT/StressEnergyBridgeReceiptSurface.agda; Docs/support/live/ScientificReferenceQidAtlas.md"

canonicalLaneIndex : List CanonicalLaneIndex
canonicalLaneIndex = nsIndex ∷ yangMillsIndex ∷ rhIndex ∷ grQuantumIndex ∷ []

------------------------------------------------------------------------
-- CLOCKED ARCHAEOLOGY ANCHORS.
------------------------------------------------------------------------

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
  ∷ clocked-anchor yangMills "2026-05-30" formalConsolidation exactCommitDate
    "dashi_agda commit 3ebb95536316159e92d89abc621b17538027ff20"
    "programme reframe: 1+1D trivially confining; 4D product lattice + Balaban is the correct Clay-facing route"
    diagnostic structuralAncestorOnly
    "Programme-state evidence that the 4D Balaban path was selected before July source-faithful reconstruction; it does not itself pay the gap."
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
-- OEIS is first-class/searchable but 'not applicable' is preferable to an
-- invented sequence identifier.
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
    "Polymath Project"
    "Effective approximation of heat flow evolution of the Riemann xi function, and a new upper bound for the de Bruijn-Newman constant"
    "DOI/arXiv source identity retained by Riemann source owner"
    "10.1007/s40687-019-0193-1" "verified in-repo QID atlas"
    "Q2000812; Q205966; Q1078285; Q5080476" "verified related identities: Polymath/RH/de Bruijn/Newman"
    "not applicable" "notApplicable"
    "external analytic/RH source"
    "de Bruijn-Newman/heat-flow source context; not automatic pole-response producer"
    "citation/source acquisition cannot replace literal same-carrier response inequality"
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
    "unresolved" "GR/QFT source-QID expansion remains source-local; no QID guessed here"
    "not applicable" "notApplicable"
    "repository representation/consumer ancestry"
    "physical carrier -> matter -> stress-energy -> Einstein consumer ancestry"
    "later common-action/common-stress weld still requires exact shared metric/action transport"
  ∷ []

------------------------------------------------------------------------
-- AUTHORITATIVE SOURCE/METADATA OWNER INDEX.
--
-- The archaeology ledger points to these owners instead of duplicating their
-- semantics.  This keeps one easy search surface while preserving authority.
------------------------------------------------------------------------

record AuthoritativeOwnerIndex : Set where
  constructor owner-index
  field
    ownerLane : Lane
    sourceQidOwner bibliographyOrAuditOwner statusOrConsumerOwner rule : String

open AuthoritativeOwnerIndex public

canonicalAuthoritativeOwnerIndex : List AuthoritativeOwnerIndex
canonicalAuthoritativeOwnerIndex =
  owner-index navierStokes
    "DASHI/Physics/Closure/NavierStokesSourceEntityQidBindingsExact.agda"
    "DASHI/Physics/Closure/NavierStokesCitationIdentityAuditExact.agda; Docs/support/live/ScientificReferenceQidAtlas.md"
    "NavierStokesRegularityTowerReceipt.agda; NSVorticityNoMechanismReceipt.agda; current R503/critical-cone owners"
    "exact publication/criterion identity remains DOI/bibliography-local; QID cannot close Package A"
  ∷ owner-index yangMills
    "DASHI/Physics/YangMills/SourceEntityQidBindingsExact.agda"
    "DASHI/Wikimedia/ScientificCitationQidBindingsExact.agda; Docs/support/live/ScientificReferenceQidAtlas.md"
    "BalabanRGMassGapReceiptSurface.agda; YangMillsMassGapBoundary.agda; current quantitative-clustering consumer"
    "QID annotates source surface; DOI/official source remains bibliographic identity; QID cannot close Clay YM"
  ∷ owner-index riemannHypothesis
    "DASHI/Analysis/RiemannSourceEntityQidBindingsExact.agda; DASHI/Analysis/RiemannExtendedSourceEntityQidBindingsExact.agda"
    "Docs/support/live/ScientificReferenceQidAtlas.md"
    "RiemannZetaProgramBoundary.agda; current universal pole-quotient/high-contradiction owners"
    "DOI/arXiv/repository remains source identity; QID cannot create certificate replay or RH proof"
  ∷ owner-index grQuantum
    "no dedicated canonical GR/QFT source-QID owner promoted here; use source-local owners and the shared scientific QID atlas"
    "Docs/support/live/ScientificReferenceQidAtlas.md; docs/conditional_gr_quantum_closure_ladder.md"
    "W4MatterStressEnergyInterfaceReceipt.agda; GRQFTTerminalCompositionBoundary.agda; EinsteinHilbertVariationConditional.agda; QFT/StressEnergyBridgeReceiptSurface.agda"
    "shared labels or QIDs do not establish same action, same metric, same stress tensor, or quantum gravity"
  ∷ []

------------------------------------------------------------------------
-- ATTEMPTED PAYMENT LINEAGE.
--
-- This is the most proof-catalytic historical view: what route was tried,
-- which consumer it was supposed to pay, and why archaeology should or should
-- not reuse it now.
------------------------------------------------------------------------

record AttemptedPayment : Set where
  constructor attempted-payment
  field
    paymentLane : Lane
    paymentDateBrisbane repositoryReference attemptedRoute : String
    paymentRole : HistoricalRole
    intendedConsumer paymentStatus reuseDecision : String

open AttemptedPayment public

canonicalAttemptedPayments : List AttemptedPayment
canonicalAttemptedPayments =
  attempted-payment navierStokes "2026-01-28"
    "dashiCFD 7938f8282541b142e93cb2a7dadf32d83ca553b3"
    "signed filament/support/coherence persistence before annihilation"
    producerTactic
    "physical retention of coherent signed structure across scales"
    "empirical/operational ancestor, not a PDE uniform estimate"
    "reuse the signed/coherence ordering idea only through an explicit same-object bridge"
  ∷ attempted-payment navierStokes "2026-05-29"
    "NavierStokesRegularityTowerReceipt.agda"
    "finite-depth enstrophy/vorticity/BKM/Serrin tower"
    terminalConsumer
    "global smooth regularity"
    "correctly exposes missing uniform continuum payment"
    "treat as early consumer diagnosis; do not mistake finite-depth control for producer"
  ∷ attempted-payment navierStokes "2026-07-18"
    "commit 5b007992df368beb69f0a3350c87ebf8f969d39f / PR #14 family"
    "profile-uniform gamma-gap reduction"
    producerTactic
    "uniform shell/profile control"
    "useful structural uniformisation, not by itself the final physical spacetime payment"
    "search its output for transport into current signed physical consumer before re-proving uniformity machinery"
  ∷ attempted-payment yangMills "2026-05-17"
    "BalabanRGMassGapReceiptSurface.agda"
    "finite-depth positive gaps plus explicit missing depth-uniform epsilon"
    terminalConsumer
    "continuum physical mass gap"
    "uniformity debt explicitly identified, not paid"
    "use as the earliest precise statement of the modern YM obstruction"
  ∷ attempted-payment yangMills "2026-07-20"
    "commits 3933eaa7618e1565580a5ac67aed875dbd850d3f + 16e0a24d5766e93fb9cfee921dc9449dda36426e; PR #248 family"
    "uniform cutoff mass-gap survival / uniform contraction through mass-gap chain"
    producerTactic
    "continuum mass-gap survival"
    "historically strong sufficient route; later archaeology still recovered quantitative continuum clustering as the cleaner canonical consumer"
    "inspect whether any theorem inside this chain directly yields same-family correlation decay before rebuilding Row-C"
  ∷ attempted-payment yangMills "2026-07-29"
    "commit c4910cdcde12c764c818545fb658bb93171c471b"
    "clustering -> transfer-gap spectral cutset"
    compiler
    "physical spectral gap from quantitative clustering"
    "downstream compiler essentially available; does not create clustering"
    "reuse; do not spend proof-search effort downstream until clustering is paid"
  ∷ attempted-payment yangMills "2026-08-05"
    "f6759d1f4bf5ac94da33906717147ce33eafe363 + 4f5fc7e4d941d324534b543c1103129432106943"
    "lattice-to-physical clustering exponent + dense-core clustering-to-full-gap"
    compiler
    "transport quantitative decay to physical spectrum"
    "matures downstream transport while upstream clustering remains load-bearing"
    "reuse as compiler once same-family quantitative clustering is inhabited"
  ∷ attempted-payment yangMills "2026-08-19"
    "commit 1a7075aa7c6343ff48a5b0ee7e49ec46bd841342 / Round64"
    "collapse terminal gap/loss budget to uniform physical gap master"
    terminalConsumer
    "uniform physical gap"
    "consumer compression; still not evidence of upstream quantitative clustering producer"
    "retain as historical consumer normalization, but current proof search starts one step earlier at clustering"
  ∷ attempted-payment riemannHypothesis "2026-02-23"
    "AbelZeta.agda at 8bf9e75a159e90c837836a998a43f55680ae66a9"
    "contraction-parameter regularisation and canonical q -> 1 limit"
    diagnostic
    "analytic continuation / regularised zeta values"
    "analytic technology only; not an RH proof route"
    "reuse only if an exact transport into current oscillatory cell response is shown"
  ∷ attempted-payment riemannHypothesis "2026-07-19"
    "PR #100 / 78bdf33b725596bd0c1bc399a3e5bb78cc9bb14c"
    "Weil positivity / explicit-formula theorem ladder"
    producerTactic
    "Riemann hypothesis via spectral/Weil positivity"
    "major formal consolidation; later route exploration moved to literal phase/pole response"
    "retain as alternate producer family/compiler context, not mandatory architecture"
  ∷ attempted-payment riemannHypothesis "2026-08-21"
    "Hermitian/top-down tranche beginning cb78f41b6f32955cc0121eb61dd8d78a6d133e54"
    "retained pair / mixed interference / Poisson / alpha-square coercivity"
    producerTactic
    "exclude off-line zero through Hermitian/interference energy"
    "valuable alternate producer family, not identical to final universal pole quotient"
    "mine literal phase-sensitive inequalities; do not revive whole architecture unless same-object transport pays current consumer"
  ∷ attempted-payment riemannHypothesis "2026-08-31"
    "PR #677"
    "H_X -> H_A -> H_M -> H_T -> H_W -> H_E"
    supersededOverpayment
    "high off-line contradiction"
    "representation/producer debt was later compressed"
    "reuse local lemmas, not the whole decomposition"
  ∷ attempted-payment grQuantum "2026-05-12"
    "W4MatterStressEnergyInterfaceReceipt.agda / 78c96a5c27795f3c3f7500bad71d4db72f53755e"
    "physical calibration -> matter -> T_mu_nu -> Einstein-law obligation"
    representationWeld
    "physical stress-energy source usable by gravity"
    "correct seam but only pre-GR contract; no same-action theorem"
    "reuse as ancestry/ordering constraint"
  ∷ attempted-payment grQuantum "2026-07-20"
    "PR #192/#226/#246 family"
    "Einstein-Hilbert variation + shared action + anomaly/renormalization/semiclassical research cutset"
    terminalConsumer
    "full GR/QFT/quantum-gravity promotion"
    "comprehensive but too broad as immediate proof-search target"
    "retain as promotion gate; search from the smaller same-action/same-stress consumer"
  ∷ attempted-payment grQuantum "2026-08-30"
    "PR #639 family; total-QFT-stress correction 8809e427d3456e039f22ed4808601d3ff3470b1b"
    "endpoint-only common metric/action/stress weld with total QFT stress-energy"
    directProducer
    "same physical source in QFT and Einstein variation"
    "strong live bridge; sector inhabitation and post-weld anomaly/UV/semiclassical work remain"
    "reuse as canonical bridge and push literal sectors into it before inventing broader unification architecture"
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
  dated-entry navierStokes "2026-07-18" exactCommitDate
    "5b007992df368beb69f0a3350c87ebf8f969d39f / PR #14 family"
    "profile-uniform gamma-gap reduction" producerTactic
    "Early explicit uniformisation attempt; search for transport into the later signed physical consumer rather than treating it as final PDE payment."
  ∷ dated-entry riemannHypothesis "2026-07-19" exactCommitDate
    "commit 78bdf33b725596bd0c1bc399a3e5bb78cc9bb14c / PR #100"
    "DASHI-Weil / explicit-formula theorem ladder" compiler
    "First currently confirmed explicit RH programme boundary; February ancestry is analytic technology, not yet this RH route."
  ∷ dated-entry grQuantum "2026-07-20" pullRequestDate "PR #246"
    "deep GR/quantum research authority cutset" terminalConsumer
    "Comprehensive later promotion gate; the stress-energy/unification spine is already present in May."
  ∷ dated-entry yangMills "2026-07-20" exactCommitDate
    "3933eaa7618e1565580a5ac67aed875dbd850d3f + 16e0a24d5766e93fb9cfee921dc9449dda36426e / PR #248 family"
    "uniform cutoff mass-gap survival + uniform contraction through mass-gap chain" producerTactic
    "Strong historical sufficient route; inspect for direct same-family correlation-decay donors before rebuilding later machinery."
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
  ∷ dated-entry yangMills "2026-08-19" exactCommitDate
    "1a7075aa7c6343ff48a5b0ee7e49ec46bd841342 / Round64"
    "uniform physical gap master" terminalConsumer
    "Historical consumer compression; later normalization moves proof search upstream to quantitative same-family clustering."
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
    "The May Balaban/RG surface already names the finite-depth-to-uniform-gap quantifier debt; July PR #248 then tries uniform gap survival directly. Search both before paying later Row-C machinery again."
  ∷ donor-window riemannHypothesis "2026-02-23" "2026-08-31"
    "phase-sensitive zeta response / reflection-paired oscillatory inequality / one-sided target-centred upper bound / Abel or contraction limit transport"
    "February Abel-zeta machinery is analytic ancestry, while the first explicit RH programme boundary currently pinned is 19 July. Search donors without pretending those carriers are already identical."
  ∷ donor-window grQuantum "2026-05-12" "2026-08-30"
    "same action variation / metric perturbation / stress-energy identity across literal sectors"
    "Stress-energy interface predates the terminal composition and the August common-action weld."
  ∷ donor-window navierStokes "2026-01-24" "current"
    "signed physical production/transfer retained before absolute value or destructive coarse-graining -> cutoff-uniform spacetime/potential payment"
    "January dashiCFD already has signed/coherence construction ancestry; May explicitly types the continuum BKM/nonlinear wall; July has profile-uniform reductions; later exact Agda rounds should be searched as refinements/compositions, not assumed origin."
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
  "January signed/coherence ancestry; May enstrophy/vorticity tower; July profile-uniform gamma/cross-shell routes; Abel/telescope/Gram/resolvent/critical-cone transports"
  "dashiCFD signed filament/truth/theta; signed commutator; spectator resolvent; packet/danger"
  "do not destroy sign/coherence before payment; historical similarity does not prove exact R294/R541/R573 identity"
  "search January-current sibling-repo and pre-round aliases for signed transfer + dissipation/potential comparison in the correct order"

yangMillsFrontier : LiveFrontier
yangMillsFrontier = live-frontier yangMills
  "same reconstructed continuum family: quantitative connected-correlation decay -> positive physical spectral gap"
  "quantitative continuum clustering on SAME Schwinger family; separately identify candidate decay rate with physical spectrum"
  "May finite-depth uniformity wall and gap boundary; July uniform-cutoff survival; OS reconstruction; clustering-to-gap; dense-core; lattice-to-physical exponent transport"
  "May Balaban RG; July uniform contraction; coercivity/reflection positivity; CMP109/CMP116 influence; Langevin/Dyson; cluster expansion; polymer norm"
  "finite/RG decay, uniform cutoff gap, or generic Clustered is not automatically same-family continuum clustering"
  "search May-August history for attempted quantifier exchange/uniformisation and same-family correlation decay before paying Row-C again"

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
  "May stress-energy target; July Einstein-Hilbert/shared-action cutsets; endpoint sector variation; native-stress transport; common metric; pairing commutation; SameStressEnergyWeld"
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
      typedTheoremStateOutranksLooseStatusLanguage
      authoritativeMetadataOwnersRemainAuthoritative
      attemptedPaymentDoesNotEqualSuccessfulPayment : Bool

canonicalArchaeologyDiscipline : ArchaeologyDiscipline
canonicalArchaeologyDiscipline = archaeology-discipline
  true true true true true true true true true true true true true true true true true true

------------------------------------------------------------------------
-- COMPACT PROOF-CATALYST DASHBOARD.
------------------------------------------------------------------------

record ProofCatalystDashboard : Set where
  constructor proof-catalyst-dashboard
  field nsTarget ymTarget rhTarget grQuantumTarget historicalWarning : String

canonicalProofCatalystDashboard : ProofCatalystDashboard
canonicalProofCatalystDashboard = proof-catalyst-dashboard
  "NS: January signed/coherence physical ancestry -> May explicit continuum wall -> July uniformisation attempts -> signed physical transfer -> uniform spacetime/potential payment"
  "YM: May finite-depth gap/uniformity wall -> July uniform-gap survival attempts -> continuum physical Schwinger family -> quantitative clustering -> physical spectrum"
  "RH: February analytic ancestry -> July first explicit RH programme -> literal oscillatory zero response -> uniform strict high margin"
  "GR/QFT: May physical matter/stress seam -> July broad shared-action/QG cutset -> literal sector + Einstein variations -> same action/metric/stress weld -> anomaly/UV/semiclassical QG recovery"
  "Dates are lower bounds. QID/OEIS/DOI are identity/provenance coordinates, not proof. Acquisition may snowball out of dependency order; theorem payment may not. Attempted payment is not successful payment. Typed theorem state outranks loose commit-message status. Search old outputs by shape and prove same-object transport before reuse."
