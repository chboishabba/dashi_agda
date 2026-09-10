module DASHI.Physics.Closure.NSSystematicProvenancePathAuditProtocolExact where

------------------------------------------------------------------------
-- SYSTEMATIC NAVIER--STOKES PROVENANCE / PATH AUDIT PROTOCOL
--
-- One append-only audit contract for the oldest -> newest provenance pass.
-- The evidence ledger is NSForensicSignedRouteLineageAuditExact.
--
-- DATE DISCIPLINE
-- Commit/source-first-appearance, PR-open/public exposure, merge, publication,
-- and external release are different events. We record only recovered events.
-- A missing PR/publication surface is written as not recovered; commit time is
-- never silently promoted to publication time.
--
-- CURRENT CLASSIFICATION
-- * 2026-06-12/13: whole-problem candidate/global-regularity roadmap receipts.
-- * 2026-06-20/23: sign-sensitive Wall-1/BKM/operator candidate routes,
--   culminating in amplitude-weighted K_N(A) and an energy/dissipation fork.
-- * 2026-07-22/23: complete typed theorem-facing completion spine and exact
--   strict-dissipation / diffuse-charging compilers, but concrete cutoff-
--   uniform analytic payments are still explicit inputs.
-- * 2026-07-26: earliest recovered assembly of the LATER EXACT SIGNED,
--   PHYSICAL, CUTOFF-UNIFORM ANALYTIC PROBLEM and its global consumer.
--
-- Thus the older work already contains the whole problem grammar, signed
-- operator experimentation, and dissipation-consumer architecture. It does
-- not by chronology alone become the later literal R423/R503 carrier.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Physics.Closure.NSForensicSignedRouteLineageAuditExact as Lineage

data AuditDirection : Set where oldestToNewest newestToOldest : AuditDirection
data AuditScope : Set where provenancePathTracing buildEnvironmentArchaeology : AuditScope
data MatchBasis : Set where exactName semanticAlias sameCarrierEquality sameConsumerShape : MatchBasis
data EvidenceGrade : Set where
  chronologyOnly structuralPrecursor candidateWholeProblem signedCandidateRoute
  completionSpine problemShape exactCarrier exactEqualityWeld canonicalConsumer : EvidenceGrade
data AuditDisposition : Set where include defer rejectAsIdentity : AuditDisposition

currentDirection : AuditDirection
currentDirection = oldestToNewest
currentScope : AuditScope
currentScope = provenancePathTracing
nixBuildArchaeologyDisposition : AuditDisposition
nixBuildArchaeologyDisposition = defer
roundNumbersArePrimarySearchKey : Bool
roundNumbersArePrimarySearchKey = false
semanticAliasesMustBeSearched : Bool
semanticAliasesMustBeSearched = true
prsAndTranchesMustBeComposed : Bool
prsAndTranchesMustBeComposed = true
crossRepositoryPrecursorsAreInScope : Bool
crossRepositoryPrecursorsAreInScope = true

data PublicSurfaceKind : Set where
  noSeparatePublicSurfaceRecovered publicPRSurface publicMergeSurface
  externalPublicationSurface : PublicSurfaceKind

record DatedPublicSurface : Set where
  constructor dated-public-surface
  field
    label : String
    sourceCommit : String
    sourceCommitUTC : String
    sourceCommitBrisbane : String
    publicKind : PublicSurfaceKind
    publicLocator : String
    publicOpenedUTC : String
    publicMergedUTC : String
    note : String
open DatedPublicSurface public

------------------------------------------------------------------------
-- JUNE: WHOLE-PROBLEM ROADMAP + SIGN/OPERATOR CANDIDATE ROUTES
------------------------------------------------------------------------

jun12FinalStateSurface : DatedPublicSurface
jun12FinalStateSurface = dated-public-surface
  "NSFinalStateReceipt candidate whole-problem roadmap"
  "66ac13c9b9c3e942ed80242957b237cde61bf662"
  "2026-06-12T06:02:01Z" "2026-06-12T16:02:01+10:00"
  noSeparatePublicSurfaceRecovered
  "DASHI/Physics/Closure/NSFinalStateReceipt.agda"
  "not separately recovered" "not separately recovered"
  "uniform enstrophy/vorticity, continuum BKM, global smoothness and Clay closure are open on this source receipt"

jun12CandidateBKMSurface : DatedPublicSurface
jun12CandidateBKMSurface = dated-public-surface
  "candidate enstrophy/vorticity/BKM/global-regularity passage grammar"
  "f545fbf5a9cc792e3717033da0bdbd42aaa8337c"
  "2026-06-12T06:05:55Z" "2026-06-12T16:05:55+10:00"
  noSeparatePublicSurfaceRecovered
  "DASHI/Physics/Closure/NSCandidateCompleteEnstrophyBKMPassageReceipt.agda"
  "not separately recovered" "not separately recovered"
  "candidate passage recorded; uniform vorticity-Linf, continuum BKM and Clay closure remain false on owning receipt"

jun13CandidateClosureSurface : DatedPublicSurface
jun13CandidateClosureSurface = dated-public-surface
  "current-state globalRegularityClosed=true candidate transition"
  "b009e8e96de2f158a74e78f9765a7f83510185b6"
  "2026-06-13T13:19:51Z" "2026-06-13T23:19:51+10:00"
  noSeparatePublicSurfaceRecovered
  "source commit/current-state receipt"
  "not separately recovered" "not separately recovered"
  "local current-state closure claim while Clay promotion remains false; not identified with later literal signed-resolvent carrier"

jun20DeterminantSignSurface : DatedPublicSurface
jun20DeterminantSignSurface = dated-public-surface
  "NS determinant/Betchov/BKM sign correction route"
  "326d075bb8030a630ca7e2dee6d4af4446404b3c"
  "2026-06-20T10:31:15Z" "2026-06-20T20:31:15+10:00"
  noSeparatePublicSurfaceRecovered
  "NSBetchovDeterminantIdentityReceipt; NSDeterminantSignRuleReceipt; NSBetchovBKMPositiveMeasureReceipt"
  "not separately recovered" "not separately recovered"
  "sign-sensitive near-blow-up route under explicit BKM/blow-up assumptions; strict H_B/area gates and Clay promotion remain open"

jun22CycleSchurSurface : DatedPublicSurface
jun22CycleSchurSurface = dated-public-surface
  "Wall-1 cycle-family / Schur-complement frame-gap target"
  "fa912fa9843635b328d654911e5518488d85e4bb"
  "2026-06-22T05:30:15Z" "2026-06-22T15:30:15+10:00"
  noSeparatePublicSurfaceRecovered
  "NSTriadCycleFamilyLowerBoundBoundary; NSSchurComplementFrameGapBoundary"
  "not separately recovered" "not separately recovered"
  "already names S_N=(I-K11)-K10(I-K00)^-1K01 and a uniform frame-gap target, but K01/non-adversarial coupling and uniform gap remain unproved"

jun22SignedWall1Surface : DatedPublicSurface
jun22SignedWall1Surface = dated-public-surface
  "NS Wall-1 signed-XOR / signed-spectrum correction tranche"
  "48b0c1918e8f615488f6efc29db8ed8f0d499893"
  "2026-06-22T08:17:20Z" "2026-06-22T18:17:20+10:00"
  noSeparatePublicSurfaceRecovered
  "NSTriadSignedXORGaugeabilityBoundary; NSTriadSignedLaplacianIdentityReceipt; NSTriadSignedLaplacianSpectrumAuditReceipt"
  "not separately recovered" "not separately recovered"
  "candidate signed operator/spectrum route; active telemetry says proposed signed-Laplacian proxy is not the same operator as I-K_N; theorem/full-NS/Clay promotion remain false"

jun22CarrierReconciliationSurface : DatedPublicSurface
jun22CarrierReconciliationSurface = dated-public-surface
  "signed Wall-1 carrier reconciliation / identification boundary"
  "484ec7d70ecdbae92ad87c0ae53b8a01b0526f48"
  "2026-06-22T13:39:30Z" "2026-06-22T23:39:30+10:00"
  noSeparatePublicSurfaceRecovered
  "NSTriadSignedCarrierReconciliationBoundary; NSTriadWall1CarrierIdentificationBoundary"
  "not separately recovered" "not separately recovered"
  "explicitly recognizes that the old signed chart, cycle-family, raw signed-XOR and signed-spectral candidates do not yet identify the correct Wall-1 carrier"

jun23ContinuousCoherenceSurface : DatedPublicSurface
jun23ContinuousCoherenceSurface = dated-public-surface
  "continuous coherence / coherence-deficit Wall-1 candidate"
  "f2a61621229630fb3cddf61ff23022ff31c9632b"
  "2026-06-22T14:34:03Z" "2026-06-23T00:34:03+10:00"
  noSeparatePublicSurfaceRecovered
  "NSTriadContinuousCoherenceCarrierBoundary; NSTriadCoherenceDeficitFloorBoundary"
  "not separately recovered" "not separately recovered"
  "records cap_N <= kappa < 1 -> Wall-1 floor >= (1-kappa)/2 as theorem shape only; proof and promotion remain false"

jun23KNIdentitySurface : DatedPublicSurface
jun23KNIdentitySurface = dated-public-surface
  "K_N exact-identity / negative-frame Wall-1 candidate"
  "a48db609b61565c0b4242699a8725cdbcd675538"
  "2026-06-22T15:40:02Z" "2026-06-23T01:40:02+10:00"
  noSeparatePublicSurfaceRecovered
  "NSTriadKNExactIdentityReceipt; NSTriadBSNegativeFrameCoercivityBoundary; NSTriadBSSpanningLemmaReceipt; NSTriadBSFrameEquidistributionBoundary"
  "not separately recovered" "not separately recovered"
  "retires raw signed-XOR as primary carrier and records corrected positive-subspace identity L_signed_norm = I - 2 K_N; theorem remains candidate-only"

jun23AmplitudeForkSurface : DatedPublicSurface
jun23AmplitudeForkSurface = dated-public-surface
  "amplitude-weighted K_N(A) / energy-budgeted Wall-1/2 fork"
  "815292afe6694abad551cd310b66a539f2209100"
  "2026-06-22T16:46:11Z" "2026-06-23T02:46:11+10:00"
  noSeparatePublicSurfaceRecovered
  "NSAmplitudeWeightedNegativeFrameBoundary; NSTriadEnergyBudgetedCoherenceForkBoundary; NSPointwiseTriadCloudBoundary"
  "not separately recovered" "not separately recovered"
  "candidate fork already separates frame-coercive, low-band bounded and high-dissipation residence-limited mechanisms; uniform genuine-Biot-Savart theorem remains open"

------------------------------------------------------------------------
-- JULY: PUBLIC COMPLETION SPINES AND EXACT SIGNED PHYSICAL ASSEMBLY
------------------------------------------------------------------------

pr140Surface = dated-public-surface
  "PR #140 compact-Gamma signed-response/Schur/tail architecture"
  "e64a38ab617cf88035555a07a223afe46480df0e"
  "2026-07-20T06:17:05Z" "2026-07-20T16:17:05+10:00"
  publicPRSurface "pull/140"
  "2026-07-19T15:36:26Z" "2026-07-20T06:17:05Z"
  "public PR surface predates merge; signed response remains distinct from nonnegative pair majorant"

pr145Surface = dated-public-surface
  "PR #145 rational six-mode Wall1 Schur/resolvent/gap packet"
  "8905dc5c4c3389f18698f1669040dcf5923af0c6"
  "2026-07-20T03:02:06Z" "2026-07-20T13:02:06+10:00"
  publicPRSurface "pull/145"
  "2026-07-20T01:50:34Z" "2026-07-20T03:02:06Z"
  "public finite Schur/resolvent/gap packet; physical representation remains mandatory"

pr227Surface = dated-public-surface
  "PR #227 cross-pollinated compact-Gamma analytic closure stack"
  "c2b313a0878b0281781dd7a1bf3ae851d24af8d9"
  "2026-07-20T09:42:15Z" "2026-07-20T19:42:15+10:00"
  publicPRSurface "pull/227"
  "2026-07-20T06:38:17Z" "2026-07-20T09:42:15Z"
  "public integration of differentiated triads, full-shell pair incidence, tail, Galerkin, invariant-region and BKM architecture"

pr255Surface = dated-public-surface
  "PR #255 concrete far-tail commutator decay"
  "bc9a627985cf4140ee10260f6399050aacf5cba4"
  "2026-07-20T15:09:40Z" "2026-07-21T01:09:40+10:00"
  publicPRSurface "pull/255"
  "2026-07-20T14:52:19Z" "2026-07-20T15:09:40Z"
  "public far-low commutator and far-high tail theorem surfaces"

pr320Surface : DatedPublicSurface
pr320Surface = dated-public-surface
  "PR #320 official-norm -> expenditure -> all-data cutoff -> continuum BKM completion spine"
  "cc241eb8bc12dec879323ae4c55d8bd67cbf942b"
  "2026-07-24T08:00:07Z" "2026-07-24T18:00:07+10:00"
  publicPRSurface "pull/320"
  "2026-07-22T05:52:23Z" "2026-07-24T08:00:07Z"
  "complete proof-relevant theorem-facing spine is public here; genuine cutoff-uniform PDE estimates remain explicit conditional inhabitants"

jul23StrictMarginSurface : DatedPublicSurface
jul23StrictMarginSurface = dated-public-surface
  "exact strict Wall-I/II dissipation-margin compiler"
  "105d654be4f3f0840df1543339df0ecae8ce40ba"
  "2026-07-23T09:56:04Z" "2026-07-23T19:56:04+10:00"
  publicPRSurface "pull/320"
  "2026-07-22T05:52:23Z" "2026-07-24T08:00:07Z"
  "machine-checked scalar compiler: near+farLow+farHigh+strictMargin <= viscosity once three concrete payments and positive margin are supplied; concrete cutoff-uniform payments remain analytic"

jul23DiffuseChargingSurface : DatedPublicSurface
jul23DiffuseChargingSurface = dated-public-surface
  "diffuse-spectrum dissipation charging -> finite vorticity/BKM compiler"
  "292748be805e593506970c2b4bc6b093c2b5116e"
  "2026-07-23T09:57:37Z" "2026-07-23T19:57:37+10:00"
  publicPRSurface "pull/320"
  "2026-07-22T05:52:23Z" "2026-07-24T08:00:07Z"
  "exact endpoint compiler; frontier remains concrete cutoff-independent diffuse charge plus finite remainder"

pr336Surface = dated-public-surface
  "PR #336 exact Wall-I signed multiplier-difference commutator frontier"
  "68ab8ffbcf5c0aa791720a454dbeb1631ea933b2"
  "2026-07-25T07:09:05Z" "2026-07-25T17:09:05+10:00"
  publicPRSurface "pull/336"
  "2026-07-25T04:57:13Z" "2026-07-25T07:09:05Z"
  "public K_raw/K_diff/K_absdiff separation and sign-sensitive frontier"

pr338Surface = dated-public-surface
  "PR #338 Stage-3 signed physical/final-problem assembly"
  "92316f005def176f490ea5c26fd7ad85017090cc"
  "2026-07-27T05:15:48Z" "2026-07-27T15:15:48+10:00"
  publicPRSurface "pull/338"
  "2026-07-25T10:42:25Z" "2026-07-27T05:15:48Z"
  "PR was public before Jul26 exact signed coefficient/gap/global-composition commits and merged after them"

------------------------------------------------------------------------
-- LATER PUBLIC RECONCILIATION SURFACES
------------------------------------------------------------------------

pr820Surface = dated-public-surface
  "PR #820 restore canonical R423 after Cauchy archaeology"
  "2c2792478ae38bc23c5efafdbfa68171fdedc9e4"
  "2026-09-09T03:34:17Z" "2026-09-09T13:34:17+10:00"
  publicPRSurface "pull/820"
  "2026-09-07T13:50:12Z" "2026-09-09T03:34:17Z"
  "R486 source implementation occurred after PR opened; public PR chronology and implementation chronology are independent"

pr825Surface = dated-public-surface
  "PR #825 literal R406/direct-resolvent terminal cone"
  "bc57debbfae2446869b805543855b289866a3437"
  "2026-09-09T03:34:17Z" "2026-09-09T13:34:17+10:00"
  publicPRSurface "pull/825"
  "2026-09-07T17:52:01Z" "2026-09-09T03:34:17Z"
  "public cone contains the later R496-R503 direct route; individual source commits remain first-implementation dates"

publicSurfaceChronology : List DatedPublicSurface
publicSurfaceChronology =
  jun12FinalStateSurface ∷ jun12CandidateBKMSurface ∷ jun13CandidateClosureSurface ∷
  jun20DeterminantSignSurface ∷ jun22CycleSchurSurface ∷ jun22SignedWall1Surface ∷
  jun22CarrierReconciliationSurface ∷ jun23ContinuousCoherenceSurface ∷
  jun23KNIdentitySurface ∷ jun23AmplitudeForkSurface ∷ pr140Surface ∷
  pr145Surface ∷ pr227Surface ∷ pr255Surface ∷ pr320Surface ∷
  jul23StrictMarginSurface ∷ jul23DiffuseChargingSurface ∷ pr336Surface ∷
  pr338Surface ∷ pr820Surface ∷ pr825Surface ∷ []

------------------------------------------------------------------------
-- SYSTEMATIC STEPS / CLASSIFICATION
------------------------------------------------------------------------

record AuditStep : Set where
  constructor audit-step
  field
    fromLabel toLabel : String
    matchBasis : MatchBasis
    evidenceGrade : EvidenceGrade
    disposition : AuditDisposition
    reason : String
open AuditStep public

janToJune = audit-step
  "dashiCFD Jan-Jun sign/support/residue/barrier" "Jun12 whole-problem roadmap"
  semanticAlias structuralPrecursor include
  "methodological ancestry only; no same-object theorem identity"

juneWholeProblem = audit-step
  "Jun12/13 whole-problem candidate receipts" "Jun20/23 sign-sensitive formal routes"
  semanticAlias candidateWholeProblem include
  "whole-problem grammar precedes sign-sensitive Wall-1 routes but does not itself construct the later signed physical operator"

juneSignedRoutes = audit-step
  "Jun20 determinant/BKM -> Jun22 cycle/Schur -> signed carrier reconciliation -> Jun23 K_N(A) energy fork"
  "Jul20 signed-response/majorant correction"
  semanticAlias signedCandidateRoute include
  "June already searches sign, Schur/frame gaps, corrected carrier identity, amplitude weighting and dissipation charging; all remain candidate/fail-closed and several old carriers are explicitly rejected"

julyCompletionSpine = audit-step
  "Jul20 signed-response/majorant and harmonic architecture"
  "Jul22/23 PR320 complete theorem-facing spine + strict dissipation/diffuse BKM compilers"
  sameConsumerShape completionSpine include
  "before Jul26 the repository already owns the complete typed consumer path from harmonic estimates through strict viscosity payment and cutoff-uniform continuum BKM; the missing concrete PDE producers remain explicit"

julyAssembly = audit-step
  "Jul22/23 complete typed consumer spine" "Jul26 exact signed physical cutoff-uniform problem"
  sameConsumerShape problemShape include
  "Jul26 remains current earliest recovered simultaneous assembly of exact signed physical coefficient, cancellation-aware route, cutoff-uniform signed target, dissipation comparison and global consumer"

augustPhysicalization = audit-step
  "Jul26 signed analytic problem" "Aug08-Aug31 physical/signed/resolvent maturation"
  semanticAlias problemShape include
  "later tranches physicalize and reuse the earlier consumer architecture"

r375SameObject = audit-step
  "R353 generic signed Gram family" "R375/R377/R379 literal physical Package A"
  sameCarrierEquality exactCarrier include
  "companion/integration become definitionally physical; caller-selected Gram/transport coordinates are removed"

r406Critical = audit-step
  "R290/R406 signed remainder" "R410/R414/R422 critical barrier"
  sameCarrierEquality exactEqualityWeld include
  "Round104 remainder becomes definitionally the literal R406 integral and actual R290 pair derivatives reach R406"

r423Canonical = audit-step
  "signed quadratic-companion forcing cross" "R423 canonical signed companion consumer"
  sameCarrierEquality canonicalConsumer include
  "no positive Wiener proxy, alternate companion or second remainder"

handoff = audit-step
  "R423" "R486/R492/R501/R503/R541/R573/R584"
  semanticAlias canonicalConsumer include
  "meeting seam with newest-to-oldest pass; later archaeology restores R423 and direct/nested routes re-express its producer"

systematicAuditSteps : List AuditStep
systematicAuditSteps =
  janToJune ∷ juneWholeProblem ∷ juneSignedRoutes ∷ julyCompletionSpine ∷
  julyAssembly ∷ augustPhysicalization ∷ r375SameObject ∷ r406Critical ∷
  r423Canonical ∷ handoff ∷ []

------------------------------------------------------------------------
-- FIREWALLS
------------------------------------------------------------------------

data ChronologyCreatesIdentity : Set where
data AliasCreatesIdentity : Set where
data SameConsumerShapeCreatesEquality : Set where
data ProblemSpecificationCreatesProof : Set where
data CandidateWholeProblemCreatesSignedCarrier : Set where
data CompletionSpineCreatesAnalyticProducer : Set where
data LaterRoundMeansNewProblem : Set where
data PublicRepositoryCreatesExternalInfluence : Set where
data CommitDateCreatesPublicationDate : Set where

chronologyDoesNotCreateIdentity : ChronologyCreatesIdentity → ⊥
chronologyDoesNotCreateIdentity ()
aliasDoesNotCreateIdentity : AliasCreatesIdentity → ⊥
aliasDoesNotCreateIdentity ()
sameShapeDoesNotCreateEquality : SameConsumerShapeCreatesEquality → ⊥
sameShapeDoesNotCreateEquality ()
problemSpecificationDoesNotCreateProof : ProblemSpecificationCreatesProof → ⊥
problemSpecificationDoesNotCreateProof ()
candidateWholeProblemDoesNotCreateSignedCarrier : CandidateWholeProblemCreatesSignedCarrier → ⊥
candidateWholeProblemDoesNotCreateSignedCarrier ()
completionSpineDoesNotCreateAnalyticProducer : CompletionSpineCreatesAnalyticProducer → ⊥
completionSpineDoesNotCreateAnalyticProducer ()
laterRoundDoesNotMeanNewProblem : LaterRoundMeansNewProblem → ⊥
laterRoundDoesNotMeanNewProblem ()
publicRepoDoesNotCreateInfluenceClaim : PublicRepositoryCreatesExternalInfluence → ⊥
publicRepoDoesNotCreateInfluenceClaim ()
commitDateDoesNotCreatePublicationDate : CommitDateCreatesPublicationDate → ⊥
commitDateDoesNotCreatePublicationDate ()

------------------------------------------------------------------------
-- CURRENT FINDINGS / ROADMAP CHECKPOINT
------------------------------------------------------------------------

commitDateEqualsPublicationDateByDefault : Bool
commitDateEqualsPublicationDateByDefault = false
prOpenDateEqualsMergeDateByDefault : Bool
prOpenDateEqualsMergeDateByDefault = false

earliestRecoveredWholeProblemRoadmapPredatesJuly : Bool
earliestRecoveredWholeProblemRoadmapPredatesJuly = true

earlyJuneSignedCandidateRoutesRecovered : Bool
earlyJuneSignedCandidateRoutesRecovered = true

juneAmplitudeDissipationForkRecovered : Bool
juneAmplitudeDissipationForkRecovered = true

juneSignedCandidateIsLiteralLaterR423R503Carrier : Bool
juneSignedCandidateIsLiteralLaterR423R503Carrier = false

july23CompleteTypedConsumerSpineRecovered : Bool
july23CompleteTypedConsumerSpineRecovered = true

july23ConcreteCutoffUniformAnalyticPaymentsRecovered : Bool
july23ConcreteCutoffUniformAnalyticPaymentsRecovered = false

earliestRecoveredAssemblyIsJuly26 : Bool
earliestRecoveredAssemblyIsJuly26 = Lineage.earliestRecoveredFinalProblemSpecificationIsJuly26
july26IsClaimedSolved : Bool
july26IsClaimedSolved = Lineage.july26ClaimedSolved
signedRouteRequiresOldPositiveMajorant : Bool
signedRouteRequiresOldPositiveMajorant = Lineage.r373SignedRouteBypassesNonnegativeMajorant
r375CompanionIsDefinitionallyPhysical : Bool
r375CompanionIsDefinitionallyPhysical = Lineage.r375R353IsDefinitionallyPhysical
r410TargetIsLiteralR406 : Bool
r410TargetIsLiteralR406 = Lineage.r410TargetIsLiteralR406
r414NeedsSecondRemainder : Bool
r414NeedsSecondRemainder = Lineage.r414SecondRemainderNeeded
r423NeedsPositiveWienerEnvelope : Bool
r423NeedsPositiveWienerEnvelope = Lineage.r423PositiveWienerEnvelopeRequired
r423RemainingProducerIsUniformSignedCompanionBudget : Bool
r423RemainingProducerIsUniformSignedCompanionBudget = Lineage.r423RemainingProducerIsCutoffUniformSignedCompanionBudget

oldestForwardPassActive : Bool
oldestForwardPassActive = true
newestBackwardPassExistsAsSeparateLane : Bool
newestBackwardPassExistsAsSeparateLane = true
passesHaveFullyReconciledEveryIntermediateAlias : Bool
passesHaveFullyReconciledEveryIntermediateAlias = false

currentMeetingRegion : String
currentMeetingRegion =
  "R423 -> R486 restoration -> R492 same-object firewall -> R501 direct resolvent -> R503/R541/R573/R584"

currentHistoricalHypothesis : String
currentHistoricalHypothesis =
  "Whole-problem roadmap receipts exist by 2026-06-12; sign-sensitive operator, Schur/frame-gap, carrier-reconciliation and amplitude/dissipation candidate routes are explicit by 2026-06-23; a complete typed harmonic-to-BKM consumer spine is public by 2026-07-22 and has exact strict-dissipation/diffuse-charging compilers by 2026-07-23. The earliest recovered assembly of the later exact signed physical cutoff-uniform analytic problem remains 2026-07-26. Later tranches primarily physicalize, repair same-object provenance, remove lossy majorants/plumbing, or re-express that same missing estimate."

nextOldestForwardObligation : String
nextOldestForwardObligation =
  "Continue Jul23->Jul26 semantic archaeology for normalized boundary signs, strict margin, signed triad/cancellation and global-scalar aliases; determine whether any pre-Jul26 source simultaneously owns the literal physical signed coefficient and the cutoff-uniform producer, otherwise preserve Jul26 as first exact assembly."

systematicAuditIsAppendOnly : Bool
systematicAuditIsAppendOnly = true
historicalReceiptsMayBeReclassifiedButNotRewritten : Bool
historicalReceiptsMayBeReclassifiedButNotRewritten = true

------------------------------------------------------------------------
-- EXPECTED POLARITIES
------------------------------------------------------------------------

currentDirectionIsOldestToNewest : currentDirection ≡ oldestToNewest
currentDirectionIsOldestToNewest = refl
roundNumbersArePrimarySearchKeyIsFalse : roundNumbersArePrimarySearchKey ≡ false
roundNumbersArePrimarySearchKeyIsFalse = refl
semanticAliasesMustBeSearchedIsTrue : semanticAliasesMustBeSearched ≡ true
semanticAliasesMustBeSearchedIsTrue = refl
commitDateEqualsPublicationDateByDefaultIsFalse : commitDateEqualsPublicationDateByDefault ≡ false
commitDateEqualsPublicationDateByDefaultIsFalse = refl
prOpenDateEqualsMergeDateByDefaultIsFalse : prOpenDateEqualsMergeDateByDefault ≡ false
prOpenDateEqualsMergeDateByDefaultIsFalse = refl
earlyJuneSignedCandidateRoutesRecoveredIsTrue : earlyJuneSignedCandidateRoutesRecovered ≡ true
earlyJuneSignedCandidateRoutesRecoveredIsTrue = refl
juneAmplitudeDissipationForkRecoveredIsTrue : juneAmplitudeDissipationForkRecovered ≡ true
juneAmplitudeDissipationForkRecoveredIsTrue = refl
juneSignedCandidateIsLiteralLaterR423R503CarrierIsFalse : juneSignedCandidateIsLiteralLaterR423R503Carrier ≡ false
juneSignedCandidateIsLiteralLaterR423R503CarrierIsFalse = refl
july23CompleteTypedConsumerSpineRecoveredIsTrue : july23CompleteTypedConsumerSpineRecovered ≡ true
july23CompleteTypedConsumerSpineRecoveredIsTrue = refl
july23ConcreteCutoffUniformAnalyticPaymentsRecoveredIsFalse : july23ConcreteCutoffUniformAnalyticPaymentsRecovered ≡ false
july23ConcreteCutoffUniformAnalyticPaymentsRecoveredIsFalse = refl
earliestRecoveredAssemblyIsJuly26IsTrue : earliestRecoveredAssemblyIsJuly26 ≡ true
earliestRecoveredAssemblyIsJuly26IsTrue = Lineage.earliestRecoveredFinalProblemSpecificationIsJuly26IsTrue
july26IsClaimedSolvedIsFalse : july26IsClaimedSolved ≡ false
july26IsClaimedSolvedIsFalse = Lineage.july26ClaimedSolvedIsFalse
signedRouteRequiresOldPositiveMajorantIsFalse : signedRouteRequiresOldPositiveMajorant ≡ false
signedRouteRequiresOldPositiveMajorantIsFalse = Lineage.r373SignedRouteBypassesNonnegativeMajorantIsFalse
r375CompanionIsDefinitionallyPhysicalIsTrue : r375CompanionIsDefinitionallyPhysical ≡ true
r375CompanionIsDefinitionallyPhysicalIsTrue = Lineage.r375R353IsDefinitionallyPhysicalIsTrue
r410TargetIsLiteralR406IsTrue : r410TargetIsLiteralR406 ≡ true
r410TargetIsLiteralR406IsTrue = Lineage.r410TargetIsLiteralR406IsTrue
r414NeedsSecondRemainderIsFalse : r414NeedsSecondRemainder ≡ false
r414NeedsSecondRemainderIsFalse = Lineage.r414SecondRemainderNeededIsFalse
r423NeedsPositiveWienerEnvelopeIsFalse : r423NeedsPositiveWienerEnvelope ≡ false
r423NeedsPositiveWienerEnvelopeIsFalse = Lineage.r423PositiveWienerEnvelopeRequiredIsFalse
passesFullyReconciledIsFalse : passesHaveFullyReconciledEveryIntermediateAlias ≡ false
passesFullyReconciledIsFalse = refl
systematicAuditIsAppendOnlyIsTrue : systematicAuditIsAppendOnly ≡ true
systematicAuditIsAppendOnlyIsTrue = refl
