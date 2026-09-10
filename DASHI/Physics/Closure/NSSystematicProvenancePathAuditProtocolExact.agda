module DASHI.Physics.Closure.NSSystematicProvenancePathAuditProtocolExact where

------------------------------------------------------------------------
-- SYSTEMATIC NAVIER--STOKES PROVENANCE / PATH AUDIT PROTOCOL
--
-- One append-only audit contract for the oldest -> newest provenance pass.
-- The evidence ledger is NSForensicSignedRouteLineageAuditExact.
--
-- DATE DISCIPLINE
-- Commit/source-first-appearance, PR-open/public exposure, merge, publication,
-- and external release are different events.  We record only recovered events.
-- A missing PR/publication surface is written as not recovered; commit time is
-- never silently promoted to publication time.
--
-- CURRENT CLASSIFICATION
-- * 2026-06-12/13: whole-problem candidate/global-regularity roadmap receipts.
-- * 2026-06-20/22: earlier formal sign-sensitive Wall-1/BKM candidate routes.
-- * 2026-07-26: earliest recovered assembly of the LATER EXACT SIGNED,
--   PHYSICAL, CUTOFF-UNIFORM ANALYTIC PROBLEM and its global consumer.
--
-- Thus June is real priority/provenance, but does not by chronology become the
-- same R423/R503 signed-resolvent carrier.  July 26 remains the current first
-- recovered same-problem assembly pending still-earlier same-carrier evidence.
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
  problemShape exactCarrier exactEqualityWeld canonicalConsumer : EvidenceGrade
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
-- JUNE: WHOLE-PROBLEM ROADMAP + SIGN-SENSITIVE CANDIDATE ROUTES
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

jun22SignedWall1Surface : DatedPublicSurface
jun22SignedWall1Surface = dated-public-surface
  "NS Wall-1 signed-XOR / signed-spectrum correction tranche"
  "48b0c1918e8f615488f6efc29db8ed8f0d499893"
  "2026-06-22T08:17:20Z" "2026-06-22T18:17:20+10:00"
  noSeparatePublicSurfaceRecovered
  "NSTriadSignedXORGaugeabilityBoundary; NSTriadSignedLaplacianIdentityReceipt; NSTriadSignedLaplacianSpectrumAuditReceipt"
  "not separately recovered" "not separately recovered"
  "candidate signed operator/spectrum route; active telemetry says proposed signed-Laplacian proxy is not the same operator as I-K_N; theorem/full-NS/Clay promotion remain false"

------------------------------------------------------------------------
-- JULY PUBLIC PR SURFACES: OPEN DATE != MERGE DATE != SOURCE-FIRST DATE
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
  jun20DeterminantSignSurface ∷ jun22SignedWall1Surface ∷ pr140Surface ∷
  pr145Surface ∷ pr227Surface ∷ pr255Surface ∷ pr336Surface ∷ pr338Surface ∷
  pr820Surface ∷ pr825Surface ∷ []

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
  "Jun12/13 whole-problem candidate receipts" "Jun20/22 sign-sensitive formal routes"
  semanticAlias candidateWholeProblem include
  "whole-problem grammar precedes sign-sensitive Wall-1 routes but does not itself construct the later signed physical operator"

juneSignedRoutes = audit-step
  "Jun20 determinant/BKM + Jun22 signed Wall-1 candidate routes" "Jul20 signed-response/majorant correction"
  semanticAlias signedCandidateRoute include
  "June already explores sign-sensitive mechanisms, but Jun22 explicitly records a same-operator failure; Jul20 later formalizes the response-vs-majorant representation boundary"

julyAssembly = audit-step
  "Jul20-Jul25 signed/resolvent/commutator architecture" "Jul26 exact signed physical cutoff-uniform problem"
  sameConsumerShape problemShape include
  "Jul26 is current earliest recovered simultaneous assembly of exact signed physical coefficient, cutoff-uniform signed target, dissipation comparison and global consumer"

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
  janToJune ∷ juneWholeProblem ∷ juneSignedRoutes ∷ julyAssembly ∷
  augustPhysicalization ∷ r375SameObject ∷ r406Critical ∷ r423Canonical ∷ handoff ∷ []

------------------------------------------------------------------------
-- FIREWALLS
------------------------------------------------------------------------

data ChronologyCreatesIdentity : Set where
data AliasCreatesIdentity : Set where
data SameConsumerShapeCreatesEquality : Set where
data ProblemSpecificationCreatesProof : Set where
data CandidateWholeProblemCreatesSignedCarrier : Set where
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

juneSignedCandidateIsLiteralLaterR423R503Carrier : Bool
juneSignedCandidateIsLiteralLaterR423R503Carrier = false

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
  "Whole-problem roadmap receipts exist by 2026-06-12 and sign-sensitive candidate routes by 2026-06-20/22. The earliest recovered assembly of the later exact signed physical cutoff-uniform analytic problem remains 2026-07-26. Later tranches primarily physicalize, repair same-object provenance, remove lossy majorants/plumbing, or re-express that same missing estimate."

nextOldestForwardObligation : String
nextOldestForwardObligation =
  "Search Jun22->Jul20 forward by semantic object (signed operator, commutator, gap, dissipation, shell/Schur/resolvent), recording source commit and independent PR/public surface where recoverable; then reconcile with the R423/R486/R492/R501 reverse pass."

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
juneSignedCandidateIsLiteralLaterR423R503CarrierIsFalse : juneSignedCandidateIsLiteralLaterR423R503Carrier ≡ false
juneSignedCandidateIsLiteralLaterR423R503CarrierIsFalse = refl
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
