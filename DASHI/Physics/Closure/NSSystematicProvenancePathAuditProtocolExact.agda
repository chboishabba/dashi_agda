module DASHI.Physics.Closure.NSSystematicProvenancePathAuditProtocolExact where

------------------------------------------------------------------------
-- SYSTEMATIC NAVIER--STOKES PROVENANCE / PATH AUDIT PROTOCOL
--
-- This owner freezes HOW the forensic audit is being performed so later
-- workers do not silently turn a chronology snowball into a theorem claim or
-- restart the search from round-number names alone.
--
-- The companion ledger is:
--   NSForensicSignedRouteLineageAuditExact
--
-- Division of labour at the time of this receipt:
--   * this lane audits OLDEST -> NEWEST;
--   * another lane audits NEWEST -> OLDEST;
--   * the intended meeting region is the R423/R486/R492/R501 direct-companion
--     convergence, not an assumption that either pass is complete by itself.
--
-- DATE DISCIPLINE
-- ---------------
-- Commit/source-first-appearance and public-facing exposure are independent
-- clocks.  A PR-open time is recorded as publicPRSurface, a merge time as
-- publicMergeSurface, and neither is silently substituted for first source
-- implementation.  Where no separate PR/publication surface has been recovered
-- we say so explicitly rather than treating commit time as publication time.
--
-- This is compatible with the repository-native temporal ontology being
-- developed on the parallel chronology lane (`FirstImplementationTimestampExact`):
-- firstImplementation, firstPullRequest, firstMerge, firstPublication and
-- externalRelease are distinct events.  We do not duplicate that module here
-- while the branches are still being reconciled.
--
-- Nix/build-environment archaeology is intentionally OUT OF SCOPE here.  This
-- is a provenance/path-tracing audit over mathematical and representational
-- artefacts, commits, PR/tranche relationships, same-object welds, and residual
-- consumers.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Physics.Closure.NSForensicSignedRouteLineageAuditExact as Lineage

------------------------------------------------------------------------
-- Audit direction and scope are first-class.
------------------------------------------------------------------------

data AuditDirection : Set where
  oldestToNewest : AuditDirection
  newestToOldest : AuditDirection

data AuditScope : Set where
  provenancePathTracing : AuditScope
  buildEnvironmentArchaeology : AuditScope

data MatchBasis : Set where
  exactName : MatchBasis
  semanticAlias : MatchBasis
  sameCarrierEquality : MatchBasis
  sameConsumerShape : MatchBasis

data EvidenceGrade : Set where
  chronologyOnly : EvidenceGrade
  structuralPrecursor : EvidenceGrade
  candidateWholeProblem : EvidenceGrade
  problemShape : EvidenceGrade
  exactCarrier : EvidenceGrade
  exactEqualityWeld : EvidenceGrade
  canonicalConsumer : EvidenceGrade

data AuditDisposition : Set where
  include : AuditDisposition
  defer : AuditDisposition
  rejectAsIdentity : AuditDisposition

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

------------------------------------------------------------------------
-- Commit/publication/public-surface provenance.
------------------------------------------------------------------------

data PublicSurfaceKind : Set where
  noSeparatePublicSurfaceRecovered : PublicSurfaceKind
  publicPRSurface : PublicSurfaceKind
  publicMergeSurface : PublicSurfaceKind
  externalPublicationSurface : PublicSurfaceKind

record DatedPublicSurface : Set where
  constructor dated-public-surface
  field
    label : String
    sourceCommit : String
    sourceCommitUTC : String
    publicKind : PublicSurfaceKind
    publicLocator : String
    publicOpenedUTC : String
    publicMergedUTC : String
    note : String

open DatedPublicSurface public

-- Earlier whole-problem/candidate roadmap receipts.  These predate the July
-- signed-resolvent analytic assembly, but inspection of the owning files shows
-- that they are candidate/global-passage grammar rather than the later literal
-- signed cutoff-uniform producer.
jun12FinalStateSurface : DatedPublicSurface
jun12FinalStateSurface = dated-public-surface
  "NSFinalStateReceipt candidate whole-problem roadmap"
  "66ac13c9b9c3e942ed80242957b237cde61bf662"
  "2026-06-12T06:02:01Z"
  noSeparatePublicSurfaceRecovered
  "DASHI/Physics/Closure/NSFinalStateReceipt.agda"
  "not separately recovered"
  "not separately recovered"
  "source receipt leaves uniform enstrophy/vorticity, continuum BKM, global smoothness and Clay closure open"

jun12CandidateBKMSurface : DatedPublicSurface
jun12CandidateBKMSurface = dated-public-surface
  "candidate-complete enstrophy/vorticity/BKM/global-regularity passage grammar"
  "f545fbf5a9cc792e3717033da0bdbd42aaa8337c"
  "2026-06-12T06:05:55Z"
  noSeparatePublicSurfaceRecovered
  "DASHI/Physics/Closure/NSCandidateCompleteEnstrophyBKMPassageReceipt.agda"
  "not separately recovered"
  "not separately recovered"
  "candidate passage recorded; uniform vorticity-Linf, continuum BKM and Clay closure remain false on the owning receipt"

jun13CandidateClosureSurface : DatedPublicSurface
jun13CandidateClosureSurface = dated-public-surface
  "candidate/current-state globalRegularityClosed=true transition"
  "b009e8e96de2f158a74e78f9765a7f83510185b6"
  "2026-06-13T13:19:51Z"
  noSeparatePublicSurfaceRecovered
  "source commit/current-state receipt"
  "not separately recovered"
  "not separately recovered"
  "records a local current-state closure claim while Clay promotion remains false; not identified with the later literal signed-resolvent theorem carrier"

-- Public PR exposure is recorded separately from merge/commit chronology.
pr140Surface : DatedPublicSurface
pr140Surface = dated-public-surface
  "PR #140 compact-Gamma signed-response/Schur/tail architecture"
  "e64a38ab617cf88035555a07a223afe46480df0e"
  "2026-07-20T06:17:05Z"
  publicPRSurface
  "pull/140"
  "2026-07-19T15:36:26Z"
  "2026-07-20T06:17:05Z"
  "PR public surface predates merge; signed response and nonnegative pair majorant are explicitly distinct"

pr145Surface : DatedPublicSurface
pr145Surface = dated-public-surface
  "PR #145 rational six-mode Wall1 Schur/resolvent/gap packet"
  "8905dc5c4c3389f18698f1669040dcf5923af0c6"
  "2026-07-20T03:02:06Z"
  publicPRSurface
  "pull/145"
  "2026-07-20T01:50:34Z"
  "2026-07-20T03:02:06Z"
  "public finite Schur/resolvent/gap packet; physical representation remains mandatory"

pr227Surface : DatedPublicSurface
pr227Surface = dated-public-surface
  "PR #227 cross-pollinated compact-Gamma analytic closure stack"
  "c2b313a0878b0281781dd7a1bf3ae851d24af8d9"
  "2026-07-20T09:42:15Z"
  publicPRSurface
  "pull/227"
  "2026-07-20T06:38:17Z"
  "2026-07-20T09:42:15Z"
  "public integration of differentiated triads, exact full-shell pair incidence, tail, Galerkin, invariant-region and BKM architecture"

pr255Surface : DatedPublicSurface
pr255Surface = dated-public-surface
  "PR #255 concrete far-tail commutator decay"
  "bc9a627985cf4140ee10260f6399050aacf5cba4"
  "2026-07-20T15:09:40Z"
  publicPRSurface
  "pull/255"
  "2026-07-20T14:52:19Z"
  "2026-07-20T15:09:40Z"
  "public far-low commutator and far-high tail theorem surfaces"

pr336Surface : DatedPublicSurface
pr336Surface = dated-public-surface
  "PR #336 exact Wall-I signed multiplier-difference commutator frontier"
  "68ab8ffbcf5c0aa791720a454dbeb1631ea933b2"
  "2026-07-25T07:09:05Z"
  publicPRSurface
  "pull/336"
  "2026-07-25T04:57:13Z"
  "2026-07-25T07:09:05Z"
  "public signed K_diff/absolute K_absdiff separation and sign-sensitive frontier"

pr338Surface : DatedPublicSurface
pr338Surface = dated-public-surface
  "PR #338 Stage-3 signed physical/final-problem assembly"
  "92316f005def176f490ea5c26fd7ad85017090cc"
  "2026-07-27T05:15:48Z"
  publicPRSurface
  "pull/338"
  "2026-07-25T10:42:25Z"
  "2026-07-27T05:15:48Z"
  "PR already public before the Jul26 source commits; Jul26 exact signed coefficient/gap/global composition appear within this public tranche before merge"

pr820Surface : DatedPublicSurface
pr820Surface = dated-public-surface
  "PR #820 restore canonical R423 target after Cauchy archaeology"
  "2c2792478ae38bc23c5efafdbfa68171fdedc9e4"
  "2026-09-09T03:34:17Z"
  publicPRSurface
  "pull/820"
  "2026-09-07T13:50:12Z"
  "2026-09-09T03:34:17Z"
  "R486 source commit occurs after PR opened; public PR chronology and first implementation chronology remain separate"

pr825Surface : DatedPublicSurface
pr825Surface = dated-public-surface
  "PR #825 literal R406/direct-resolvent terminal cone"
  "bc57debbfae2446869b805543855b289866a3437"
  "2026-09-09T03:34:17Z"
  publicPRSurface
  "pull/825"
  "2026-09-07T17:52:01Z"
  "2026-09-09T03:34:17Z"
  "contains R496-R503 direct-resolvent cone including R501; source commits remain the first-implementation clock"

publicSurfaceChronology : List DatedPublicSurface
publicSurfaceChronology =
  jun12FinalStateSurface ∷ jun12CandidateBKMSurface ∷ jun13CandidateClosureSurface ∷
  pr140Surface ∷ pr145Surface ∷ pr227Surface ∷ pr255Surface ∷ pr336Surface ∷
  pr338Surface ∷ pr820Surface ∷ pr825Surface ∷ []

commitDateEqualsPublicationDateByDefault : Bool
commitDateEqualsPublicationDateByDefault = false

prOpenDateEqualsMergeDateByDefault : Bool
prOpenDateEqualsMergeDateByDefault = false

------------------------------------------------------------------------
-- What counts as a systematic audit step.
------------------------------------------------------------------------

record AuditStep : Set where
  constructor audit-step
  field
    fromLabel : String
    toLabel : String
    matchBasis : MatchBasis
    evidenceGrade : EvidenceGrade
    disposition : AuditDisposition
    reason : String

open AuditStep public

janToJuneStep : AuditStep
janToJuneStep = audit-step
  "dashiCFD signed/support and theta/signed-transfer experiments"
  "June candidate whole-problem roadmap surfaces"
  semanticAlias structuralPrecursor include
  "cross-repo sign/support/residue and barrier objects precede a formal candidate enstrophy/vorticity/BKM/global roadmap; neither is identified with the later signed-resolvent carrier"

juneCandidateStep : AuditStep
juneCandidateStep = audit-step
  "Jun12-Jun13 candidate whole-problem/global-regularity receipts"
  "Jul20-Jul26 signed analytic final-problem assembly"
  sameConsumerShape candidateWholeProblem include
  "June records global passage/closure grammar and a local current-state closure claim, but does not yet expose the later exact signed physical coefficient plus cutoff-uniform signed-resolvent producer; July remains earliest recovered assembly of that analytic problem"

julyAssemblyStep : AuditStep
julyAssemblyStep = audit-step
  "Jul20 distributed resolvent/Schur/tail/Galerkin architecture"
  "Jul26 assembled final-problem specification"
  sameConsumerShape problemShape include
  "all principal coordinates of the later terminal analytic problem are simultaneously present, but the missing quantitative signed estimate is not thereby proved"

augustPhysicalizationStep : AuditStep
augustPhysicalizationStep = audit-step
  "Jul26 signed physical specification"
  "Aug08-Aug31 physical/signed/resolvent maturation"
  semanticAlias problemShape include
  "trace physical specialization, removal of positive-majorant dependence, and reuse of existing consumers rather than treating each new round label as a new problem"

r375SameObjectStep : AuditStep
r375SameObjectStep = audit-step
  "R353 generic signed Gram family"
  "R375/R377/R379 literal physical Package-A family"
  sameCarrierEquality exactCarrier include
  "companion/integration become definitionally physical and caller-selectable Gram/transport coordinates are removed"

r406CriticalStep : AuditStep
r406CriticalStep = audit-step
  "R290/R406 signed remainder"
  "R410/R414/R422 critical-barrier route"
  sameCarrierEquality exactEqualityWeld include
  "the old critical remainder is made definitionally the literal R406 remainder integral and actual R290 pair derivatives reach the same R406 flux"

r423CanonicalStep : AuditStep
r423CanonicalStep = audit-step
  "signed quadratic-companion forcing cross"
  "R423 canonical cutoff-uniform signed companion consumer"
  sameCarrierEquality canonicalConsumer include
  "R423 forbids alternate positive/Wiener companions and second remainder estimates; it names the same-object producer"

handoffStep : AuditStep
handoffStep = audit-step
  "R423 canonical signed companion target"
  "R486/R492/R501 restored/direct-companion convergence"
  semanticAlias canonicalConsumer include
  "meeting seam with newest-to-oldest audit: later archaeology restores R423, reinstates same-object firewall, then compiles the direct resolvent companion back into R423"

systematicAuditSteps : List AuditStep
systematicAuditSteps =
  janToJuneStep ∷ juneCandidateStep ∷ julyAssemblyStep ∷ augustPhysicalizationStep ∷
  r375SameObjectStep ∷ r406CriticalStep ∷ r423CanonicalStep ∷ handoffStep ∷ []

------------------------------------------------------------------------
-- Mandatory firewalls for provenance interpretation.
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
-- Explicit audit findings inherited from the forensic ledger.
------------------------------------------------------------------------

earliestRecoveredWholeProblemRoadmapPredatesJuly : Bool
earliestRecoveredWholeProblemRoadmapPredatesJuly = true

earliestRecoveredAssemblyIsJuly26 : Bool
earliestRecoveredAssemblyIsJuly26 =
  Lineage.earliestRecoveredFinalProblemSpecificationIsJuly26

july26IsClaimedSolved : Bool
july26IsClaimedSolved = Lineage.july26ClaimedSolved

signedRouteRequiresOldPositiveMajorant : Bool
signedRouteRequiresOldPositiveMajorant =
  Lineage.r373SignedRouteBypassesNonnegativeMajorant

r375CompanionIsDefinitionallyPhysical : Bool
r375CompanionIsDefinitionallyPhysical =
  Lineage.r375R353IsDefinitionallyPhysical

r410TargetIsLiteralR406 : Bool
r410TargetIsLiteralR406 = Lineage.r410TargetIsLiteralR406

r414NeedsSecondRemainder : Bool
r414NeedsSecondRemainder = Lineage.r414SecondRemainderNeeded

r423NeedsPositiveWienerEnvelope : Bool
r423NeedsPositiveWienerEnvelope =
  Lineage.r423PositiveWienerEnvelopeRequired

r423RemainingProducerIsUniformSignedCompanionBudget : Bool
r423RemainingProducerIsUniformSignedCompanionBudget =
  Lineage.r423RemainingProducerIsCutoffUniformSignedCompanionBudget

------------------------------------------------------------------------
-- Current systematic-audit checkpoint.
------------------------------------------------------------------------

oldestForwardPassActive : Bool
oldestForwardPassActive = true

newestBackwardPassExistsAsSeparateLane : Bool
newestBackwardPassExistsAsSeparateLane = true

passesHaveFullyReconciledEveryIntermediateAlias : Bool
passesHaveFullyReconciledEveryIntermediateAlias = false

currentMeetingRegion : String
currentMeetingRegion =
  "R423 canonical target -> R486 restoration -> R492 same-object firewall -> R501 direct resolvent companion -> R503/R541/R573/R584"

currentHistoricalHypothesis : String
currentHistoricalHypothesis =
  "Whole-problem candidate/global-regularity roadmaps are recovered by 2026-06-12, but the earliest recovered assembly of the later exact signed/cutoff-uniform analytic problem remains 2026-07-26; later tranches primarily physicalize, repair same-object provenance, remove lossy majorants/plumbing, or re-express that same missing estimate."

nextOldestForwardObligation : String
nextOldestForwardObligation =
  "Continue between the June whole-problem roadmap and Jul26 signed analytic assembly, then forward through R423->R486/R492/R501; reconcile semantic aliases and public/commit clocks without inferring same-object identity from chronology."

systematicAuditIsAppendOnly : Bool
systematicAuditIsAppendOnly = true

historicalReceiptsMayBeReclassifiedButNotRewritten : Bool
historicalReceiptsMayBeReclassifiedButNotRewritten = true

------------------------------------------------------------------------
-- Expected polarities.
------------------------------------------------------------------------

currentDirectionIsOldestToNewest : currentDirection ≡ oldestToNewest
currentDirectionIsOldestToNewest = refl

currentScopeIsProvenancePathTracing : currentScope ≡ provenancePathTracing
currentScopeIsProvenancePathTracing = refl

roundNumbersArePrimarySearchKeyIsFalse : roundNumbersArePrimarySearchKey ≡ false
roundNumbersArePrimarySearchKeyIsFalse = refl

semanticAliasesMustBeSearchedIsTrue : semanticAliasesMustBeSearched ≡ true
semanticAliasesMustBeSearchedIsTrue = refl

prsAndTranchesMustBeComposedIsTrue : prsAndTranchesMustBeComposed ≡ true
prsAndTranchesMustBeComposedIsTrue = refl

commitDateEqualsPublicationDateByDefaultIsFalse : commitDateEqualsPublicationDateByDefault ≡ false
commitDateEqualsPublicationDateByDefaultIsFalse = refl

prOpenDateEqualsMergeDateByDefaultIsFalse : prOpenDateEqualsMergeDateByDefault ≡ false
prOpenDateEqualsMergeDateByDefaultIsFalse = refl

earliestRecoveredWholeProblemRoadmapPredatesJulyIsTrue :
  earliestRecoveredWholeProblemRoadmapPredatesJuly ≡ true
earliestRecoveredWholeProblemRoadmapPredatesJulyIsTrue = refl

earliestRecoveredAssemblyIsJuly26IsTrue : earliestRecoveredAssemblyIsJuly26 ≡ true
earliestRecoveredAssemblyIsJuly26IsTrue =
  Lineage.earliestRecoveredFinalProblemSpecificationIsJuly26IsTrue

july26IsClaimedSolvedIsFalse : july26IsClaimedSolved ≡ false
july26IsClaimedSolvedIsFalse = Lineage.july26ClaimedSolvedIsFalse

signedRouteRequiresOldPositiveMajorantIsFalse :
  signedRouteRequiresOldPositiveMajorant ≡ false
signedRouteRequiresOldPositiveMajorantIsFalse =
  Lineage.r373SignedRouteBypassesNonnegativeMajorantIsFalse

r375CompanionIsDefinitionallyPhysicalIsTrue :
  r375CompanionIsDefinitionallyPhysical ≡ true
r375CompanionIsDefinitionallyPhysicalIsTrue =
  Lineage.r375R353IsDefinitionallyPhysicalIsTrue

r410TargetIsLiteralR406IsTrue : r410TargetIsLiteralR406 ≡ true
r410TargetIsLiteralR406IsTrue = Lineage.r410TargetIsLiteralR406IsTrue

r414NeedsSecondRemainderIsFalse : r414NeedsSecondRemainder ≡ false
r414NeedsSecondRemainderIsFalse = Lineage.r414SecondRemainderNeededIsFalse

r423NeedsPositiveWienerEnvelopeIsFalse :
  r423NeedsPositiveWienerEnvelope ≡ false
r423NeedsPositiveWienerEnvelopeIsFalse =
  Lineage.r423PositiveWienerEnvelopeRequiredIsFalse

oldestForwardPassActiveIsTrue : oldestForwardPassActive ≡ true
oldestForwardPassActiveIsTrue = refl

passesFullyReconciledIsFalse : passesHaveFullyReconciledEveryIntermediateAlias ≡ false
passesFullyReconciledIsFalse = refl

systematicAuditIsAppendOnlyIsTrue : systematicAuditIsAppendOnly ≡ true
systematicAuditIsAppendOnlyIsTrue = refl
