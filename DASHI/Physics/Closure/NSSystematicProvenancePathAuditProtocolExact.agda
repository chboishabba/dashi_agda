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
  "July formal signed/majorant separation"
  semanticAlias structuralPrecursor include
  "cross-repo methodological precursor: sign/support/residue and barrier objects are tracked without claiming formal same-object identity"

julyAssemblyStep : AuditStep
julyAssemblyStep = audit-step
  "Jul20 distributed resolvent/Schur/tail/Galerkin architecture"
  "Jul26 assembled final-problem specification"
  sameConsumerShape problemShape include
  "all principal coordinates of the later terminal problem are simultaneously present, but the missing quantitative signed estimate is not thereby proved"

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
  janToJuneStep ∷ julyAssemblyStep ∷ augustPhysicalizationStep ∷
  r375SameObjectStep ∷ r406CriticalStep ∷ r423CanonicalStep ∷
  handoffStep ∷ []

------------------------------------------------------------------------
-- Mandatory firewalls for provenance interpretation.
------------------------------------------------------------------------

data ChronologyCreatesIdentity : Set where
data AliasCreatesIdentity : Set where
data SameConsumerShapeCreatesEquality : Set where
data ProblemSpecificationCreatesProof : Set where
data LaterRoundMeansNewProblem : Set where
data PublicRepositoryCreatesExternalInfluence : Set where

chronologyDoesNotCreateIdentity : ChronologyCreatesIdentity → ⊥
chronologyDoesNotCreateIdentity ()

aliasDoesNotCreateIdentity : AliasCreatesIdentity → ⊥
aliasDoesNotCreateIdentity ()

sameShapeDoesNotCreateEquality : SameConsumerShapeCreatesEquality → ⊥
sameShapeDoesNotCreateEquality ()

problemSpecificationDoesNotCreateProof : ProblemSpecificationCreatesProof → ⊥
problemSpecificationDoesNotCreateProof ()

laterRoundDoesNotMeanNewProblem : LaterRoundMeansNewProblem → ⊥
laterRoundDoesNotMeanNewProblem ()

publicRepoDoesNotCreateInfluenceClaim : PublicRepositoryCreatesExternalInfluence → ⊥
publicRepoDoesNotCreateInfluenceClaim ()

------------------------------------------------------------------------
-- Explicit audit findings inherited from the forensic ledger.
------------------------------------------------------------------------

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
  "The final analytic problem was already assembled in distributed form by 2026-07-26; later tranches primarily physicalize, repair same-object provenance, remove lossy majorants/plumbing, or re-express the same cutoff-uniform signed estimate."

nextOldestForwardObligation : String
nextOldestForwardObligation =
  "Continue forward through R423->R486/R492/R501 and reconcile every semantic alias, producer/consumer edge, and representation-loss boundary with the newest-to-oldest pass; do not infer identity without a carrier/equality receipt."

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
