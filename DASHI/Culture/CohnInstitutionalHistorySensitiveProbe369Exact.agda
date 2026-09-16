module DASHI.Culture.CohnInstitutionalHistorySensitiveProbe369Exact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Core.IntersectionalNonFactorability as INF
import DASHI.Culture.CohnInstitutionalResidualDiagnosisExact as Diagnosis
import DASHI.Culture.CohnInstitutionalProofSearchResidualPortfolioReuseExact as PortfolioReuse
import DASHI.Reasoning.Spacy369AdaptiveConsumerProbeSchedulerExact as Scheduler369
import DASHI.Reasoning.Spacy369ConsumerScheduleNonfactorabilityExact as Schedule369

------------------------------------------------------------------------
-- COHN INSTITUTIONAL EPISTEMICS x HISTORY-SENSITIVE PROBE SCHEDULING x 369
--
-- This is a consumer-return bridge over already-owned machinery.
--
-- The Cohn lane already supplies source-bounded candidate residual families
-- and a concrete institutional collision.  The proof-search reuse owner already
-- redirects generic portfolio/search machinery to canonical owners.  The 369
-- reasoning lane independently proves that the same materialised forward
-- evidence can support different downstream information policies when the
-- declared consumer changes.
--
-- The only new theorem here isolates another independent coordinate: retained
-- inquiry history.  Even when the current institutional statement AND declared
-- consumer are held fixed, different live residual histories can require
-- different next probes.
------------------------------------------------------------------------

existingSearchOwnersReused : Bool
existingSearchOwnersReused = true

existingPortfolioBoundary :
  PortfolioReuse.ProofSearchResidualPortfolioReuseBoundary
existingPortfolioBoundary = PortfolioReuse.canonicalReuseBoundary

existing369SchedulerBoundary :
  Scheduler369.Spacy369AdaptiveConsumerProbeSchedulerBoundary
existing369SchedulerBoundary =
  Scheduler369.canonicalSpacy369AdaptiveConsumerProbeSchedulerBoundary

existing369ScheduleNonfactorabilityBoundary :
  Schedule369.Spacy369ConsumerScheduleNonfactorabilityBoundary
existing369ScheduleNonfactorabilityBoundary =
  Schedule369.canonicalSpacy369ConsumerScheduleNonfactorabilityBoundary

------------------------------------------------------------------------
-- Finite institutional inquiry fixture.
------------------------------------------------------------------------

data InstitutionalInquiryWorld : Set where
  sameStatementWithLiveHermeneuticalRefusal : InstitutionalInquiryWorld
  sameStatementWithUnpaidLineageDebt : InstitutionalInquiryWorld

data CurrentInstitutionalStatement : Set where
  sameAdmittedInstitutionalStatement : CurrentInstitutionalStatement

data DeclaredInstitutionalConsumer : Set where
  interventionAuditConsumer : DeclaredInstitutionalConsumer

data InstitutionalNextProbe : Set where
  probeHermeneuticalRefusal : InstitutionalNextProbe
  probeSourceLineage : InstitutionalNextProbe

currentInstitutionalStatement :
  InstitutionalInquiryWorld → CurrentInstitutionalStatement
currentInstitutionalStatement _ = sameAdmittedInstitutionalStatement

declaredInstitutionalConsumer :
  InstitutionalInquiryWorld → DeclaredInstitutionalConsumer
declaredInstitutionalConsumer _ = interventionAuditConsumer

nextInstitutionalProbe : InstitutionalInquiryWorld → InstitutionalNextProbe
nextInstitutionalProbe sameStatementWithLiveHermeneuticalRefusal =
  probeHermeneuticalRefusal
nextInstitutionalProbe sameStatementWithUnpaidLineageDebt =
  probeSourceLineage

------------------------------------------------------------------------
-- Current statement alone is too coarse.
------------------------------------------------------------------------

currentStatementCollision :
  currentInstitutionalStatement sameStatementWithLiveHermeneuticalRefusal
  ≡ currentInstitutionalStatement sameStatementWithUnpaidLineageDebt
currentStatementCollision = refl

nextProbeDifference :
  nextInstitutionalProbe sameStatementWithLiveHermeneuticalRefusal
  ≡ nextInstitutionalProbe sameStatementWithUnpaidLineageDebt → ⊥
nextProbeDifference ()

currentStatementDoesNotDetermineNextProbe :
  INF.FactorsThrough currentInstitutionalStatement nextInstitutionalProbe → ⊥
currentStatementDoesNotDetermineNextProbe =
  INF.witnessRulesOutEveryFlatFactorisation
    (INF.nonFactorabilityWitness
      sameStatementWithLiveHermeneuticalRefusal
      sameStatementWithUnpaidLineageDebt
      currentStatementCollision
      nextProbeDifference)

------------------------------------------------------------------------
-- Stronger collision: statement + declared consumer are both fixed.
-- History is therefore not being smuggled into the theorem through a consumer
-- change; the 369 consumer-relative scheduler is an independent donor axis.
------------------------------------------------------------------------

statementAndConsumer :
  InstitutionalInquiryWorld →
  CurrentInstitutionalStatement × DeclaredInstitutionalConsumer
statementAndConsumer world =
  currentInstitutionalStatement world , declaredInstitutionalConsumer world

sameStatementAndConsumer :
  statementAndConsumer sameStatementWithLiveHermeneuticalRefusal
  ≡ statementAndConsumer sameStatementWithUnpaidLineageDebt
sameStatementAndConsumer = refl

statementAndConsumerDoNotDetermineNextProbe :
  INF.FactorsThrough statementAndConsumer nextInstitutionalProbe → ⊥
statementAndConsumerDoNotDetermineNextProbe =
  INF.witnessRulesOutEveryFlatFactorisation
    (INF.nonFactorabilityWitness
      sameStatementWithLiveHermeneuticalRefusal
      sameStatementWithUnpaidLineageDebt
      sameStatementAndConsumer
      nextProbeDifference)

------------------------------------------------------------------------
-- Application candidates are reused, not redefined.
------------------------------------------------------------------------

selectedFixtureResidualIsHermeneuticalRefusal :
  Diagnosis.selectedResidualIsHermeneuticalRefusal ≡ true
selectedFixtureResidualIsHermeneuticalRefusal = refl

portfolioAlreadyOwned :
  PortfolioReuse.genericResidualPortfolioAlreadyOwned
    PortfolioReuse.canonicalReuseBoundary ≡ true
portfolioAlreadyOwned = refl

newGenericSetCoverStillNotRequired :
  PortfolioReuse.newGenericSetCoverSubsystemRequired
    PortfolioReuse.canonicalReuseBoundary ≡ false
newGenericSetCoverStillNotRequired = refl

------------------------------------------------------------------------
-- 369 scheduler pins.
------------------------------------------------------------------------

declaredConsumerMayChangeProbePath369 :
  Scheduler369.changingDeclaredConsumersMayChangeProbePath
    Scheduler369.canonicalSpacy369AdaptiveConsumerProbeSchedulerBoundary ≡ true
declaredConsumerMayChangeProbePath369 = refl

consumerChangeDoesNotRewriteMaterialisedEvidence369 :
  Scheduler369.addingConsumerRewritesMaterialisedParserEvidence
    Scheduler369.canonicalSpacy369AdaptiveConsumerProbeSchedulerBoundary ≡ false
consumerChangeDoesNotRewriteMaterialisedEvidence369 = refl

materialisedSurfaceAloneDoesNotDetermineSchedule369 :
  Schedule369.parserEvidenceAloneDeterminesDownstreamProbeSchedule
    Schedule369.canonicalSpacy369ConsumerScheduleNonfactorabilityBoundary ≡ false
materialisedSurfaceAloneDoesNotDetermineSchedule369 = refl

differentConsumersMayShareProbe369 :
  Schedule369.differentConsumersMayShareOneProbe
    Schedule369.canonicalSpacy369ConsumerScheduleNonfactorabilityBoundary ≡ true
differentConsumersMayShareProbe369 = refl

------------------------------------------------------------------------
-- Boundary.
------------------------------------------------------------------------

record HistorySensitiveProbeBoundary : Set where
  constructor history-sensitive-probe-boundary
  field
    currentInstitutionalStatementDeterminesNextProbe : Bool
    statementPlusFixedConsumerDeterminesNextProbe : Bool
    retainedInquiryHistoryMayChangeNextProbe : Bool
    declaredConsumerMayChangeProbePath : Bool
    probePolicyChangeRewritesCurrentInstitutionalSurface : Bool
    sameProbeUniquelyIdentifiesConsumer : Bool
    existingResidualPortfolioAlreadyOwned : Bool
    newPlannerRequired : Bool
    existing369SchedulerReused : Bool
    institutionalFixtureProvesRealHistoricalRefusal : Bool

open HistorySensitiveProbeBoundary public

canonicalHistorySensitiveProbeBoundary : HistorySensitiveProbeBoundary
canonicalHistorySensitiveProbeBoundary =
  history-sensitive-probe-boundary
    false
    false
    true
    true
    false
    false
    true
    false
    true
    false

bridgeSummary : String
bridgeSummary =
  "The same current institutional statement and even the same declared consumer can require different next probes when retained inquiry history differs. Cohn supplies application-specific residual candidates; existing proof-search portfolio owners supply admission/Pareto/reopening; the 369 scheduler independently proves that consumer changes can alter information policy without rewriting materialised evidence. No new planner, dialectic ontology, or source-derived historical fact is introduced."
