module DASHI.Culture.CohnInstitutionalEpistemicActivismConsumer369Exact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.String using (String)

import DASHI.Core.AttributedSourceCore as Attribution
import DASHI.Core.IntersectionalNonFactorability as INF
import DASHI.Culture.CohnInstitutionalIbrahimDeweyAcquisitionExtensionFourExact as SourceFollow
import DASHI.Governance.SituatedDissentDeceptionAssayExact as Dissent
import DASHI.Law.SensibLawDialecticalProofSearchExact as Dialectic
import DASHI.Reasoning.Spacy369AdaptiveConsumerProbeSchedulerExact as Scheduler

------------------------------------------------------------------------
-- EPISTEMIC-ACTIVISM / PROPER-UPTAKE CONSUMER RETURN
--
-- Medina 2023 contributes a source-bounded candidate family concerning
-- epistemic activism / resistant uptake. The theorem-bearing consumer is
-- reused from SituatedDissentDeceptionAssayExact: the same recorded-dissent
-- surface can coexist with materially effective or decorative dissent.
--
-- This owner does not identify Medina's theory with the DASHI dissent assay or
-- with the spaCy/369 fixture. It returns the source candidate into canonical
-- discriminator, dialectical-search and consumer-relative scheduling grammar.
------------------------------------------------------------------------

epistemicActivismSource : Attribution.AttributedSource
epistemicActivismSource = SourceFollow.medinaEpistemologyOfProtest

epistemicActivismTraversal = SourceFollow.medinaToEpistemicActivism

------------------------------------------------------------------------
-- Concrete existing consumer: recorded dissent does not determine whether the
-- dissent is materially effective.
------------------------------------------------------------------------

effectiveUptakeNonfactorability :
  INF.FactorsThrough Dissent.recordedDissent Dissent.dissentEffect → ⊥
effectiveUptakeNonfactorability = Dissent.recordedDissentCannotRecoverEffectiveVeto

------------------------------------------------------------------------
-- The discriminator is a proof-search role, not a doctrine or empirical claim.
------------------------------------------------------------------------

uptakeSearchDiscriminator : Dialectic.SearchDiscriminator
uptakeSearchDiscriminator = Dialectic.searchDiscriminator
  "institutional dissent / resistant-uptake consumer"
  "recorded dissent with evidence of material response, protected correction channel, or changed transition"
  "recorded dissent that is procedurally visible but leaves the transition unchanged"
  "effective uptake / dissent effect"
  "same recorded-dissent surface; distinguish materially effective from decorative uptake"

dialecticalSearchBoundary : Dialectic.DialecticalSearchBoundary
dialecticalSearchBoundary = Dialectic.canonicalDialecticalSearchBoundary

------------------------------------------------------------------------
-- History/consumer-sensitive next probe.
------------------------------------------------------------------------

data UptakeProbe : Set where
  noFurtherUptakeProbe : UptakeProbe
  inspectEffectiveUptake : UptakeProbe

nextUptakeProbe : Dissent.DissentState → UptakeProbe
nextUptakeProbe Dissent.protectedEffectiveDissent = noFurtherUptakeProbe
nextUptakeProbe Dissent.managedDecorativeDissent = inspectEffectiveUptake

nextProbeDiffers :
  nextUptakeProbe Dissent.protectedEffectiveDissent
  ≡ nextUptakeProbe Dissent.managedDecorativeDissent → ⊥
nextProbeDiffers ()

recordedDissentCannotDetermineNextProbe :
  INF.FactorsThrough Dissent.recordedDissent nextUptakeProbe → ⊥
recordedDissentCannotDetermineNextProbe =
  INF.witnessRulesOutEveryFlatFactorisation
    (INF.nonFactorabilityWitness
      Dissent.protectedEffectiveDissent
      Dissent.managedDecorativeDissent
      Dissent.sameDissentSurface
      nextProbeDiffers)

------------------------------------------------------------------------
-- 369 consumer-relative scheduling reuse.
------------------------------------------------------------------------

data UptakeConsumer : Set where
  recordOnlyConsumer : UptakeConsumer
  effectiveUptakeConsumer : UptakeConsumer

uptakePlan : UptakeConsumer → Scheduler.ScheduledPlan
uptakePlan recordOnlyConsumer = Scheduler.stopNow
uptakePlan effectiveUptakeConsumer = Scheduler.runSharedContext

addingEffectiveUptakeConsumerChangesPlan :
  uptakePlan recordOnlyConsumer ≡ uptakePlan effectiveUptakeConsumer → ⊥
addingEffectiveUptakeConsumerChangesPlan ()

materialisedDissentSurface : UptakeConsumer → Dissent.DissentSurface
materialisedDissentSurface _ = Dissent.dissentRecorded

consumerRevisionDoesNotRewriteRecordedDissent :
  materialisedDissentSurface recordOnlyConsumer
  ≡ materialisedDissentSurface effectiveUptakeConsumer
consumerRevisionDoesNotRewriteRecordedDissent = refl

schedulerBoundary : Scheduler.Spacy369AdaptiveConsumerProbeSchedulerBoundary
schedulerBoundary = Scheduler.canonicalSpacy369AdaptiveConsumerProbeSchedulerBoundary

------------------------------------------------------------------------
-- Attribution / semantic firewall.
------------------------------------------------------------------------

record EpistemicActivismConsumerBoundary : Set where
  constructor epistemic-activism-consumer-boundary
  field
    epistemicActivismSourceRetained : Bool
    recordedDissentDeterminesEffectiveUptake : Bool
    recordedDissentDeterminesNextProbe : Bool
    canonicalDialecticalProofSearchReused : Bool
    canonical369SchedulerBoundaryReused : Bool
    medinaSourceOwnsDashiNonfactorability : Bool
    medinaTheoryDefinitionallyEqualsDissentAssay : Bool
    spacyConsumerBundleDefinitionallyEqualsInstitutionalConsumer : Bool
    consumerRevisionRewritesRecordedDissent : Bool

open EpistemicActivismConsumerBoundary public

canonicalEpistemicActivismConsumerBoundary : EpistemicActivismConsumerBoundary
canonicalEpistemicActivismConsumerBoundary = epistemic-activism-consumer-boundary
  true false false true true false false false false

medinaCitationStillDoesNotImportProof :
  Attribution.citationImportsProof epistemicActivismSource ≡ false
medinaCitationStillDoesNotImportProof = refl

------------------------------------------------------------------------
-- Frontier consequence.
------------------------------------------------------------------------

record EpistemicActivismConsumerFrontier : Set where
  constructor epistemic-activism-consumer-frontier
  field
    acquiredCandidate : String
    reusedConsumer : String
    discriminator : String
    proofSearchReuse : String
    schedulerReuse : String
    remainingOpenFamilies : String

open EpistemicActivismConsumerFrontier public

canonicalEpistemicActivismConsumerFrontier : EpistemicActivismConsumerFrontier
canonicalEpistemicActivismConsumerFrontier = epistemic-activism-consumer-frontier
  "Medina 2023 epistemic activism / resistant uptake"
  "SituatedDissentDeceptionAssayExact: recorded dissent != materially effective dissent"
  "effective uptake / dissent effect"
  "SensibLawDialecticalProofSearchExact SearchDiscriminator + support/defeater boundary"
  "Spacy369AdaptiveConsumerProbeSchedulerExact ScheduledPlan + consumer-relative/frozen-evidence boundary"
  "epistemic labour burden and relational research burden remain source-specific; generic burden-distribution neighbours exist but no source-specific institutional fixture is asserted here"
