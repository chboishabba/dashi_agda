module DASHI.Cognition.CCDCOEP3CognitiveWarfareArtDiscriminatorExact where

------------------------------------------------------------------------
-- SOURCE-CREDITED CROSS-DOMAIN CONSUMER, not a new causal calculus.
--
-- Existing DASHI owners:
--   CCDCOEP3CausalTrialecticInteractionExact (finite observational
--   confounding, hostile-purpose and revisability non-identification)
--   CCDCOEP3GCCExecutedCampaignSourceExact (original GCC/PR firm,
--   archived media, separate scholarly review and Exxon corpus roles)
--   CCDCOEP3ClimateObservedActivityAndCorpusExact (original 2017
--   Supran & Oreskes publication; document-content != treatment effect)
--   CriticalArtEditionAuthorityExact and critical-art genre owner
--   (film/edition metadata and fictional representation boundaries).
--
-- Original authors retain ALL creative, conceptual, historical and
-- empirical contributions; this is DASHI's bounded formal reuse.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Bool using (false)
open import Data.Empty using (⊥)

import DASHI.Core.IntersectionalNonFactorability as NF
import DASHI.Core.DiscriminatorSynthesisExact as D
import DASHI.Cognition.CCDCOEP3CausalTrialecticInteractionExact as Causal
import DASHI.Cognition.CCDCOEP3GCCExecutedCampaignSourceExact as GCC
import DASHI.Cognition.CCDCOEP3ClimateObservedActivityAndCorpusExact as Corpus
import DASHI.Cognition.CCDCOEP3CulturalSourceGenreExact as Culture
import DASHI.Culture.CriticalArtEditionAuthorityExact as Edition

-- A dated published source, a historical actor's self-asserted success,
-- a coded document and a measured response are not interchangeable.

originalGCCHistoricalSourceTypesDoNotCollapse :
  NF.FactorsThrough GCC.flatten GCC.kind → ⊥
originalGCCHistoricalSourceTypesDoNotCollapse =
  GCC.evidenceKindDoesNotFactorThroughGenericTopic

sourceKindDiscriminatesAgencyReportFromArchivedPress :
  D.BundleSeparates GCC.sourceIdentityProbe
    GCC.harrisonFirmCaseHistory GCC.gccHeldMediaClippings1993
sourceKindDiscriminatesAgencyReportFromArchivedPress =
  GCC.sourceIdentitySeparates

publishedDocumentStatisticsNotHumanTreatmentEffect :
  Corpus.PublishedCorpusMeasurement.isHumanTreatmentEffect
    Corpus.originalPublishedCorpusMeasurement ≡
  false
publishedDocumentStatisticsNotHumanTreatmentEffect =
  Corpus.documentContentIsNotPublicBeliefEffect

-- Even with a measured outcome, observational association can fit
-- distinct causal structures. These are ORIGINAL finite theorem owners.
observationalCooccurrenceCannotIdentifyCause :
  NF.FactorsThrough Causal.observedPairFor Causal.interventionalProbe → ⊥
observationalCooccurrenceCannotIdentifyCause =
  Causal.observationalAssociationDoesNotIdentifyCausation

measuredEffectAloneCannotIdentifyHostilePurpose :
  NF.FactorsThrough Causal.observedEffect Causal.worldPurpose → ⊥
measuredEffectAloneCannotIdentifyHostilePurpose =
  Causal.effectCannotIdentifyHostilePurpose

publicNarrativeAgreementCannotDetermineRevisability :
  NF.FactorsThrough Causal.publicCoherence Causal.evidenceRevision → ⊥
publicNarrativeAgreementCannotDetermineRevisability =
  Causal.narrativeCoherenceDoesNotDetermineRevisability

prospectiveEvidenceResponseDiscriminator :
  D.BundleSeparates Causal.revisabilityDistinguishingProbe
    Causal.coherentAndContestable Causal.coherentButSelfSealed
prospectiveEvidenceResponseDiscriminator =
  Causal.revisionProbeSeparates

prospectiveControlledEffectDiscriminator :
  D.BundleSeparates Causal.counterfactualDistinguishingProbe
    Causal.directEffect Causal.commonCause
prospectiveControlledEffectDiscriminator =
  Causal.counterfactualProbeSeparates

-- Original film publishers / original film creators own what a work
-- depicts. Source metadata cannot be promoted to a scene or measured
-- audience effect, much less an intentionally hostile operation.
filmEditionMetadataNotMeasuredAudienceResponse :
  (edition : Edition.Edition) →
  Edition.editionGrade edition ≡ Edition.responseEmpiricallyMeasured → ⊥
filmEditionMetadataNotMeasuredAudienceResponse =
  Edition.sourceMetadataNotMeasuredAudience

fictionalSatireNotIndependentAudienceObservation :
  Culture.CulturalWork.status Culture.dontLookUp2021
  ≡ Culture.independentlyVerifiedObservation → ⊥
fictionalSatireNotIndependentAudienceObservation =
  Culture.satireNotEmpiricalObservation

-- A substantive real-world cognitive-warfare finding requires all
-- listed independent gates. The type below is a REQUIREMENT, not
-- a proof that they are satisfied by any selected historical actor.
record OperationAdmission (Evidence : Set) : Set₁ where
  field
    originalIntervention : Evidence
    independentExposureReceipt : Evidence
    validatedMechanismMeasurement : Evidence
    causalDiscriminationReceipt : Evidence
    independentlySourcedIntentAndTargeting : Evidence
    historicalAttributionReceipt : Evidence

-- No specific GCC/API/Exxon/film case is instantiated as an operation.
-- The existing 1998 proposal is never merged with a separate 1993 GCC
-- effort, and Hollywood film form never supplies an original treatment.
