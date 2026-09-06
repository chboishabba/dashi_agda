module DASHI.Cognition.PNF.SensibLawBillyDominantChartRemedyCompressionExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

import DASHI.Core.DominantChartEpistemicCompressionExact as Compression
import DASHI.Core.IntersectionalNonFactorability as INF
import DASHI.Cognition.PNF.SensibLawBillySituatedKnowledgeRemedyAdequacyExact as Situated
import DASHI.Cognition.PNF.SensibLawDeclaredReasonRealizedEffectOperationalExact as Realized

------------------------------------------------------------------------
-- BILLY / TWO-EYED REMEDY AS DOMINANT-CHART COMPRESSION INSTANCE
--
-- The existing Billy owner already provides exact finite collisions.  This file
-- only compiles those witnesses through the generic merged #711 machinery.
------------------------------------------------------------------------

consultationAuthorityCompression :
  Compression.ProjectionInadequacyReceipt
    Situated.consultationSurface
    Situated.authorityParticipation
consultationAuthorityCompression =
  Compression.projection-inadequacy-receipt
    Compression.juridicalRecognitionCompression
    "government consultation record"
    "meaningful consultation / authority-bearing participation consumer"
    "same recorded statement can coexist with erased or preserved community authority"
    Situated.consultationAuthorityWitness
    true refl
    false refl
    false refl
    false refl

consultationReciprocityCompression :
  Compression.ProjectionInadequacyReceipt
    Situated.consultationSurface
    Situated.reciprocalImplementation
consultationReciprocityCompression =
  Compression.projection-inadequacy-receipt
    Compression.administrativeClassificationCompression
    "government consultation record"
    "reciprocal implementation / correction-feedback consumer"
    "same recorded statement can coexist with one-way extraction or reciprocal feedback"
    Situated.consultationReciprocityWitness
    true refl
    false refl
    false refl
    false refl

consultationCannotCarryAuthority :
  INF.FactorsThrough Situated.consultationSurface Situated.authorityParticipation → ⊥
consultationCannotCarryAuthority =
  Compression.projectionCannotFactorTarget consultationAuthorityCompression

consultationCannotCarryReciprocity :
  INF.FactorsThrough Situated.consultationSurface Situated.reciprocalImplementation → ⊥
consultationCannotCarryReciprocity =
  Compression.projectionCannotFactorTarget consultationReciprocityCompression

consultationRewordingCannotRecoverAuthority :
  ∀ {Recharted : Set} →
  (rechart : Situated.ConsultationSurface → Recharted) →
  INF.FactorsThrough
    (λ state → rechart (Situated.consultationSurface state))
    Situated.authorityParticipation → ⊥
consultationRewordingCannotRecoverAuthority =
  Compression.projectionCannotBeRepairedByPostcomposition consultationAuthorityCompression

consultationScoringCannotRecoverReciprocity :
  ∀ {Recharted : Set} →
  (rechart : Situated.ConsultationSurface → Recharted) →
  INF.FactorsThrough
    (λ state → rechart (Situated.consultationSurface state))
    Situated.reciprocalImplementation → ⊥
consultationScoringCannotRecoverReciprocity =
  Compression.projectionCannotBeRepairedByPostcomposition consultationReciprocityCompression

------------------------------------------------------------------------
-- POSIWID / system-operation x-pollination.
------------------------------------------------------------------------

record RemedyOperationalObserverBoundary : Set where
  constructor remedy-operational-observer-boundary
  field
    declaredReasonDeterminesDistribution : Bool
    declaredReasonDeterminesDistributionIsFalse : declaredReasonDeterminesDistribution ≡ false
    declaredRemedyDeterminesRealizedRepair : Bool
    declaredRemedyDeterminesRealizedRepairIsFalse : declaredRemedyDeterminesRealizedRepair ≡ false
    consultationCountDeterminesAuthorityBearingParticipation : Bool
    consultationCountDeterminesAuthorityBearingParticipationIsFalse :
      consultationCountDeterminesAuthorityBearingParticipation ≡ false
    systemAssessmentMustInspectRealizedEffectAndCorrectionResponse : Bool
    systemAssessmentMustInspectRealizedEffectAndCorrectionResponseIsTrue :
      systemAssessmentMustInspectRealizedEffectAndCorrectionResponse ≡ true

canonicalRemedyOperationalObserverBoundary : RemedyOperationalObserverBoundary
canonicalRemedyOperationalObserverBoundary =
  remedy-operational-observer-boundary
    false refl
    false refl
    false refl
    true refl

stateMetricStillDoesNotDetermineCommunityAdequacy :
  Realized.stateDefinedMetricAloneDeterminesCommunityRemedyAdequacy
    Realized.canonicalCommunityDefinedOutcomeBoundary ≡ false
stateMetricStillDoesNotDetermineCommunityAdequacy = refl

correctionFeedbackRemainsOperational :
  Realized.correctionFeedbackIsPartOfSystemOperation
    Realized.canonicalCommunityDefinedOutcomeBoundary ≡ true
correctionFeedbackRemainsOperational = refl

------------------------------------------------------------------------
-- Required repair is richer observation, not a nicer label on extracted data.
------------------------------------------------------------------------

record BillyRemedyResidualCoordinates : Set where
  constructor billy-remedy-residual-coordinates
  field
    authorityCoordinateRequired : Bool
    provenanceCoordinateRequired : Bool
    permissionProtocolCoordinateRequired : Bool
    reciprocalObligationCoordinateRequired : Bool
    communityDefinedOutcomeCoordinateRequired : Bool
    implementationFeedbackCoordinateRequired : Bool

canonicalBillyRemedyResidualCoordinates : BillyRemedyResidualCoordinates
canonicalBillyRemedyResidualCoordinates =
  billy-remedy-residual-coordinates true true true true true true

------------------------------------------------------------------------
-- No-collapse laws.
------------------------------------------------------------------------

data BetterConsultationLabelCreatesCommunityAuthority : Set where
data MoreConsultationEventsGuaranteeReciprocalImplementation : Set where
data GovernmentOutcomeMetricExhaustsCommunityDefinedSuccess : Set where

betterLabelDoesNotCreateAuthority : BetterConsultationLabelCreatesCommunityAuthority → ⊥
betterLabelDoesNotCreateAuthority ()

moreEventsDoNotGuaranteeReciprocity : MoreConsultationEventsGuaranteeReciprocalImplementation → ⊥
moreEventsDoNotGuaranteeReciprocity ()

governmentMetricDoesNotExhaustCommunitySuccess :
  GovernmentOutcomeMetricExhaustsCommunityDefinedSuccess → ⊥
governmentMetricDoesNotExhaustCommunitySuccess ()
