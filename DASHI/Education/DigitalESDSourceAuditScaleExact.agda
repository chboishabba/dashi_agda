module DASHI.Education.DigitalESDSourceAuditScaleExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Core.AttributedSourceCore as Attr
import DASHI.Core.SnowballAttributionProvenanceInvariantExact as Snowball

------------------------------------------------------------------------
-- DIGITAL-ESD SOURCE AUDIT VISIBILITY SCALE
--
-- The score is a compact source-coverage projection only. It is not source
-- quality, validity, study design, claim ceiling, authority, or a welfare rank.
------------------------------------------------------------------------

data Score0to5 : Set where
  score0Absent : Score0to5
  score1Mentioned : Score0to5
  score2Indirect : Score0to5
  score3DirectIncomplete : Score0to5
  score4Substantial : Score0to5
  score5UnusuallyComplete : Score0to5

scoreReading : Score0to5 → String
scoreReading score0Absent = "source does not address or evidence this audit axis"
scoreReading score1Mentioned = "axis appears only as background, framing, or contextual mention"
scoreReading score2Indirect = "source supplies partial, proxy, or indirect evidence for the axis"
scoreReading score3DirectIncomplete = "source supplies direct source-bounded evidence but leaves material parts unresolved"
scoreReading score4Substantial = "source supplies substantial direct coverage with important subdimensions or affected groups and explicit limitations"
scoreReading score5UnusuallyComplete = "source supplies unusually complete source-specific coverage including object/population, evidential basis, relevant subgroup/incidence, boundaries, and limitations"

data CoreAuditAxis : Set where
  educationalOutcomeTransformation : CoreAuditAxis
  representationWhoMissing : CoreAuditAxis
  disabilityEffectiveAccessibility : CoreAuditAxis
  participantVoiceAuthority : CoreAuditAxis
  environmentalMaterialLifecycle : CoreAuditAxis
  externalityIncidence : CoreAuditAxis
  politicalEconomy : CoreAuditAxis
  socialProvisioningCommunity : CoreAuditAxis
  maintenanceInstitutionalDurability : CoreAuditAxis
  contextTransferTimeIntergenerational : CoreAuditAxis

coreAuditAxes : List CoreAuditAxis
coreAuditAxes =
  educationalOutcomeTransformation
  ∷ representationWhoMissing
  ∷ disabilityEffectiveAccessibility
  ∷ participantVoiceAuthority
  ∷ environmentalMaterialLifecycle
  ∷ externalityIncidence
  ∷ politicalEconomy
  ∷ socialProvisioningCommunity
  ∷ maintenanceInstitutionalDurability
  ∷ contextTransferTimeIntergenerational
  ∷ []

coreAuditAxisCount : Nat
coreAuditAxisCount = 10

record AxisVisibilityReceipt (source : Attr.AttributedSource) : Set where
  constructor axis-visibility-receipt
  field
    axis : CoreAuditAxis
    score : Score0to5
    scoreReason : String
    supportingLocator : String
    limitation : String
    scoringProtocolVersion : String
    sourceRoleSnowball : Snowball.SourceRoleSnowballReceipt source

open AxisVisibilityReceipt public

mkAxisVisibilityReceipt :
  (source : Attr.AttributedSource) →
  CoreAuditAxis → Score0to5 → String → String → String → String →
  AxisVisibilityReceipt source
mkAxisVisibilityReceipt source axis score reason locator limitation version =
  axis-visibility-receipt
    axis score reason locator limitation version
    (Snowball.canonicalSourceRoleSnowballReceipt source)

------------------------------------------------------------------------
-- No-promotion firewalls.
------------------------------------------------------------------------

data ScoreCreatesSourceQuality : Set where
data ScoreRaisesClaimCeiling : Set where
data ScoreCreatesEmpiricalValidity : Set where
data ScoreCreatesSourceAuthority : Set where
data SumOfScoresCreatesAuthoritativeQualityRank : Set where

scoreDoesNotCreateSourceQuality : ScoreCreatesSourceQuality → ⊥
scoreDoesNotCreateSourceQuality ()

scoreDoesNotRaiseClaimCeiling : ScoreRaisesClaimCeiling → ⊥
scoreDoesNotRaiseClaimCeiling ()

scoreDoesNotCreateEmpiricalValidity : ScoreCreatesEmpiricalValidity → ⊥
scoreDoesNotCreateEmpiricalValidity ()

scoreDoesNotCreateSourceAuthority : ScoreCreatesSourceAuthority → ⊥
scoreDoesNotCreateSourceAuthority ()

sumOfScoresDoesNotCreateAuthoritativeQualityRank :
  SumOfScoresCreatesAuthoritativeQualityRank → ⊥
sumOfScoresDoesNotCreateAuthoritativeQualityRank ()

record SourceAuditScaleBoundary : Set where
  constructor source-audit-scale-boundary
  field
    visibilityIsCoverageOnly : Bool
    visibilityIsCoverageOnlyIsTrue : visibilityIsCoverageOnly ≡ true
    scoreRaisesClaimCeiling : Bool
    scoreRaisesClaimCeilingIsFalse : scoreRaisesClaimCeiling ≡ false
    aggregateQualityRankAuthoritative : Bool
    aggregateQualityRankAuthoritativeIsFalse : aggregateQualityRankAuthoritative ≡ false
    attributionSnowballsWithScore : Bool
    attributionSnowballsWithScoreIsTrue : attributionSnowballsWithScore ≡ true

open SourceAuditScaleBoundary public

canonicalSourceAuditScaleBoundary : SourceAuditScaleBoundary
canonicalSourceAuditScaleBoundary = source-audit-scale-boundary
  true refl
  false refl
  false refl
  true refl
