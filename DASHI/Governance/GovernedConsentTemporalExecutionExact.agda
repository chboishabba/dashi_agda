module DASHI.Governance.GovernedConsentTemporalExecutionExact where

open import DASHI.Core.Prelude

import DASHI.Core.GovernedAdmissibleCostedExperimentChoiceExact as GovernedChoice
import DASHI.Core.ConsentTemporalExternalityExact as Consent
import DASHI.Core.BenefitBurdenExternalityDistributionExact as Dist
import DASHI.Governance.ConstitutionalAxisResidualCapabilityExact as Constitutional
import DASHI.Governance.ExecutionGovernanceClosureAssayExact as Execution
import DASHI.Governance.ConsentTemporalExternalitySourceAtlasExact as Sources

------------------------------------------------------------------------
-- GOVERNED CONSENT / TEMPORAL EXECUTION
--
-- Thin execution adapter.  The generic admissibility receipts are DASHI-owned;
-- the source atlas calibrates application semantics without transferring
-- theorem authorship, community authority or automatic legal applicability.
------------------------------------------------------------------------

data TemporalResidual : Set where
  temporalResolved temporalUnresolved : TemporalResidual

data ConsentResidual : Set where
  consentResolved consentUnresolved : ConsentResidual

data DistributionResidual : Set where
  distributionResolved distributionUnresolved : DistributionResidual

record HighImpactGovernedAdmission
    (scope : Consent.ActionScope) : Set where
  constructor highImpactGovernedAdmission
  field
    governedMove :
      GovernedChoice.GovernedAdmissibleAt scope
        (Dist.strategyMove Dist.distributionAwareStrategy)
    constitutionalCoverage : Constitutional.ConstitutionalCoverage
    distributionalCoverage : Dist.DistributionalCoverage
    presentConsentEvidence : Consent.ConsentEvidence Consent.presentlyAffected
    futureInterestRepresentation :
      Consent.IntergenerationalRepresentation Consent.futureAffected

open HighImpactGovernedAdmission public

canonicalInitialHighImpactAdmission :
  HighImpactGovernedAdmission Consent.initialResearch
canonicalInitialHighImpactAdmission =
  highImpactGovernedAdmission
    GovernedChoice.canonicalGovernedInitialMove
    Constitutional.canonicalConstitutionalCoverage
    Dist.canonicalDistributionalCoverage
    Consent.presentPartyConsentEvidence
    Consent.futureStewardshipRepresentation

------------------------------------------------------------------------
-- Residuals contract capability rather than becoming advisory notes.
------------------------------------------------------------------------

data ExecutionAdmissionState : Set where
  fullyResolved unresolvedConsent unresolvedDistribution unresolvedTemporal
  : ExecutionAdmissionState

coverageState : ExecutionAdmissionState → Execution.CoverageState
coverageState fullyResolved = Execution.completeCoverage
coverageState unresolvedConsent = Execution.unresolvedExternality
coverageState unresolvedDistribution = Execution.unresolvedExternality
coverageState unresolvedTemporal = Execution.unresolvedExternality

unresolvedConsentBlocksIrreversibleExecution :
  Execution.AutonomousExecution
    Execution.irreversibleHighConsequence
    (coverageState unresolvedConsent) → ⊥
unresolvedConsentBlocksIrreversibleExecution =
  Execution.unresolvedHighConsequenceBlocksAutonomousExecution

unresolvedDistributionBlocksIrreversibleExecution :
  Execution.AutonomousExecution
    Execution.irreversibleHighConsequence
    (coverageState unresolvedDistribution) → ⊥
unresolvedDistributionBlocksIrreversibleExecution =
  Execution.unresolvedHighConsequenceBlocksAutonomousExecution

unresolvedTemporalBlocksIrreversibleExecution :
  Execution.AutonomousExecution
    Execution.irreversibleHighConsequence
    (coverageState unresolvedTemporal) → ⊥
unresolvedTemporalBlocksIrreversibleExecution =
  Execution.unresolvedHighConsequenceBlocksAutonomousExecution

------------------------------------------------------------------------
-- Current-party consent and future-interest representation remain different.
------------------------------------------------------------------------

futureRepresentationCannotSupplyPresentConsent :
  Consent.IntergenerationalRepresentation Consent.futureAffected →
  Consent.ConsentEvidence Consent.futureAffected → ⊥
futureRepresentationCannotSupplyPresentConsent =
  Consent.futureRepresentationIsNotFutureConsent

------------------------------------------------------------------------
-- Source attribution remains explicit.
------------------------------------------------------------------------

sourceBoundary : Sources.SourceAttributionBoundary
sourceBoundary = Sources.canonicalSourceAttributionBoundary

------------------------------------------------------------------------
-- Boundary.
------------------------------------------------------------------------

record GovernedConsentTemporalExecutionBoundary : Set where
  constructor governed-consent-temporal-execution-boundary
  field
    highImpactExecutionMayIgnoreConsentResidual : Bool
    highImpactExecutionMayIgnoreConsentResidualIsFalse :
      highImpactExecutionMayIgnoreConsentResidual ≡ false
    highImpactExecutionMayIgnoreDistributionResidual : Bool
    highImpactExecutionMayIgnoreDistributionResidualIsFalse :
      highImpactExecutionMayIgnoreDistributionResidual ≡ false
    highImpactExecutionMayIgnoreTemporalResidual : Bool
    highImpactExecutionMayIgnoreTemporalResidualIsFalse :
      highImpactExecutionMayIgnoreTemporalResidual ≡ false
    futureRepresentationEqualsPresentConsent : Bool
    futureRepresentationEqualsPresentConsentIsFalse :
      futureRepresentationEqualsPresentConsent ≡ false
    sourceCitationCreatesExecutionAuthority : Bool
    sourceCitationCreatesExecutionAuthorityIsFalse :
      sourceCitationCreatesExecutionAuthority ≡ false
    fullCoverageSettlesSubstantiveJustice : Bool
    fullCoverageSettlesSubstantiveJusticeIsFalse :
      fullCoverageSettlesSubstantiveJustice ≡ false

canonicalGovernedConsentTemporalExecutionBoundary :
  GovernedConsentTemporalExecutionBoundary
canonicalGovernedConsentTemporalExecutionBoundary =
  governed-consent-temporal-execution-boundary
    false refl false refl false refl false refl false refl false refl
