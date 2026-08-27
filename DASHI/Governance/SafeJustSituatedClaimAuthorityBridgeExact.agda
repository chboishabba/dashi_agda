module DASHI.Governance.SafeJustSituatedClaimAuthorityBridgeExact where

open import DASHI.Core.Prelude
import DASHI.Core.SituatedClaimAuthoritySystemExact as Situated
import DASHI.Governance.SafeJustSourceRegistryExact as Sources
import DASHI.Governance.Fanning2022ForecastAuthorityExact as Forecast
import DASHI.Governance.SafeJustForecastConsumerAdequacyExact as ForecastAdequacy
import DASHI.Governance.SafeJustEpistemicResidualLedgerExact as Residual
import DASHI.Governance.Kallis2025ClaimByClaimEvidenceRealizationExact as Kallis

------------------------------------------------------------------------
-- SAFE/JUST -> SITUATED CLAIM AUTHORITY BRIDGE
--
-- Primary source attribution retained from the repository registries:
--
-- Andrew L. Fanning, Daniel W. O'Neill, Jason Hickel & Nicolas Roux,
-- "The social shortfall and ecological overshoot of nations",
-- Nature Sustainability 5 (2022), DOI 10.1038/s41893-021-00799-z.
--
-- Giorgos Kallis et al.,
-- "Post-growth: the science of wellbeing within planetary boundaries",
-- The Lancet Planetary Health 9 (2025),
-- DOI 10.1016/S2542-5196(24)00310-3.
--
-- The situated-authority product below is a DASHI construction.  Citation of
-- either paper does not transfer authorship of this formal authority calculus.
--
-- This module makes the empirical chain an actual consumer of
-- SituatedClaimAuthoritySystemExact rather than keeping empirical adequacy and
-- agenda/category/protocol/permission authority in adjacent modules.
------------------------------------------------------------------------

data SafeJustWorld : Set where
  observedCountryYearWorld projectedCountryYearWorld : SafeJustWorld

data SafeJustAgenda : Set where
  safeJustResearchAgenda : SafeJustAgenda

data SafeJustCategory : Set where
  safeJustIndicatorCategory : SafeJustCategory

data SafeJustMeasurement : Set where
  normalizedIndicatorMeasurement : SafeJustMeasurement

data SafeJustRepresentation : Set where
  residualAggregateRepresentation reviewClaimRepresentation : SafeJustRepresentation

data SafeJustSituatedClaim : Set where
  fanningBAUProjectionClaim kallisGDP15000Claim : SafeJustSituatedClaim

data SafeJustAuthorityContext : Set where
  repositorySourceRegistryContext : SafeJustAuthorityContext

data SafeJustSituatedConsumer : Set where
  forecastResearchConsumer
  descriptiveResearchConsumer
  causalMechanismConsumer
  policyInterventionConsumer
  : SafeJustSituatedConsumer

data SafeJustUse : Set where
  researchSynthesisUse causalPromotionUse policyInterventionUse : SafeJustUse

data SafeJustUseObligation : Set where
  attributionAndResidualCarriage : SafeJustUseObligation

------------------------------------------------------------------------
-- Upstream agenda/category receipts are explicit.
--
-- These are repository-governance receipts for this formal research synthesis;
-- they are not claims that the cited authors or affected populations granted a
-- general political mandate.
------------------------------------------------------------------------

data AgendaAuthorized : SafeJustAuthorityContext → SafeJustAgenda → Set where
  repositoryAgendaReceipt :
    AgendaAuthorized repositorySourceRegistryContext safeJustResearchAgenda

data CategoryAuthorized : SafeJustAuthorityContext → SafeJustCategory → Set where
  repositoryCategoryReceipt :
    CategoryAuthorized repositorySourceRegistryContext safeJustIndicatorCategory

------------------------------------------------------------------------
-- Source provenance is claim-specific and anchored to the existing registry.
------------------------------------------------------------------------

data ClaimProvenance : SafeJustSituatedClaim → SafeJustAuthorityContext → Set where
  fanningSourceProvenance :
    ClaimProvenance fanningBAUProjectionClaim repositorySourceRegistryContext
  kallisSourceProvenance :
    ClaimProvenance kallisGDP15000Claim repositorySourceRegistryContext

fanningSource : Sources.SourceReference
fanningSource = Sources.fanning2022

kallisSource : Sources.SourceReference
kallisSource = Sources.kallis2025

------------------------------------------------------------------------
-- Research synthesis is the only protocol/use route inhabited here.
------------------------------------------------------------------------

data ProtocolAllows :
  SafeJustAuthorityContext → SafeJustSituatedClaim → SafeJustUse → Set where
  fanningResearchProtocol :
    ProtocolAllows repositorySourceRegistryContext fanningBAUProjectionClaim
      researchSynthesisUse
  kallisResearchProtocol :
    ProtocolAllows repositorySourceRegistryContext kallisGDP15000Claim
      researchSynthesisUse

data UsePermission :
  SafeJustAuthorityContext → SafeJustSituatedClaim →
  SafeJustSituatedConsumer → SafeJustUse → Set where
  fanningForecastResearchPermission :
    UsePermission repositorySourceRegistryContext fanningBAUProjectionClaim
      forecastResearchConsumer researchSynthesisUse
  kallisDescriptiveResearchPermission :
    UsePermission repositorySourceRegistryContext kallisGDP15000Claim
      descriptiveResearchConsumer researchSynthesisUse

------------------------------------------------------------------------
-- Empirical adequacy is not recreated locally: constructors carry the exact
-- existing #625 consumer-adequacy receipts.
------------------------------------------------------------------------

data EmpiricallyAdequate : SafeJustSituatedClaim → SafeJustSituatedConsumer → Set where
  fanningForecastEvidence :
    ForecastAdequacy.AdequateFor
      Forecast.canonicalProjectionReceipt ForecastAdequacy.forecastConsumer →
    EmpiricallyAdequate fanningBAUProjectionClaim forecastResearchConsumer
  kallisGDPDescriptiveEvidence :
    Kallis.AdequateFor
      Kallis.gdp15000Realization Kallis.descriptiveSynthesisConsumer →
    EmpiricallyAdequate kallisGDP15000Claim descriptiveResearchConsumer

data PoliticallyContestable : SafeJustSituatedClaim → Set where
  fanningProjectionContestable : PoliticallyContestable fanningBAUProjectionClaim
  kallisGDPClaimContestable : PoliticallyContestable kallisGDP15000Claim

-- No intervention/decision mandate is constructed by these empirical sources.
data DecisionAuthorized :
  SafeJustAuthorityContext → SafeJustSituatedClaim → SafeJustUse → Set where

------------------------------------------------------------------------
-- Qualified research use carries the live source-specific residual.
------------------------------------------------------------------------

data ObligationSatisfied :
  SafeJustSituatedClaim → SafeJustSituatedConsumer → SafeJustUse →
  SafeJustUseObligation → Set where
  fanningAttributionAndProjectionResidual :
    Residual.Carries
      Residual.kallisSynthesisStage Residual.projectionIsNotObservation →
    ObligationSatisfied fanningBAUProjectionClaim forecastResearchConsumer
      researchSynthesisUse attributionAndResidualCarriage
  kallisAttributionAndAssociationResidual :
    Kallis.ClaimEvidenceRealization.residual Kallis.gdp15000Realization ≡
      Kallis.associationNotCausation →
    ObligationSatisfied kallisGDP15000Claim descriptiveResearchConsumer
      researchSynthesisUse attributionAndResidualCarriage

safeJustSituatedClaimAuthoritySystem : Situated.SituatedClaimAuthoritySystem
safeJustSituatedClaimAuthoritySystem =
  Situated.situatedClaimAuthoritySystem
    SafeJustWorld
    SafeJustAgenda
    SafeJustCategory
    SafeJustMeasurement
    SafeJustRepresentation
    SafeJustSituatedClaim
    SafeJustAuthorityContext
    SafeJustSituatedConsumer
    SafeJustUse
    SafeJustUseObligation
    AgendaAuthorized
    CategoryAuthorized
    ClaimProvenance
    ProtocolAllows
    UsePermission
    EmpiricallyAdequate
    PoliticallyContestable
    DecisionAuthorized
    ObligationSatisfied

------------------------------------------------------------------------
-- Concrete qualified research uses.
------------------------------------------------------------------------

fanningQualifiedResearchUse :
  Situated.QualifiedUse
    safeJustSituatedClaimAuthoritySystem
    safeJustResearchAgenda
    safeJustIndicatorCategory
    fanningBAUProjectionClaim
    repositorySourceRegistryContext
    forecastResearchConsumer
    researchSynthesisUse
    attributionAndResidualCarriage
fanningQualifiedResearchUse =
  Situated.qualifiedUse
    repositoryAgendaReceipt
    repositoryCategoryReceipt
    (fanningForecastEvidence ForecastAdequacy.forecastAdequate)
    fanningSourceProvenance
    fanningResearchProtocol
    fanningForecastResearchPermission
    (fanningAttributionAndProjectionResidual
      Residual.projectionStatusStillOpenAtSynthesis)

kallisGDPQualifiedResearchUse :
  Situated.QualifiedUse
    safeJustSituatedClaimAuthoritySystem
    safeJustResearchAgenda
    safeJustIndicatorCategory
    kallisGDP15000Claim
    repositorySourceRegistryContext
    descriptiveResearchConsumer
    researchSynthesisUse
    attributionAndResidualCarriage
kallisGDPQualifiedResearchUse =
  Situated.qualifiedUse
    repositoryAgendaReceipt
    repositoryCategoryReceipt
    (kallisGDPDescriptiveEvidence Kallis.gdp15000Descriptive)
    kallisSourceProvenance
    kallisResearchProtocol
    kallisDescriptiveResearchPermission
    (kallisAttributionAndAssociationResidual refl)

------------------------------------------------------------------------
-- Promotion failures are theorem-level, not prose caveats.
------------------------------------------------------------------------

fanningCausalQualifiedUseImpossible :
  Situated.QualifiedUse
    safeJustSituatedClaimAuthoritySystem
    safeJustResearchAgenda
    safeJustIndicatorCategory
    fanningBAUProjectionClaim
    repositorySourceRegistryContext
    causalMechanismConsumer
    causalPromotionUse
    attributionAndResidualCarriage → ⊥
fanningCausalQualifiedUseImpossible qualified with
  Situated.QualifiedUse.empiricalReceipt qualified
... | ()

kallisPolicyQualifiedUseImpossible :
  Situated.QualifiedUse
    safeJustSituatedClaimAuthoritySystem
    safeJustResearchAgenda
    safeJustIndicatorCategory
    kallisGDP15000Claim
    repositorySourceRegistryContext
    policyInterventionConsumer
    policyInterventionUse
    attributionAndResidualCarriage → ⊥
kallisPolicyQualifiedUseImpossible qualified with
  Situated.QualifiedUse.permissionReceipt qualified
... | ()

fanningResearchUseDoesNotCreateDecisionAuthority :
  DecisionAuthorized repositorySourceRegistryContext fanningBAUProjectionClaim
    policyInterventionUse → ⊥
fanningResearchUseDoesNotCreateDecisionAuthority ()

kallisResearchUseDoesNotCreateDecisionAuthority :
  DecisionAuthorized repositorySourceRegistryContext kallisGDP15000Claim
    policyInterventionUse → ⊥
kallisResearchUseDoesNotCreateDecisionAuthority ()

record SafeJustSituatedClaimAuthorityBoundary : Set where
  constructor safeJustSituatedClaimAuthorityBoundary
  field
    empiricalAdequacyAloneQualifiesUse : Bool
    empiricalAdequacyAloneQualifiesUseIsFalse :
      empiricalAdequacyAloneQualifiesUse ≡ false
    sourceAttributionAloneQualifiesUse : Bool
    sourceAttributionAloneQualifiesUseIsFalse :
      sourceAttributionAloneQualifiesUse ≡ false
    qualifiedResearchUseCarriesAgendaAndCategoryReceipts : Bool
    qualifiedResearchUseCarriesAgendaAndCategoryReceiptsIsTrue :
      qualifiedResearchUseCarriesAgendaAndCategoryReceipts ≡ true
    qualifiedResearchUseCarriesLiveResidual : Bool
    qualifiedResearchUseCarriesLiveResidualIsTrue :
      qualifiedResearchUseCarriesLiveResidual ≡ true
    forecastResearchUseBecomesCausalAuthority : Bool
    forecastResearchUseBecomesCausalAuthorityIsFalse :
      forecastResearchUseBecomesCausalAuthority ≡ false
    descriptiveReviewUseBecomesPolicyMandate : Bool
    descriptiveReviewUseBecomesPolicyMandateIsFalse :
      descriptiveReviewUseBecomesPolicyMandate ≡ false
    sourceCitationAuthorsSituatedAuthorityCalculus : Bool
    sourceCitationAuthorsSituatedAuthorityCalculusIsFalse :
      sourceCitationAuthorsSituatedAuthorityCalculus ≡ false

canonicalSafeJustSituatedClaimAuthorityBoundary :
  SafeJustSituatedClaimAuthorityBoundary
canonicalSafeJustSituatedClaimAuthorityBoundary =
  safeJustSituatedClaimAuthorityBoundary
    false refl false refl true refl true refl false refl false refl false refl
