module DASHI.Core.GovernedEpistemicInquiry where

open import Agda.Builtin.Equality using (_≡_)

import DASHI.Core.ConsumerIndexedRelevanceMeasure as Relevance
import DASHI.Core.DynamicalQuotientSafety as Dynamic
import DASHI.Core.EpistemicInquiryGovernance as Governance
import DASHI.Core.PolicyRelativeProjectionSafety as Policy
import DASHI.Core.QueryFactorisationSufficiency as Query
import DASHI.Core.TypedDependencyCore as Dependency

------------------------------------------------------------------------
-- MASTER GOVERNED EPISTEMIC INQUIRY
--
-- This record assembles, without collapsing, the formal coordinates developed
-- across the PNF / hyperfabric / SoTL thread:
--
--   X              fine represented state
--   C              authorised consumer / observer family
--   Q_C            genuinely consumer-indexed present-question carrier
--   mu_C           consumer-indexed relevance / provenance mass
--   pi_C           active coarse projection
--   delta_C / R_C  reopening receipt and exact recovery
--   F              proof-bearing admissible future dynamics
--   kappa_C        operational policy chosen from the coarse surface
--   Gamma          constitutive epistemic governance over inquiry coordinates.
--
-- Importantly this carrier does NOT require static sufficiency, dynamic safety,
-- policy safety, world coverage, or governance legitimacy.  Those are separate
-- certificates below.  An inquiry can therefore be represented before being
-- certified, audited, repaired or refined.
------------------------------------------------------------------------

record GovernedEpistemicInquiry
    (State Action Consumer Observation Region Mass Agent : Set)
    : Set₂ where
  constructor governedEpistemicInquiry
  field
    dynamics : Dependency.DependentActionSystem State Action

    Question : Consumer → Set
    questions :
      (consumer : Consumer) →
      Query.InquiryQuestionFamily State (Question consumer)

    relevanceMeasure :
      Relevance.ConsumerIndexedRelevanceMeasure Consumer Region Mass

    project : Consumer → State → Observation

    Receipt : Consumer → Set
    receipt : (consumer : Consumer) → State → Receipt consumer
    reopen :
      (consumer : Consumer) →
      Observation → Receipt consumer → State
    reopenExact :
      (consumer : Consumer) →
      (state : State) →
      reopen consumer
        (project consumer state)
        (receipt consumer state)
      ≡ state

    policy :
      Consumer → Policy.CoarseInterventionPolicy Observation Action

    governance : Governance.EpistemicGovernance Agent

open GovernedEpistemicInquiry public

------------------------------------------------------------------------
-- Four distinct certification questions.
------------------------------------------------------------------------

record QuerySufficiencyCertificate
    {State Action Consumer Observation Region Mass Agent : Set}
    (inquiry :
      GovernedEpistemicInquiry
        State Action Consumer Observation Region Mass Agent)
    : Set₂ where
  constructor querySufficiencyCertificate
  field
    staticallySufficientFor :
      (consumer : Consumer) →
      Query.StaticSufficient
        (questions inquiry consumer)
        (project inquiry consumer)

open QuerySufficiencyCertificate public

record DynamicCongruenceCertificate
    {State Action Consumer Observation Region Mass Agent : Set}
    (inquiry :
      GovernedEpistemicInquiry
        State Action Consumer Observation Region Mass Agent)
    : Set₂ where
  constructor dynamicCongruenceCertificate
  field
    dynamicallySafeFor :
      (consumer : Consumer) →
      Dynamic.DynamicConsumerSafety
        (dynamics inquiry)
        (project inquiry consumer)

open DynamicCongruenceCertificate public

record PolicySafetyCertificate
    {State Action Consumer Observation Region Mass Agent : Set}
    (inquiry :
      GovernedEpistemicInquiry
        State Action Consumer Observation Region Mass Agent)
    : Set₂ where
  constructor policySafetyCertificate
  field
    policySafeFor :
      (consumer : Consumer) →
      Policy.PolicyRelativeSafety
        (dynamics inquiry)
        (project inquiry consumer)
        (policy inquiry consumer)

open PolicySafetyCertificate public

record GovernanceLegitimacyCertificate
    {State Action Consumer Observation Region Mass Agent : Set}
    (inquiry :
      GovernedEpistemicInquiry
        State Action Consumer Observation Region Mass Agent)
    : Set₂ where
  constructor governanceLegitimacyCertificate
  field
    LegitimateAllocation : Agent → Governance.InquiryCoordinate → Set
    everyAuthorisedAllocationLegitimate :
      (agent : Agent) →
      (coordinate : Governance.InquiryCoordinate) →
      Governance.Authorised (governance inquiry) agent coordinate →
      LegitimateAllocation agent coordinate

open GovernanceLegitimacyCertificate public

------------------------------------------------------------------------
-- Strong governed-safe inquiry: all four certificates are carried together.
-- World coverage remains intentionally absent: it requires the separate
-- WorldCoverageSystem / WorldCoverageWitness from ConsumerIndexedRelevanceMeasure.
------------------------------------------------------------------------

record GovernedSafeInquiry
    {State Action Consumer Observation Region Mass Agent : Set}
    (inquiry :
      GovernedEpistemicInquiry
        State Action Consumer Observation Region Mass Agent)
    : Set₂ where
  constructor governedSafeInquiry
  field
    querySufficiency : QuerySufficiencyCertificate inquiry
    dynamicCongruence : DynamicCongruenceCertificate inquiry
    policySafety : PolicySafetyCertificate inquiry
    governanceLegitimacy : GovernanceLegitimacyCertificate inquiry

open GovernedSafeInquiry public
