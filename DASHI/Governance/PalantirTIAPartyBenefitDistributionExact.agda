module DASHI.Governance.PalantirTIAPartyBenefitDistributionExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Core.BenefitBurdenExternalityDistributionExact as Distribution
import DASHI.Core.IntersectionalNonFactorability as INF
import DASHI.Core.DisruptionBenefitHypothesisExact as Disruption
import DASHI.Governance.PalantirTIAHistoricalGenealogyExact as Genealogy

------------------------------------------------------------------------
-- PALANTIR / TIA PARTY-DISTRIBUTION AND ORDERED-DOWNSTREAM-BENEFIT ADAPTER
--
-- DASHI owns the finite distribution/order calculus below. Historical source
-- propositions remain owned by PalantirTIAHistoricalGenealogyExact and its
-- attributed sources.  In particular:
--
--   benefited != intended to benefit
--   benefited != controlled the mechanism
--   benefited != caused the outcome
--   contract/investment != profit != policy authorship
--
-- Benefit order is graph/path distance in a declared consequence chain, not
-- an evidence grade, culpability score, motive score, or welfare scalar.
------------------------------------------------------------------------

data Party : Set where
  darpaIAO : Party
  ciaIQT : Party
  palantir : Party
  chiliad : Party
  governmentCustomer : Party
  contractorCompetitor : Party
  monitoredOrDataSubject : Party
  oversightBody : Party
  publicTaxpayer : Party

data AggregateSurface : Set where
  nationalSecurityCapabilitySurface : AggregateSurface

data Contribution : Set where
  programmeResearch : Contribution
  capitalAndCustomerAccess : Contribution
  productDevelopment : Contribution
  adjacentAnalyticsCapability : Contribution
  operationalUse : Contribution
  competitiveMarketParticipation : Contribution
  dataOrExposure : Contribution
  governanceOversight : Contribution
  publicFunding : Contribution

data Benefit : Set where
  programmeCapabilityBenefit : Benefit
  investmentStrategicAccessBenefit : Benefit
  commercialProductPositionBenefit : Benefit
  adjacentSupplierBenefit : Benefit
  operationalAnalyticsBenefit : Benefit
  competitiveBenefitUnresolved : Benefit
  noPaidBenefit : Benefit
  oversightInformationBenefit : Benefit
  publicSecurityBenefitUnresolved : Benefit

data Burden : Set where
  programmeTerminationBurden : Burden
  investmentRiskBurden : Burden
  deliveryAndPerformanceBurden : Burden
  competitiveDisplacementBurden : Burden
  privacyOrSurveillanceBurden : Burden
  oversightBurden : Burden
  fiscalBurden : Burden
  burdenUnresolved : Burden

data Voice : Set where
  programmeDecisionVoice : Voice
  investorCustomerVoice : Voice
  vendorVoice : Voice
  purchaserOperationalVoice : Voice
  competitiveVoice : Voice
  limitedSubjectVoice : Voice
  legislativeOversightVoice : Voice
  electoralPublicVoice : Voice

data Authority : Set where
  programmeAuthority : Authority
  procurementOrCustomerAuthority : Authority
  vendorImplementationAuthority : Authority
  noDirectOperationalAuthority : Authority
  oversightAuthority : Authority
  authorityUnresolved : Authority

aggregate : Party → AggregateSurface
aggregate _ = nationalSecurityCapabilitySurface

contribution : Party → Contribution
contribution darpaIAO = programmeResearch
contribution ciaIQT = capitalAndCustomerAccess
contribution palantir = productDevelopment
contribution chiliad = adjacentAnalyticsCapability
contribution governmentCustomer = operationalUse
contribution contractorCompetitor = competitiveMarketParticipation
contribution monitoredOrDataSubject = dataOrExposure
contribution oversightBody = governanceOversight
contribution publicTaxpayer = publicFunding

benefit : Party → Benefit
benefit darpaIAO = programmeCapabilityBenefit
benefit ciaIQT = investmentStrategicAccessBenefit
benefit palantir = commercialProductPositionBenefit
benefit chiliad = adjacentSupplierBenefit
benefit governmentCustomer = operationalAnalyticsBenefit
benefit contractorCompetitor = competitiveBenefitUnresolved
benefit monitoredOrDataSubject = noPaidBenefit
benefit oversightBody = oversightInformationBenefit
benefit publicTaxpayer = publicSecurityBenefitUnresolved

burden : Party → Burden
burden darpaIAO = programmeTerminationBurden
burden ciaIQT = investmentRiskBurden
burden palantir = deliveryAndPerformanceBurden
burden chiliad = deliveryAndPerformanceBurden
burden governmentCustomer = deliveryAndPerformanceBurden
burden contractorCompetitor = competitiveDisplacementBurden
burden monitoredOrDataSubject = privacyOrSurveillanceBurden
burden oversightBody = oversightBurden
burden publicTaxpayer = fiscalBurden

voice : Party → Voice
voice darpaIAO = programmeDecisionVoice
voice ciaIQT = investorCustomerVoice
voice palantir = vendorVoice
voice chiliad = vendorVoice
voice governmentCustomer = purchaserOperationalVoice
voice contractorCompetitor = competitiveVoice
voice monitoredOrDataSubject = limitedSubjectVoice
voice oversightBody = legislativeOversightVoice
voice publicTaxpayer = electoralPublicVoice

authority : Party → Authority
authority darpaIAO = programmeAuthority
authority ciaIQT = procurementOrCustomerAuthority
authority palantir = vendorImplementationAuthority
authority chiliad = vendorImplementationAuthority
authority governmentCustomer = procurementOrCustomerAuthority
authority contractorCompetitor = noDirectOperationalAuthority
authority monitoredOrDataSubject = noDirectOperationalAuthority
authority oversightBody = oversightAuthority
authority publicTaxpayer = noDirectOperationalAuthority

partyDistribution :
  Distribution.DistributionGeometry
    Party AggregateSurface Contribution Benefit Burden Voice
partyDistribution = Distribution.distributionGeometry
  aggregate contribution benefit burden voice

------------------------------------------------------------------------
-- Exact non-factorability witnesses: one aggregate label cannot recover the
-- party-level distribution.  These are finite DASHI counterexamples, not
-- empirical population estimates.
------------------------------------------------------------------------

aggregateCannotRecoverBenefit : INF.FactorsThrough aggregate benefit → ⊥
aggregateCannotRecoverBenefit =
  INF.witnessRulesOutEveryFlatFactorisation
    (INF.nonFactorabilityWitness
      ciaIQT monitoredOrDataSubject refl (λ ()))

aggregateCannotRecoverBurden : INF.FactorsThrough aggregate burden → ⊥
aggregateCannotRecoverBurden =
  INF.witnessRulesOutEveryFlatFactorisation
    (INF.nonFactorabilityWitness
      ciaIQT monitoredOrDataSubject refl (λ ()))

aggregateCannotRecoverVoice : INF.FactorsThrough aggregate voice → ⊥
aggregateCannotRecoverVoice =
  INF.witnessRulesOutEveryFlatFactorisation
    (INF.nonFactorabilityWitness
      ciaIQT monitoredOrDataSubject refl (λ ()))

aggregateCannotRecoverAuthority : INF.FactorsThrough aggregate authority → ⊥
aggregateCannotRecoverAuthority =
  INF.witnessRulesOutEveryFlatFactorisation
    (INF.nonFactorabilityWitness
      ciaIQT monitoredOrDataSubject refl (λ ()))

sameAggregateCannotRecoverPartyDistribution : Bool
sameAggregateCannotRecoverPartyDistribution = true

------------------------------------------------------------------------
-- Ordered downstream consequence/benefit geometry.
------------------------------------------------------------------------

data BenefitOrder : Set where
  firstOrder : BenefitOrder
  secondOrder : BenefitOrder
  thirdOrder : BenefitOrder

data PaymentState : Set where
  paidByAttributedSource : PaymentState
  candidateToAcquire : PaymentState
  deliberatelyUnresolved : PaymentState

record OrderedBenefitEdge : Set where
  constructor ordered-benefit-edge
  field
    sourceParty : Party
    beneficiaryParty : Party
    order : BenefitOrder
    mechanism : String
    payment : PaymentState
    exactObjectReference : String
    intentReceiptPaid : Bool
    controlReceiptPaid : Bool
    causalReceiptPaid : Bool

open OrderedBenefitEdge public

-- First-order: the existing source atlas pays an In-Q-Tel -> Palantir
-- investment/customer-access edge.  It does not pay intent beyond the bounded
-- investment/development proposition, policy authorship, or TIA privatization.
firstOrderIQTPalantir : OrderedBenefitEdge
firstOrderIQTPalantir = ordered-benefit-edge
  ciaIQT palantir firstOrder
  "capital plus intelligence-community customer access during early product development"
  paidByAttributedSource
  "PalantirTIAHistoricalGenealogyExact.inQTelEdge / ciaFeedbackEdge"
  false false false

-- Second-order: customer agencies can benefit operationally from a vendor
-- capability.  The generic consequence is admissible; any specific deployment,
-- mission success or policy effect remains a same-object acquisition problem.
secondOrderCustomerCapability : OrderedBenefitEdge
secondOrderCustomerCapability = ordered-benefit-edge
  palantir governmentCustomer secondOrder
  "downstream operational analytics capability made available to a government customer"
  candidateToAcquire
  "deployment- and contract-specific customer object required"
  false false false

-- Third-order: market/standards/lock-in or institutional leverage is a useful
-- hypothesis class only.  It is intentionally unpaid until procurement,
-- standards, switching-cost, network-effect or authority evidence is acquired.
thirdOrderInstitutionalPosition : OrderedBenefitEdge
thirdOrderInstitutionalPosition = ordered-benefit-edge
  governmentCustomer palantir thirdOrder
  "possible downstream vendor entrenchment, standards influence, switching-cost advantage or institutional leverage"
  deliberatelyUnresolved
  "requires same-object procurement/renewal/standard/control evidence"
  false false false

firstOrderBenefitDoesNotEstablishIntent : Bool
firstOrderBenefitDoesNotEstablishIntent = true

secondOrderBenefitDoesNotEstablishControl : Bool
secondOrderBenefitDoesNotEstablishControl = true

thirdOrderBenefitDoesNotEstablishCausation : Bool
thirdOrderBenefitDoesNotEstablishCausation = true

------------------------------------------------------------------------
-- Disruption-benefit donor reuse.  This is a hypothesis/search vocabulary,
-- not actor identification or motive payment.
------------------------------------------------------------------------

vendorPositionHypothesis : Disruption.DisruptionBeneficiaryHypothesis
vendorPositionHypothesis = Disruption.disruption-beneficiary-hypothesis
  "vendor or contractor with a downstream position advantage"
  "government analytics procurement / technical standard / installed base"
  Disruption.shiftsFundingOrContractPosition
  "a predecessor/successor transition could alter contract position or installed-base advantage"
  "requires same-object contract/procurement/renewal evidence"
  "actor awareness + exact timing + material benefit + authority/control + independent causal evidence"

------------------------------------------------------------------------
-- Strong-claim firewall remains inherited from the genealogy owner.
------------------------------------------------------------------------

currentStrongPrivatizationClaimStillBlocked : Bool
currentStrongPrivatizationClaimStillBlocked = true

underlyingPrivatizationPromotionReadyIsFalse :
  Genealogy.promotionReady Genealogy.currentPromotionReceipt ≡ false
underlyingPrivatizationPromotionReadyIsFalse = refl

------------------------------------------------------------------------
-- Canonical boundary.
------------------------------------------------------------------------

record OrderedBenefitBoundary : Set where
  constructor ordered-benefit-boundary
  field
    benefitImpliesIntent : Bool
    benefitImpliesControl : Bool
    benefitImpliesCausation : Bool
    contractOrInvestmentImpliesPolicyAuthorship : Bool
    downstreamOrderIsEvidenceGrade : Bool
    beneficiaryIdentifiesPerpetrator : Bool

canonicalOrderedBenefitBoundary : OrderedBenefitBoundary
canonicalOrderedBenefitBoundary = ordered-benefit-boundary
  false false false false false false
