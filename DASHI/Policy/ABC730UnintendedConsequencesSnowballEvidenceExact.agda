module DASHI.Policy.ABC730UnintendedConsequencesSnowballEvidenceExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.String using (String)

import DASHI.Core.AttributedSourceCore as Source
import DASHI.Policy.ABC730UnintendedConsequencesEvidenceObligationExact as Obligation
import DASHI.Policy.ABC730IbrahimSnowballAttributionExact as Snowball
import DASHI.Wikimedia.DashiKnowledgeTraversalFunnelExact as Ibrahim

------------------------------------------------------------------------
-- First mechanism-evidence snowball downstream of C029.
--
-- Acquisition order is opportunistic. Payment is not. Each receipt records
-- what proposition the source can actually pay and what remains residual.
------------------------------------------------------------------------

data SourceAuthorityClass : Set where
  primaryGovernmentInstrument : SourceAuthorityClass
  primaryGovernmentGuidance : SourceAuthorityClass
  primaryGovernmentStatement : SourceAuthorityClass
  primaryJointGovernmentStatement : SourceAuthorityClass
  secondaryNewsAnalysis : SourceAuthorityClass
  academicMechanismStudy : SourceAuthorityClass

data PaymentDisposition : Set where
  paid : PaymentDisposition
  partiallyPaid : PaymentDisposition
  retainedCounterEvidence : PaymentDisposition
  unresolved : PaymentDisposition

record MechanismSourceReceipt : Set where
  constructor mechanismSourceReceipt
  field
    receiptId : String
    source : Source.AttributedSource
    authorityClass : SourceAuthorityClass
    deweyParent : String
    primaryQidReference : String
    stableSourceId : String
    propositionPaid : String
    disposition : PaymentDisposition
    residual : String
    sourceCreatesPolicyTruth : Bool

open MechanismSourceReceipt public

ukSettlementOriginNoticeSource : Source.AttributedSource
ukSettlementOriginNoticeSource = Source.mkNoDOISource
  "UK Department for Business and Trade"
  "Notice to importers: imports from Israel into the United Kingdom"
  "GOV.UK"
  "2025"
  "https://www.gov.uk/government/publications/notice-to-importers-treatment-of-goods-from-israeli-settlements/notice-to-importers-imports-from-israel-into-the-united-kingdom"
  Source.governmentSource
  "primary implementation guidance for settlement-origin differentiation under the UK-Israel trade agreement"
  Source.publicAttribution

ukSettlementOriginMechanism : MechanismSourceReceipt
ukSettlementOriginMechanism = mechanismSourceReceipt
  "ABC730-snowball:uk-origin-differentiation"
  ukSettlementOriginNoticeSource
  primaryGovernmentGuidance
  "382.7"
  "qid-unresolved-for-document-object"
  "govuk:notice-to-importers-israel-settlements:updated-2025-08-22"
  "The UK already operates an origin-control mechanism in which Israeli origin documents carry production-location information and preferential treatment is refused where the production-conferring location is a settlement."
  paid
  "This proves an existing UK differentiation mechanism, not that a new comprehensive settlement-goods ban imposes zero implementation cost and not that Australia already has an equivalent customs implementation."
  false

ukPalestinianTradeSource : Source.AttributedSource
ukPalestinianTradeSource = Source.mkNoDOISource
  "UK Department for International Trade"
  "Continuing the United Kingdom's trade relationship with the Palestine Liberation Organisation for the benefit of the Palestinian Authority of the West Bank and the Gaza Strip"
  "GOV.UK parliamentary report"
  "2019"
  "https://www.gov.uk/government/publications/continuing-the-uks-trade-relationship-with-the-palestinian-authority-parliamentary-report/continuing-the-united-kingdoms-trade-relationship-with-the-palestine-liberation-organisation-plo-for-the-benefit-of-the-palestinian-authority-of-th"
  Source.governmentSource
  "primary government report for the UK-Palestinian Authority trade architecture and rules of origin"
  Source.publicAttribution

ukPalestinianDifferentiationMechanism : MechanismSourceReceipt
ukPalestinianDifferentiationMechanism = mechanismSourceReceipt
  "ABC730-snowball:uk-palestinian-origin-channel"
  ukPalestinianTradeSource
  primaryGovernmentInstrument
  "382.7"
  "qid-unresolved-for-document-object"
  "govuk:uk-pa-trade-parliamentary-report:2019"
  "The UK maintains a distinct Palestinian Authority trade channel covering West Bank/Gaza-origin goods while settlement products are excluded from those preferences."
  paid
  "This is counterevidence to the proposition that settlement-origin differentiation necessarily collapses Palestinian-origin goods into the sanction target; it does not prove Palestinian actors would experience no indirect harm under the 2026 ban."
  false

ukPalestinianTariffExtensionSource : Source.AttributedSource
ukPalestinianTariffExtensionSource = Source.mkNoDOISource
  "UK-Palestinian Authority Joint Committee"
  "Decision No.2/2021 on amending Protocol 1"
  "GOV.UK"
  "2021"
  "https://www.gov.uk/government/publications/uk-palestinian-authority-political-trade-and-partnership-committee-documents/22-september-2021-decision-no22021-of-the-joint-committee-for-united-kingdom-palestinian-authority-trade-and-cooperation-on-amending-protocol-1"
  Source.governmentSource
  "primary bilateral trade instrument extending tariff-free access for qualifying West Bank/Gaza goods"
  Source.publicAttribution

palestinianTariffChannelReceipt : MechanismSourceReceipt
palestinianTariffChannelReceipt = mechanismSourceReceipt
  "ABC730-snowball:palestinian-tariff-channel"
  ukPalestinianTariffExtensionSource
  primaryGovernmentInstrument
  "382.7"
  "qid-unresolved-for-document-object"
  "govuk:uk-pa-joint-committee-decision-2-2021"
  "A bilateral instrument extended tariff-free access for qualifying products originating in the West Bank and Gaza Strip."
  retainedCounterEvidence
  "The existence of a preferential Palestinian channel weakens a simple goods-origin conflation mechanism; employment, intermediary, customs-delay and supply-chain incidence remain unpaid."
  false

uk2026PolicySource : Source.AttributedSource
uk2026PolicySource = Source.mkNoDOISource
  "Ed Miliband / UK Foreign, Commonwealth & Development Office"
  "Foreign Secretary Oral Statement on Israel-Palestine"
  "GOV.UK / House of Commons"
  "2026"
  "https://www.gov.uk/government/speeches/foreign-secretary-oral-statement-on-israel-palestine"
  Source.governmentSource
  "primary statement defining the announced settlement-goods ban and services/company sanctions scope"
  Source.publicAttribution

uk2026InstrumentScopeReceipt : MechanismSourceReceipt
uk2026InstrumentScopeReceipt = mechanismSourceReceipt
  "ABC730-snowball:uk-2026-instrument-scope"
  uk2026PolicySource
  primaryGovernmentStatement
  "327"
  "qid-unresolved-for-document-object"
  "govuk:foreign-secretary-israel-palestine:2026-09-08"
  "The announced UK policy covers settlement goods and a wider sanctions regime directed at companies/individuals providing construction, infrastructure, financing or real-estate services for settlement expansion, while retaining trade with green-line Israel."
  paid
  "Implementation legislation was announced for a 6-to-9-month horizon; final statutory text, exemptions, customs rules and enforcement costs remain future/unpaid objects."
  false

ukJointPolicySource : Source.AttributedSource
ukJointPolicySource = Source.mkNoDOISource
  "Foreign Ministers of Canada, Denmark, Finland, France, Iceland, Ireland, Norway, Poland, Portugal, Spain, Sweden and the UK"
  "Joint Foreign Ministers' Statement on the Two-State Solution"
  "GOV.UK / FCDO"
  "2026"
  "https://www.gov.uk/government/news/joint-foreign-ministers-statement-on-the-two-state-solution"
  Source.governmentSource
  "primary multilateral policy statement announcing or considering settlement-goods restrictions"
  Source.publicAttribution

multilateralRestrictionReceipt : MechanismSourceReceipt
multilateralRestrictionReceipt = mechanismSourceReceipt
  "ABC730-snowball:multilateral-settlement-restrictions"
  ukJointPolicySource
  primaryJointGovernmentStatement
  "327"
  "qid-unresolved-for-document-object"
  "govuk:joint-foreign-ministers-two-state:2026-09-08"
  "Multiple governments announced, supported or actively considered national/European restrictions on trade in settlement goods as a two-state-solution measure."
  paid
  "Common adoption establishes policy comparators, not causal effectiveness or absence of unintended consequences."
  false

australiaE1JointSource : Source.AttributedSource
australiaE1JointSource = Source.mkNoDOISource
  "Leaders/foreign ministers including Australia and the UK"
  "Joint Statement on the situation in the West Bank: 22 May 2026"
  "GOV.UK-hosted multilateral joint statement"
  "2026"
  "https://www.gov.uk/government/news/joint-statement-from-the-leaders-of-the-e4-canada-australia-new-zealand-on-the-situation-in-the-west-bank"
  Source.governmentSource
  "primary joint statement for signatories' public position on E1 and business participation"
  Source.publicAttribution

australiaObjectiveConsistencyReceipt : MechanismSourceReceipt
australiaObjectiveConsistencyReceipt = mechanismSourceReceipt
  "ABC730-snowball:australia-e1-business-warning"
  australiaE1JointSource
  primaryJointGovernmentStatement
  "327"
  "qid-unresolved-for-document-object"
  "govuk:joint-west-bank:2026-05-22"
  "Australia joined a statement warning businesses not to bid for E1 or other settlement-development tenders and reaffirming the two-state objective."
  paid
  "This pays objective/settlement-participation consistency, not the comparative merits of a blanket settlement import ban versus targeted sanctions."
  false

allPrimaryMechanismReceipts : List MechanismSourceReceipt
allPrimaryMechanismReceipts =
  ukSettlementOriginMechanism ∷ ukPalestinianDifferentiationMechanism ∷
  palestinianTariffChannelReceipt ∷ uk2026InstrumentScopeReceipt ∷
  multilateralRestrictionReceipt ∷ australiaObjectiveConsistencyReceipt ∷ []

------------------------------------------------------------------------
-- What this first snowball changes in the existing C029 obligation surface.
------------------------------------------------------------------------

data ObligationPaymentUpdate : Set where
  ukOriginDifferentiationExistsPaid : ObligationPaymentUpdate
  ukInstrumentScopePaid : ObligationPaymentUpdate
  australiaObjectiveConsistencyPaid : ObligationPaymentUpdate
  australianBusinessImpactStillOpen : ObligationPaymentUpdate
  palestinianIndirectIncidenceStillOpen : ObligationPaymentUpdate
  israeliIndirectIncidenceStillOpen : ObligationPaymentUpdate
  australiaImplementationCostStillOpen : ObligationPaymentUpdate
  causalEffectivenessStillOpen : ObligationPaymentUpdate

record SnowballFrontier : Set where
  constructor snowballFrontier
  field
    paidUpdates : List ObligationPaymentUpdate
    nextPrimaryTargets : String
    nextAcademicTargets : String
    acquisitionOrderMaySnowball : Bool
    paymentOrderMaySkipMechanism : Bool

canonicalSnowballFrontier : SnowballFrontier
canonicalSnowballFrontier = snowballFrontier
  (ukOriginDifferentiationExistsPaid ∷ ukInstrumentScopePaid ∷ australiaObjectiveConsistencyPaid ∷
   australianBusinessImpactStillOpen ∷ palestinianIndirectIncidenceStillOpen ∷
   israeliIndirectIncidenceStillOpen ∷ australiaImplementationCostStillOpen ∷ causalEffectivenessStillOpen ∷ [])
  "Australian departmental/Cabinet/ABF implementation analysis; Palestinian trade/employment incidence; settlement trade volume and intermediary structure; final UK implementing legislation and customs guidance"
  "after mechanism objects are fixed: empirical sanctions/trade-incidence literature with DOI, matched to the exact mechanism rather than generic sanctions effects"
  true false

------------------------------------------------------------------------
-- Ibrahim graph links. External coordinates guide traversal but do not pay the
-- consequence proposition by themselves.
------------------------------------------------------------------------

ukOriginNode : Ibrahim.DashiKnowledgeCoordinate
ukOriginNode = Ibrahim.dashi-knowledge-coordinate
  "GOV.UK/notice-to-importers-israel-settlements"
  "DASHI.Policy.ABC730UnintendedConsequencesSnowballEvidenceExact"
  "382.7"
  "qid-unresolved-for-document-object"
  "govuk:notice-to-importers-israel-settlements:2025-08-22"

obligationNode : Ibrahim.DashiKnowledgeCoordinate
obligationNode = Ibrahim.dashi-knowledge-coordinate
  "DASHI/Policy/ABC730UnintendedConsequencesEvidenceObligationExact.agda"
  "DASHI.Policy.ABC730UnintendedConsequencesEvidenceObligationExact"
  "327"
  "Q456759"
  "ABC730-2026-09-09-C029"

originSupportsObligation : Ibrahim.DashiFirstLinkEdge
originSupportsObligation = Ibrahim.dashi-first-link-edge
  obligationNode ukOriginNode Ibrahim.supportedBy Ibrahim.canonicalDashiFirstLinkPolicy
  "Existing UK origin differentiation pays one implementation-feasibility sub-obligation but not the Australian impact claim."
  true

------------------------------------------------------------------------
-- Firewalls.
------------------------------------------------------------------------

data ExistingUKMechanismProvesAustralianEase : Set where
existingUKMechanismDoesNotProveAustralianEase : ExistingUKMechanismProvesAustralianEase → ⊥
existingUKMechanismDoesNotProveAustralianEase ()

data PalestinianPreferenceProvesNoPalestinianHarm : Set where
palestinianPreferenceDoesNotProveNoPalestinianHarm : PalestinianPreferenceProvesNoPalestinianHarm → ⊥
palestinianPreferenceDoesNotProveNoPalestinianHarm ()

data MultilateralAdoptionProvesEffectiveness : Set where
multilateralAdoptionDoesNotProveEffectiveness : MultilateralAdoptionProvesEffectiveness → ⊥
multilateralAdoptionDoesNotProveEffectiveness ()

data ObjectiveConsistencyProvesInstrumentOptimality : Set where
objectiveConsistencyDoesNotProveInstrumentOptimality : ObjectiveConsistencyProvesInstrumentOptimality → ⊥
objectiveConsistencyDoesNotProveInstrumentOptimality ()

data OfficialSourceCreatesDOI : Set where
officialSourceDoesNotCreateDOI : OfficialSourceCreatesDOI → ⊥
officialSourceDoesNotCreateDOI ()

obligationRoadmapAnchor : Obligation.PolicyEvaluationRoadmap
obligationRoadmapAnchor = Obligation.canonicalPolicyEvaluationRoadmap

snowballBoundaryAnchor : Snowball.SnowballAttributionBoundary
snowballBoundaryAnchor = Snowball.canonicalSnowballAttributionBoundary
