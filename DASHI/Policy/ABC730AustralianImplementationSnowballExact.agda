module DASHI.Policy.ABC730AustralianImplementationSnowballExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.String using (String)

import DASHI.Core.AttributedSourceCore as Source
import DASHI.Policy.ABC730UnintendedConsequencesEvidenceObligationExact as Obligation
import DASHI.Policy.ABC730UnintendedConsequencesSnowballEvidenceExact as UKSnowball
import DASHI.Policy.ABC730IbrahimSnowballAttributionExact as Snowball

------------------------------------------------------------------------
-- Australian implementation/compliance snowball downstream of C029.
--
-- Key correction:
--   targeted sanctions already impose compliance/due-diligence obligations.
-- Therefore the relevant comparison is incremental compliance burden and
-- coverage, not "blanket ban has compliance costs, targeted sanctions do not".
------------------------------------------------------------------------

data AustralianImplementationEvidenceClass : Set where
  primaryMinisterialStatement : AustralianImplementationEvidenceClass
  primarySanctionsMeasure : AustralianImplementationEvidenceClass
  primarySanctionsGuidance : AustralianImplementationEvidenceClass
  primaryComplianceRegister : AustralianImplementationEvidenceClass
  secondaryPublicAnalysis : AustralianImplementationEvidenceClass

data AustralianImplementationPayment : Set where
  statedConcernPaid : AustralianImplementationPayment
  targetedAlternativeExistsPaid : AustralianImplementationPayment
  targetedComplianceBurdenExistsPaid : AustralianImplementationPayment
  targetedCoveragePaid : AustralianImplementationPayment
  blanketIncrementalBurdenUnpaid : AustralianImplementationPayment
  comparativeAdministrativeCostUnpaid : AustralianImplementationPayment
  comparativeEvasionRiskUnpaid : AustralianImplementationPayment
  comparativeEffectivenessUnpaid : AustralianImplementationPayment

record AustralianImplementationReceipt : Set where
  constructor australianImplementationReceipt
  field
    receiptId : String
    source : Source.AttributedSource
    deweyParent : String
    stableIdentifier : String
    evidenceClass : AustralianImplementationEvidenceClass
    payment : AustralianImplementationPayment
    boundedFinding : String
    residual : String

open AustralianImplementationReceipt public

wongSenateSource : Source.AttributedSource
wongSenateSource = Source.mkNoDOISource
  "Penny Wong"
  "Palestine, Speech to the Senate"
  "Australian Parliament / Minister for Foreign Affairs"
  "2026"
  "https://www.foreignminister.gov.au/minister/penny-wong/speech/palestine-speech-senate"
  Source.governmentSource
  "primary statement of Australia's decision not to pursue a blanket-style import ban at that time and the stated concern categories"
  Source.publicAttribution

wongStatedConcernReceipt : AustralianImplementationReceipt
wongStatedConcernReceipt = australianImplementationReceipt
  "ABC730-aus:wong-stated-concern"
  wongSenateSource
  "327"
  "foreignminister:palestine-speech-senate:2026-09-08"
  primaryMinisterialStatement
  statedConcernPaid
  "Australia publicly stated concerns about implementation and unintended consequences for Australian businesses, Palestinians and Israelis while preferring further targeted measures."
  "The statement does not specify mechanism, affected subpopulation, probability, materiality, implementation cost estimate, model, departmental advice or counterfactual comparison."

settlerSanctions2026Source : Source.AttributedSource
settlerSanctions2026Source = Source.mkNoDOISource
  "Penny Wong / Australian Government"
  "Further human rights sanctions in response to escalating settler violence in the West Bank"
  "Australian Minister for Foreign Affairs"
  "2026"
  "https://www.foreignminister.gov.au/minister/penny-wong/media-release/further-human-rights-sanctions-response-escalating-settler-violence-west-bank"
  Source.governmentSource
  "primary source for Australia's targeted financial sanctions and travel bans against West Bank settler individuals/entities"
  Source.publicAttribution

existingTargetedAlternativeReceipt : AustralianImplementationReceipt
existingTargetedAlternativeReceipt = australianImplementationReceipt
  "ABC730-aus:targeted-alternative-exists"
  settlerSanctions2026Source
  "327"
  "foreignminister:further-human-rights-sanctions-west-bank:2026-06-02"
  primarySanctionsMeasure
  targetedAlternativeExistsPaid
  "Australia had already imposed targeted financial sanctions and travel bans against named settler actors/entities, including farming outposts serving as hubs for settler violence."
  "This pays existence and scope of a targeted alternative, not that it achieves the same deterrence as a settlement-goods/services ban."

dfatComplianceSource : Source.AttributedSource
dfatComplianceSource = Source.mkNoDOISource
  "Australian Sanctions Office / DFAT"
  "Guidance Note - Reporting a sanctions contravention"
  "Department of Foreign Affairs and Trade"
  "2026"
  "https://www.dfat.gov.au/international-relations/security/sanctions/guidance/reporting-sanctions-contravention"
  Source.governmentSource
  "primary compliance guidance for obligations and enforcement under Australia's sanctions regime"
  Source.publicAttribution

targetedComplianceBurdenReceipt : AustralianImplementationReceipt
targetedComplianceBurdenReceipt = australianImplementationReceipt
  "ABC730-aus:targeted-compliance-burden"
  dfatComplianceSource
  "382.7"
  "DFAT-ASO:reporting-sanctions-contravention:2026"
  primarySanctionsGuidance
  targetedComplianceBurdenExistsPaid
  "Australia's existing targeted sanctions regime already requires regulated actors to identify designated persons/entities, avoid prohibited dealings, report contraventions and manage enforcement risk."
  "This establishes non-zero compliance burden under the targeted alternative; it does not quantify that burden or the incremental burden of a settlement-origin ban."

consolidatedListSource : Source.AttributedSource
consolidatedListSource = Source.mkNoDOISource
  "Australian Sanctions Office / DFAT"
  "Consolidated List"
  "Department of Foreign Affairs and Trade"
  "2026"
  "https://www.dfat.gov.au/international-relations/security/sanctions/consolidated-list"
  Source.governmentSource
  "primary current register of Australian sanctioned individuals/entities/vessels"
  Source.publicAttribution

targetedIdentificationMechanismReceipt : AustralianImplementationReceipt
targetedIdentificationMechanismReceipt = australianImplementationReceipt
  "ABC730-aus:targeted-identification-mechanism"
  consolidatedListSource
  "382.7"
  "DFAT-ASO:consolidated-list:2026-09-08"
  primaryComplianceRegister
  targetedCoveragePaid
  "The targeted regime supplies a named-entity identification mechanism through the Consolidated List for due-diligence and asset-freeze compliance."
  "Named-entity identification is structurally different from product/place-of-production origin identification; the relative false-positive, evasion and administrative costs remain unmeasured."

allAustralianImplementationReceipts : List AustralianImplementationReceipt
allAustralianImplementationReceipts =
  wongStatedConcernReceipt ∷ existingTargetedAlternativeReceipt ∷
  targetedComplianceBurdenReceipt ∷ targetedIdentificationMechanismReceipt ∷ []

------------------------------------------------------------------------
-- Comparative burden state.
------------------------------------------------------------------------

record ComparativeComplianceState : Set where
  constructor comparativeComplianceState
  field
    targetedSanctionsHaveComplianceBurden : Bool
    targetedSanctionsHaveNamedEntityIdentifier : Bool
    blanketSettlementBanWouldRequireOriginClassification : Bool
    incrementalOriginClassificationCostPaid : Bool
    incrementalBusinessDueDiligenceCostPaid : Bool
    customsSystemsChangeCostPaid : Bool
    falsePositiveMisclassificationRatePaid : Bool
    evasionSubstitutionRiskPaid : Bool
    comparativeEnforcementCostPaid : Bool
    comparativeDeterrencePaid : Bool

canonicalComparativeComplianceState : ComparativeComplianceState
canonicalComparativeComplianceState =
  comparativeComplianceState true true true false false false false false false false

------------------------------------------------------------------------
-- Public-evidence wall.
------------------------------------------------------------------------

data PublicRationaleStatus : Set where
  affectedClassesNamed : PublicRationaleStatus
  implementationConcernNamed : PublicRationaleStatus
  mechanismSpecified : PublicRationaleStatus
  materialitySpecified : PublicRationaleStatus
  probabilitySpecified : PublicRationaleStatus
  documentaryImpactAssessmentAttached : PublicRationaleStatus
  alternativeInstrumentComparisonAttached : PublicRationaleStatus

record PublicRationaleEvidenceState : Set where
  constructor publicRationaleEvidenceState
  field
    affectedClasses : Bool
    implementationConcern : Bool
    mechanism : Bool
    materiality : Bool
    probability : Bool
    impactAssessment : Bool
    instrumentComparison : Bool

canonicalPublicRationaleEvidenceState : PublicRationaleEvidenceState
canonicalPublicRationaleEvidenceState =
  publicRationaleEvidenceState true true false false false false false

------------------------------------------------------------------------
-- Next source obligations.
------------------------------------------------------------------------

record AustralianImplementationFrontier : Set where
  constructor australianImplementationFrontier
  field
    dfatPolicyAdvice : String
    abfCustomsAdvice : String
    treasuryBusinessImpact : String
    attorneyGeneralLegalDesign : String
    cabinetDecisionRecord : String
    industryConsultation : String
    originClassificationPilotOrEstimate : String
    targetedVsBlanketCostComparison : String
    paymentMayInferMissingAdviceFromMinisterialStatement : Bool

canonicalAustralianImplementationFrontier : AustralianImplementationFrontier
canonicalAustralianImplementationFrontier = australianImplementationFrontier
  "obtain public/FOI/released DFAT analysis specifying the three unintended-consequence mechanisms"
  "obtain ABF advice on identifying settlement origin, customs fields, documentary burden and enforcement feasibility"
  "obtain Treasury/departmental estimates of Australian business compliance/importer costs if any"
  "identify legal instrument design, exceptions and interaction with sanctions/customs law"
  "locate any publicly released Cabinet decision material without inferring contents from the final announcement"
  "locate importer/industry/Palestinian/Israeli consultation submissions actually relied upon"
  "identify any trial, worked example or quantified estimate for settlement-origin classification"
  "compare marginal administrative/evasion/deterrence burden against the already-operating targeted-sanctions regime"
  false

------------------------------------------------------------------------
-- Firewalls.
------------------------------------------------------------------------

data TargetedSanctionsAreCostless : Set where
targetedSanctionsAreNotProvenCostless : TargetedSanctionsAreCostless → ⊥
targetedSanctionsAreNotProvenCostless ()

data ExistingComplianceBurdenProvesBlanketBanCheap : Set where
existingComplianceBurdenDoesNotProveBlanketBanCheap : ExistingComplianceBurdenProvesBlanketBanCheap → ⊥
existingComplianceBurdenDoesNotProveBlanketBanCheap ()

data MinisterialConcernPaysMechanism : Set where
ministerialConcernDoesNotPayMechanism : MinisterialConcernPaysMechanism → ⊥
ministerialConcernDoesNotPayMechanism ()

data NamedEntityDueDiligenceEqualsOriginDueDiligence : Set where
namedEntityDueDiligenceDoesNotEqualOriginDueDiligence : NamedEntityDueDiligenceEqualsOriginDueDiligence → ⊥
namedEntityDueDiligenceDoesNotEqualOriginDueDiligence ()

data EnforcementPenaltyProvesAdministrativeBurden : Set where
enforcementPenaltyDoesNotProveAdministrativeBurden : EnforcementPenaltyProvesAdministrativeBurden → ⊥
enforcementPenaltyDoesNotProveAdministrativeBurden ()

businessMechanismAnchor : Obligation.PolicyEffectObligation
businessMechanismAnchor = Obligation.businessMechanism

alternativeInstrumentAnchor : Obligation.PolicyEffectObligation
alternativeInstrumentAnchor = Obligation.alternativeInstrument

ukSnowballAnchor : UKSnowball.SnowballFrontier
ukSnowballAnchor = UKSnowball.canonicalSnowballFrontier

snowballBoundaryAnchor : Snowball.SnowballAttributionBoundary
snowballBoundaryAnchor = Snowball.canonicalSnowballAttributionBoundary
