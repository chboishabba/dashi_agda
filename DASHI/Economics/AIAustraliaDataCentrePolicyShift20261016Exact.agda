module DASHI.Economics.AIAustraliaDataCentrePolicyShift20261016Exact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)

import DASHI.Core.AttributedSourceCore as Source

primaryGovernmentKind : Source.SourceKind
primaryGovernmentKind = Source.namedSourceKind "Australian Government primary policy statement"

mandatoryGuardrailsUpdate : Source.AttributedSource
mandatoryGuardrailsUpdate = Source.mkNoDOISource
  "Department of Industry, Science and Resources"
  "Introducing mandatory guardrails for AI in high-risk settings: proposals paper"
  "Australian Government consultation outcome"
  "2026-10-16 access"
  "https://consult.industry.gov.au/ai-mandatory-guardrails"
  primaryGovernmentKind
  "Government says it will not proceed at this time with the previous proposals for general mandatory AI guardrails; consultation informed the National AI Plan."
  Source.publicAttribution

dataCentreExpectationsSource : Source.AttributedSource
dataCentreExpectationsSource = Source.mkNoDOISource
  "Department of Industry, Science and Resources"
  "Expectations of data centres and AI infrastructure developers"
  "Australian Government policy expectations"
  "2026"
  "https://www.industry.gov.au/publications/expectations-data-centres-and-ai-infrastructure-developers"
  primaryGovernmentKind
  "Current expectations affect Commonwealth proposal prioritisation and call for new power supply, grid-cost responsibility, demand flexibility, water responsibility and other national-interest conditions; they work alongside existing law."
  Source.publicAttribution

futureStandardsAnnouncement : Source.AttributedSource
futureStandardsAnnouncement = Source.mkNoDOISource
  "Australian Government ministers"
  "AI in Australia's interests"
  "Ministerial policy announcement"
  "2026-07-15"
  "https://www.minister.industry.gov.au/charlton/media/ai-australias-interests"
  primaryGovernmentKind
  "Government announced future Australian Standards for AI including legal obligations for large data centres to underwrite new power supply, bear grid-connection costs, support demand flexibility and improve water efficiency. Announcement is not treated here as proof that the new legal duties have already been enacted."
  Source.publicAttribution

record PolicyLocusShift : Set where
  constructor policy-locus-shift
  field
    generalMandatoryModelGuardrailsProceeding : Bool
    currentDataCentreExpectations : Bool
    expectationsAffectCommonwealthPrioritisation : Bool
    announcedFutureMandatoryDataCentreStandards : Bool
    announcedNewSupplyRequirement : Bool
    announcedGridConnectionCostRequirement : Bool
    announcedDemandFlexibilityRequirement : Bool
    newMandatoryDataCentreDutyEnacted : Bool
    realisedInfrastructureComplianceCostMeasured : Bool
    modelComplianceMoatEstablished : Bool
    infrastructureBurdenConcentrationEffectEstablished : Bool

open PolicyLocusShift public

currentPolicyShift : PolicyLocusShift
currentPolicyShift = policy-locus-shift
  false true true true true true true
  false false false false

policyLocusShiftPaid :
  (generalMandatoryModelGuardrailsProceeding currentPolicyShift ≡ false) ×
  (currentDataCentreExpectations currentPolicyShift ≡ true) ×
  (announcedFutureMandatoryDataCentreStandards currentPolicyShift ≡ true)
policyLocusShiftPaid = refl , refl , refl

enactmentStillOpen : newMandatoryDataCentreDutyEnacted currentPolicyShift ≡ false
enactmentStillOpen = refl

realisedCostStillOpen : realisedInfrastructureComplianceCostMeasured currentPolicyShift ≡ false
realisedCostStillOpen = refl

data ProposalEqualsEnactmentPermission : Set where
data InfrastructureRuleImpliesModelMoatPermission : Set where
data ExpectationsImplyRealisedCostPermission : Set where

proposalDoesNotCreateEnactment : ProposalEqualsEnactmentPermission → ⊥
proposalDoesNotCreateEnactment ()

infrastructureRuleDoesNotCreateModelMoat : InfrastructureRuleImpliesModelMoatPermission → ⊥
infrastructureRuleDoesNotCreateModelMoat ()

expectationsDoNotCreateRealisedCost : ExpectationsImplyRealisedCostPermission → ⊥
expectationsDoNotCreateRealisedCost ()

boundary : String
boundary =
  "Australia's 2026 AI-policy trajectory is not a simple deregulation story. The earlier general mandatory high-risk-AI guardrail proposal is not proceeding at this time, while current Data Centre Expectations already influence Commonwealth prioritisation and government has announced future mandatory standards/legal obligations directed at large data-centre power supply, grid costs, demand flexibility and related infrastructure externalities. This pays a policy-locus-shift observation only. Announcement is not enactment; current expectations are not converted into a new statutory duty; infrastructure obligations do not establish a model/open-weight compliance moat; and no realised actor-class compliance-cost or concentration effect is manufactured."
