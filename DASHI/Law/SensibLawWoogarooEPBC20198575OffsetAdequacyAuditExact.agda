module DASHI.Law.SensibLawWoogarooEPBC20198575OffsetAdequacyAuditExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.String using (String)

------------------------------------------------------------------------
-- EPBC 2019/8575 OFFSET ADEQUACY AUDIT
--
-- Source-bounded audit of the proposed-offset lane.  The exact proponent
-- offset package is not yet primary-source paid; public submissions are used
-- only as acquisition leads.  Commonwealth policy tests are primary-policy
-- consumers.  No conclusion of approval/refusal is asserted here.
------------------------------------------------------------------------

data OffsetEvidenceStage : Set where
  primaryPolicy : OffsetEvidenceStage
  secondarySubmissionLead : OffsetEvidenceStage
  primaryProjectOpen : OffsetEvidenceStage

record OffsetTest : Set where
  constructor offset-test
  field
    testName : String
    policyRule : String
    projectLead : String
    evidenceStage : OffsetEvidenceStage
    testPaid : Bool
    failureProved : Bool
    residual : String

open OffsetTest public

avoidMitigateFirst : OffsetTest
avoidMitigateFirst = offset-test
  "avoidance and mitigation before offset"
  "Offsets compensate only residual adverse impacts after avoidance and mitigation."
  "Need the actual PD alternatives/avoidance/mitigation sequence before treating an offset as relevant to the remaining impact."
  primaryProjectOpen false false
  "Extract alternatives, avoided clearing, retained habitat and mitigation measures from Part Ai."

sameMatterAttribute : OffsetTest
sameMatterAttribute = offset-test
  "same protected matter / impacted attribute"
  "Offsets must relate to the same protected matter and should be tailored to the impacted attribute; trading across protected matters is not suitable."
  "Public submissions allege regional-ecosystem, landscape and habitat-feature differences between Woogaroo and proposed offset sites."
  secondarySubmissionLead false false
  "Bind each impact attribute (foraging, shelter, breeding, corridor, TEC/flora) to the exact offset attribute claimed to compensate it."

location : OffsetTest
location = offset-test
  "location / conservation benefit"
  "In most cases the offset site should be as close to the impact site as possible; a more distant site may be accepted if greater conservation benefit is demonstrated."
  "A detailed public submission says proposed offsets are almost 100 km away and two are outside the local government area."
  secondarySubmissionLead false false
  "Recover exact offset-site coordinates/distances and the proponent's greater-conservation-benefit justification."

habitatQuality : OffsetTest
habitatQuality = offset-test
  "habitat quality"
  "For threatened-species/community habitat impacts, a direct offset must as a minimum meet impact-site habitat quality, or be managed/resourced to reach that quality over a defined period."
  "Submission criticism alleges mature hollow-bearing ironbark/complex ecosystem attributes at Woogaroo are not present at bare or lower-quality offset land."
  secondarySubmissionLead false false
  "Extract impact-site and offset-site habitat-quality scores, starting conditions, uplift assumptions, timeframe and management commitments."

timeLagRisk : OffsetTest
timeLagRisk = offset-test
  "time to ecological benefit / risk"
  "Offset suitability must consider time to conservation gain and confidence; longer delays increase risk and may require greater scale/variety."
  "Submissions argue mature-habitat features cannot be recreated on relevant timeframes."
  secondarySubmissionLead false false
  "Quantify ecological lag for each protected matter/attribute and compare with impact immediacy and offset calculator assumptions."

additionality : OffsetTest
additionality = offset-test
  "additionality"
  "Conservation gain must be new/additional to existing legal, planning or other-program obligations."
  "No primary project material yet proves the proposed offset gain is additional rather than already required/protected."
  primaryProjectOpen false false
  "Recover tenure, existing protection, baseline risk-of-loss and any pre-existing conservation obligations/funding."

scientificRobustness : OffsetTest
scientificRobustness = offset-test
  "scientific robustness / monitoring / precaution"
  "Offset decisions must be scientifically robust, measurable/monitorable/auditable/enforceable and precautionary under uncertainty."
  "A public submission alleges insufficient MNES baseline surveys and questions how population gain would be measured."
  secondarySubmissionLead false false
  "Recover baseline surveys, monitoring design, success criteria, confidence parameters, enforcement mechanism and adaptive-management triggers."

scale : OffsetTest
scale = offset-test
  "size and scale proportionate to residual impact"
  "The offset must be proportionate to residual impact, statutory status, attribute importance, risk, time lag and confidence."
  "Publicly quoted area totals and multiplication factors are not yet primary-source paid."
  primaryProjectOpen false false
  "Extract the exact impact hectares, offset hectares, quality scores, risk-of-loss, time-horizon and calculator inputs from the PD/offset assessment guide output."

localPopulation : OffsetTest
localPopulation = offset-test
  "local population / connectivity correspondence"
  "Policy requires an overall conservation outcome for the impacted protected matter; distant sites require a demonstrated conservation benefit."
  "Submission material raises an Ipswich-vs-Brisbane-Valley koala population/genetic distinction and the loss of local connectivity function."
  secondarySubmissionLead false false
  "Verify the genetics/population evidence and determine whether the offset package improves/maintains viability of the impacted population or only the species elsewhere."

record OffsetAuditSummary : Set where
  constructor offset-audit-summary
  field
    commonwealthPolicyTestsIdentified : Bool
    detailedSecondaryOffsetCritiqueLocated : Bool
    exactProponentOffsetPackagePrimaryPaid : Bool
    offsetAdequacyProved : Bool
    offsetFailureProved : Bool
    refusalFromOffsetFailureProved : Bool

currentOffsetAudit : OffsetAuditSummary
currentOffsetAudit = offset-audit-summary true true false false false false

record OffsetBoundary : Set where
  constructor offset-boundary
  field
    largeOffsetAreaDoesNotProveAdequacy : Bool
    distantOffsetDoesNotAutomaticallyProveInvalidity : Bool
    policyNonComplianceLeadDoesNotEqualLegalFinding : Bool
    offsetAdequacyDoesNotProveApproval : Bool
    offsetInadequacyDoesNotByItselfProveRefusal : Bool

offsetBoundary : OffsetBoundary
offsetBoundary = offset-boundary true true true true true
