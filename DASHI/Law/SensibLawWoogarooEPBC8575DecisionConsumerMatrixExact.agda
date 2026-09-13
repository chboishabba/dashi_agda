module DASHI.Law.SensibLawWoogarooEPBC8575DecisionConsumerMatrixExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.String using (String)

------------------------------------------------------------------------
-- EPBC 2019/8575 DECISION-CONSUMER MATRIX
--
-- This owner separates:
--   * primary Commonwealth project/control facts;
--   * project-specific ecological facts still requiring final-PD table/map
--     extraction;
--   * external submission evidence;
--   * downstream EPBC decision arguments;
--   * Queensland NCA reuse candidates.
--
-- Missing final-PD tables/maps are left open rather than reconstructed from
-- campaign or submission summaries.
------------------------------------------------------------------------

data EvidenceStage : Set where
  commonwealthPrimaryPaid : EvidenceStage
  finalPDPrimaryExtractionOpen : EvidenceStage
  externalSubmissionSupported : EvidenceStage
  dashiCrossSourceApplication : EvidenceStage
  externalDecisionOpen : EvidenceStage

data DecisionCoordinate : Set where
  projectIdentity : DecisionCoordinate
  controllingProvisionIdentity : DecisionCoordinate
  actionAreaIdentity : DecisionCoordinate
  totalHabitatArea : DecisionCoordinate
  directlyImpactedHabitatArea : DecisionCoordinate
  retainedHabitatArea : DecisionCoordinate
  conservationHabitatArea : DecisionCoordinate
  habitatCriticalToSpeciesSurvival : DecisionCoordinate
  observedSpeciesUse : DecisionCoordinate
  movementConnectivity : DecisionCoordinate
  fragmentationEffect : DecisionCoordinate
  cumulativeImpact : DecisionCoordinate
  avoidanceAlternative : DecisionCoordinate
  residualImpactAfterMitigation : DecisionCoordinate
  offsetProposal : DecisionCoordinate
  conservationAdviceConsistency : DecisionCoordinate
  recoveryPlanConsistency : DecisionCoordinate
  finalApprovalOrRefusal : DecisionCoordinate

record DecisionEvidenceReceipt : Set where
  constructor decision-evidence-receipt
  field
    coordinate : DecisionCoordinate
    stage : EvidenceStage
    boundedProposition : String
    sourceReference : String
    epbcConsumerRelevant : Bool
    qldNCAReuseCandidate : Bool

open DecisionEvidenceReceipt public

projectIdentityPaid : DecisionEvidenceReceipt
projectIdentityPaid = decision-evidence-receipt
  projectIdentity
  commonwealthPrimaryPaid
  "Springfield Residential Development is EPBC 2019/8575, proposed by Cherish Enterprises Pty Ltd for residential subdivision development in Springfield, Queensland."
  "EPBC Act Public Portal; 2026 invitation for public comment; s 130(1A) extension notice"
  true
  false

controllingProvisionPaid : DecisionEvidenceReceipt
controllingProvisionPaid = decision-evidence-receipt
  controllingProvisionIdentity
  commonwealthPrimaryPaid
  "EPBC 2019/8575 was determined a controlled action assessed by Preliminary Documentation; listed threatened species and communities under ss 18 and 18A are controlling provisions."
  "Australian Government invitation for public comment on EPBC 2019/8575 Preliminary Documentation"
  true
  false

------------------------------------------------------------------------
-- The coordinates below are the exact extraction obligations from the final
-- Preliminary Documentation and its maps/tables.  They are not filled from
-- secondary summaries merely because those summaries look numerically precise.
------------------------------------------------------------------------

actionAreaPrimaryOpen : DecisionEvidenceReceipt
actionAreaPrimaryOpen = decision-evidence-receipt
  actionAreaIdentity
  finalPDPrimaryExtractionOpen
  "Recover the exact action-area parcel/lot identity and area from the final Preliminary Documentation."
  "EPBC 2019/8575 final Preliminary Documentation / project maps"
  true
  true

totalHabitatPrimaryOpen : DecisionEvidenceReceipt
totalHabitatPrimaryOpen = decision-evidence-receipt
  totalHabitatArea
  finalPDPrimaryExtractionOpen
  "Recover total project-area habitat by species/community and habitat class."
  "EPBC 2019/8575 final Preliminary Documentation habitat tables"
  true
  true

impactedHabitatPrimaryOpen : DecisionEvidenceReceipt
impactedHabitatPrimaryOpen = decision-evidence-receipt
  directlyImpactedHabitatArea
  finalPDPrimaryExtractionOpen
  "Recover hectares of direct clearing/impact for each relevant species habitat and ecological community."
  "EPBC 2019/8575 final Preliminary Documentation impact tables/maps"
  true
  true

retainedHabitatPrimaryOpen : DecisionEvidenceReceipt
retainedHabitatPrimaryOpen = decision-evidence-receipt
  retainedHabitatArea
  finalPDPrimaryExtractionOpen
  "Recover retained habitat area and spatial relationship to the impact footprint."
  "EPBC 2019/8575 final Preliminary Documentation retention maps/tables"
  true
  true

conservationHabitatPrimaryOpen : DecisionEvidenceReceipt
conservationHabitatPrimaryOpen = decision-evidence-receipt
  conservationHabitatArea
  finalPDPrimaryExtractionOpen
  "Recover any designated conservation area, management area or protected-retention area and its habitat composition."
  "EPBC 2019/8575 final Preliminary Documentation conservation/management plans"
  true
  true

criticalHabitatPrimaryOpen : DecisionEvidenceReceipt
criticalHabitatPrimaryOpen = decision-evidence-receipt
  habitatCriticalToSpeciesSurvival
  finalPDPrimaryExtractionOpen
  "Recover the proponent/final-PD classification, if any, of project habitat as habitat critical to survival for each controlled species."
  "EPBC 2019/8575 final Preliminary Documentation species assessments"
  true
  true

speciesUsePrimaryOpen : DecisionEvidenceReceipt
speciesUsePrimaryOpen = decision-evidence-receipt
  observedSpeciesUse
  finalPDPrimaryExtractionOpen
  "Recover survey evidence of observed use, detection, foraging, movement, shelter, breeding or roosting on the exact action area."
  "EPBC 2019/8575 final Preliminary Documentation survey appendices"
  true
  true

connectivityPrimaryOpen : DecisionEvidenceReceipt
connectivityPrimaryOpen = decision-evidence-receipt
  movementConnectivity
  finalPDPrimaryExtractionOpen
  "Recover mapped connectivity/corridor function linking the action area with Woogaroo Creek, Opossum Creek and surrounding remnant habitat."
  "EPBC 2019/8575 final Preliminary Documentation connectivity figures"
  true
  true

fragmentationPrimaryOpen : DecisionEvidenceReceipt
fragmentationPrimaryOpen = decision-evidence-receipt
  fragmentationEffect
  finalPDPrimaryExtractionOpen
  "Recover the proponent's quantified/qualitative fragmentation consequences after clearing and infrastructure construction."
  "EPBC 2019/8575 final Preliminary Documentation impact assessment"
  true
  true

cumulativePrimaryOpen : DecisionEvidenceReceipt
cumulativePrimaryOpen = decision-evidence-receipt
  cumulativeImpact
  finalPDPrimaryExtractionOpen
  "Recover whether and how cumulative impacts with nearby Springfield/Woogaroo developments are assessed."
  "EPBC 2019/8575 final Preliminary Documentation cumulative-impact analysis"
  true
  true

avoidancePrimaryOpen : DecisionEvidenceReceipt
avoidancePrimaryOpen = decision-evidence-receipt
  avoidanceAlternative
  finalPDPrimaryExtractionOpen
  "Recover the alternatives/avoidance analysis, including whether smaller footprints, different layout, no-action or other locations were considered and why rejected."
  "EPBC 2019/8575 final Preliminary Documentation alternatives section"
  true
  false

residualPrimaryOpen : DecisionEvidenceReceipt
residualPrimaryOpen = decision-evidence-receipt
  residualImpactAfterMitigation
  finalPDPrimaryExtractionOpen
  "Recover the residual impact remaining after avoidance and mitigation for each controlled matter."
  "EPBC 2019/8575 final Preliminary Documentation residual-impact assessment"
  true
  true

offsetPrimaryOpen : DecisionEvidenceReceipt
offsetPrimaryOpen = decision-evidence-receipt
  offsetProposal
  finalPDPrimaryExtractionOpen
  "Recover proposed offsets and the relationship between offset claims and the exact habitat lost."
  "EPBC 2019/8575 final Preliminary Documentation offset strategy"
  true
  false

------------------------------------------------------------------------
-- Submission-supported propositions are retained as evidence leads, not as
-- replacements for the primary project records.
------------------------------------------------------------------------

qccCriticalHabitatLead : DecisionEvidenceReceipt
qccCriticalHabitatLead = decision-evidence-receipt
  habitatCriticalToSpeciesSurvival
  externalSubmissionSupported
  "Queensland Conservation Council states that the proponent's ecology classifies vegetation proposed for clearing as Koala Habitat Score 7 / habitat critical to survival and reports up to approximately 136 ha of remnant native vegetation clearing."
  "Queensland Conservation Council submission on EPBC 2019/8575, March 2026"
  true
  true

qccConnectivityLead : DecisionEvidenceReceipt
qccConnectivityLead = decision-evidence-receipt
  movementConnectivity
  externalSubmissionSupported
  "Queensland Conservation Council describes the Woogaroo Creek forest as a connected habitat network supporting koala movement and argues that clearing would fragment that network."
  "Queensland Conservation Council submission on EPBC 2019/8575, March 2026"
  true
  true

qutIrreversibilityLead : DecisionEvidenceReceipt
qutIrreversibilityLead = decision-evidence-receipt
  fragmentationEffect
  externalSubmissionSupported
  "QUT School of Law submission characterises the proposed clearing as irreversible habitat loss/fragmentation and argues for refusal of EPBC 2019/8575."
  "QUT School of Law submission to the Commonwealth Environment Minister, March 2026"
  true
  true

------------------------------------------------------------------------
-- Decision-rule boundary.
------------------------------------------------------------------------

data ControlledActionEqualsRefusal : Set where
data CriticalHabitatLabelEqualsQueenslandS13Finding : Set where
data SubmissionNumericClaimEqualsFinalPDPrimaryFact : Set where
data OffsetProposalEqualsEcologicalEquivalence : Set where

controlledActionDoesNotEqualRefusal : ControlledActionEqualsRefusal → ⊥
controlledActionDoesNotEqualRefusal ()

federalCriticalHabitatDoesNotEqualQueenslandS13 :
  CriticalHabitatLabelEqualsQueenslandS13Finding → ⊥
federalCriticalHabitatDoesNotEqualQueenslandS13 ()

submissionNumberDoesNotBecomeFinalPDPayment :
  SubmissionNumericClaimEqualsFinalPDPrimaryFact → ⊥
submissionNumberDoesNotBecomeFinalPDPayment ()

offsetDoesNotDefinitionallyEqualHabitat : OffsetProposalEqualsEcologicalEquivalence → ⊥
offsetDoesNotDefinitionallyEqualHabitat ()

record CurrentEPBC8575ExtractionWall : Set where
  constructor current-epbc8575-extraction-wall
  field
    projectAndControllingProvisionsPaid : Bool
    deadlineAndDelegatePaid : Bool
    finalPDMapTableBundleRecoveredByThisOwner : Bool
    submissionEvidenceAvailable : Bool
    refusalDecisionPaid : Bool
    qldS13SameParcelPaid : Bool

currentEPBC8575ExtractionWall : CurrentEPBC8575ExtractionWall
currentEPBC8575ExtractionWall =
  current-epbc8575-extraction-wall true true false true false false
