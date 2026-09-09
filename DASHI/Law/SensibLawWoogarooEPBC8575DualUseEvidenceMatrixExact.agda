module DASHI.Law.SensibLawWoogarooEPBC8575DualUseEvidenceMatrixExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Law.SensibLawWoogarooPreservationLegalCutsetExact as Cutset
import DASHI.Law.SensibLawWoogarooDecisionMakerAndDelayLineageExact as Decision

------------------------------------------------------------------------
-- EPBC 2019/8575 DUAL-USE EVIDENCE MATRIX
--
-- One ecological datum may be relevant to more than one legal consumer, but
-- the consumer-specific legal conclusion is not transported automatically.
-- In particular:
--   federal controlled-action / significant-impact material
--     != Queensland NCA s 13 critical-habitat classification.
------------------------------------------------------------------------

data EvidenceSourceStage : Set where
  commonwealthPrimaryRecord : EvidenceSourceStage
  proponentPreliminaryDocumentation : EvidenceSourceStage
  expertOrPeakBodySubmission : EvidenceSourceStage
  dashiCrossSourceApplication : EvidenceSourceStage

data EvidenceCoordinate : Set where
  exactProjectIdentity : EvidenceCoordinate
  exactLotIdentity : EvidenceCoordinate
  listedSpeciesOrCommunity : EvidenceCoordinate
  habitatLossExtent : EvidenceCoordinate
  habitatCriticalityClaim : EvidenceCoordinate
  corridorConnectivity : EvidenceCoordinate
  fragmentationRisk : EvidenceCoordinate
  mortalityRisk : EvidenceCoordinate
  avoidanceFeasibility : EvidenceCoordinate
  offsetReplaceability : EvidenceCoordinate
  cumulativeLandscapeDepletion : EvidenceCoordinate

data Consumer : Set where
  epbcSections18And18A : Consumer
  epbcPart9ApprovalDecision : Consumer
  qldNCASection13 : Consumer
  qldNCASection102 : Consumer
  qldNCASection49 : Consumer

data PaymentState : Set where
  sourcePaid : PaymentState
  sourcePaidButApplicationOpen : PaymentState
  secondarySupportOnly : PaymentState
  openResidual : PaymentState

record EvidenceReceipt : Set where
  constructor evidence-receipt
  field
    coordinate : EvidenceCoordinate
    sourceStage : EvidenceSourceStage
    boundedProposition : String
    sourceReference : String
    state : PaymentState

open EvidenceReceipt public

------------------------------------------------------------------------
-- Primary Commonwealth/project identity and controlling-provision facts.
------------------------------------------------------------------------

projectIdentity : EvidenceReceipt
projectIdentity = evidence-receipt
  exactProjectIdentity
  commonwealthPrimaryRecord
  "Springfield Residential Development is EPBC 2019/8575; Cherish Enterprises Pty Ltd seeks approval for a residential subdivision in Springfield, Queensland."
  "EPBC Act Public Portal, Springfield Residential Development, EPBC 2019/8575; Preliminary Documentation public-comment notice"
  sourcePaid

controllingMatters : EvidenceReceipt
controllingMatters = evidence-receipt
  listedSpeciesOrCommunity
  commonwealthPrimaryRecord
  "EPBC 2019/8575 was determined a controlled action under ss 18 and 18A for listed threatened species and communities, including koala, grey-headed flying-fox, swift parrot, regent honeyeater, Macadamia integrifolia, Coleus habrophyllus, Gossia gonoclada and Lowland Rainforest of Subtropical Australia."
  "Australian Government EPBC 2019/8575 Preliminary Documentation public-comment notice"
  sourcePaid

------------------------------------------------------------------------
-- Parcel / habitat-loss evidence presently recovered from public submissions.
-- These are useful evidence leads but are not silently promoted to Commonwealth
-- findings merely because they were submitted into the EPBC assessment.
------------------------------------------------------------------------

lot9999IdentityLead : EvidenceReceipt
lot9999IdentityLead = evidence-receipt
  exactLotIdentity
  expertOrPeakBodySubmission
  "Public submissions concerning EPBC 2019/8575 identify Lot 9999 SP292760, 7001 Mur Boulevard, Springfield, as the subject development land."
  "Public submissions to EPBC 2019/8575, including 6-7 March 2026 submissions published by Save Woogaroo Forest"
  secondarySupportOnly

koalaHabitatLossLead : EvidenceReceipt
koalaHabitatLossLead = evidence-receipt
  habitatLossExtent
  expertOrPeakBodySubmission
  "Queensland Conservation Council and other published submissions describe the proposal as clearing approximately 134-136 hectares of remnant/koala habitat within the Springview 2 and 3 proposal."
  "Queensland Conservation Council, EPBC 2019/8575 submission, 12 March 2026; published community expert submissions"
  secondarySupportOnly

koalaCriticalHabitatLead : EvidenceReceipt
koalaCriticalHabitatLead = evidence-receipt
  habitatCriticalityClaim
  expertOrPeakBodySubmission
  "Queensland Conservation Council characterises the forest proposed for clearing as critical habitat for the endangered koala."
  "Queensland Conservation Council, EPBC 2019/8575 submission, 12 March 2026"
  sourcePaidButApplicationOpen

corridorLead : EvidenceReceipt
corridorLead = evidence-receipt
  corridorConnectivity
  expertOrPeakBodySubmission
  "Queensland Conservation Council describes the forest as part of the Woogaroo Creek-Opossum Creek habitat corridor and one of the remaining connected forest areas in the Springfield-Ipswich region."
  "Queensland Conservation Council, EPBC 2019/8575 submission, 12 March 2026"
  sourcePaidButApplicationOpen

landscapeDepletionLead : EvidenceReceipt
landscapeDepletionLead = evidence-receipt
  cumulativeLandscapeDepletion
  expertOrPeakBodySubmission
  "Queensland Conservation Council reports that Ipswich retains around 21 percent remnant vegetation and argues that further clearing would intensify fragmentation in an already depleted landscape."
  "Queensland Conservation Council, EPBC 2019/8575 submission, 12 March 2026"
  secondarySupportOnly

qutIrreversibilityLead : EvidenceReceipt
qutIrreversibilityLead = evidence-receipt
  fragmentationRisk
  expertOrPeakBodySubmission
  "A Queensland University of Technology School of Law submission argues that the proposal involves irreversible clearing of habitat critical to survival, fragmentation of one of the last functional habitat blocks in South-East Queensland, increased mortality risk for an endangered species and cumulative impacts in a region already experiencing severe koala decline."
  "QUT School of Law submission by Monica Taylor, Rowena Maguire and Bridget Lewis, 12 March 2026"
  secondarySupportOnly

------------------------------------------------------------------------
-- Consumer-indexed relevance.  Relevance is deliberately weaker than payment.
------------------------------------------------------------------------

record ConsumerRelevance : Set where
  constructor consumer-relevance
  field
    evidence : EvidenceReceipt
    consumer : Consumer
    relevant : Bool
    currentlyPaysConsumer : Bool
    residual : String

open ConsumerRelevance public

controllingMattersToEPBC : ConsumerRelevance
controllingMattersToEPBC = consumer-relevance
  controllingMatters
  epbcSections18And18A
  true
  true
  "No residual for controlled-action identity; final approval/refusal remains separate."

koalaLossToPart9 : ConsumerRelevance
koalaLossToPart9 = consumer-relevance
  koalaHabitatLossLead
  epbcPart9ApprovalDecision
  true
  false
  "Recover the corresponding proponent/final Preliminary Documentation pages, exact mapped area and the assessment's own significance/avoidance conclusions."

corridorToPart9 : ConsumerRelevance
corridorToPart9 = consumer-relevance
  corridorLead
  epbcPart9ApprovalDecision
  true
  false
  "Bind corridor function to the exact action footprint and applicable species conservation advice/recovery criteria."

koalaCriticalityToQldS13 : ConsumerRelevance
koalaCriticalityToQldS13 = consumer-relevance
  koalaCriticalHabitatLead
  qldNCASection13
  true
  false
  "Show under Queensland law that the exact habitat is essential for conservation of a viable population of protected wildlife; the phrase 'critical habitat' in an EPBC submission is not the s 13 finding."

corridorToQldS13 : ConsumerRelevance
corridorToQldS13 = consumer-relevance
  corridorLead
  qldNCASection13
  true
  false
  "Convert landscape connectivity into species/population-specific evidence of essential habitat rather than treating connectivity alone as sufficient."

qutRiskToInterimOrder : ConsumerRelevance
qutRiskToInterimOrder = consumer-relevance
  qutIrreversibilityLead
  qldNCASection102
  true
  false
  "Bind the threatened process, timing and likely significant detrimental effect to the exact Queensland statutory predicates."

------------------------------------------------------------------------
-- WrongType / Factors-through-style firewalls.
------------------------------------------------------------------------

data ControlledActionEqualsRefusal : Set where
data SubmissionClaimEqualsAgencyFinding : Set where
data FederalCriticalHabitatEqualsQueenslandCriticalHabitat : Set where
data LargeHabitatLossAloneProvesEssentialToViablePopulation : Set where
data CorridorLabelAlonePaysSection13 : Set where

controlledActionDoesNotEqualRefusal : ControlledActionEqualsRefusal → ⊥
controlledActionDoesNotEqualRefusal ()

submissionDoesNotBecomeAgencyFinding : SubmissionClaimEqualsAgencyFinding → ⊥
submissionDoesNotBecomeAgencyFinding ()

federalCriticalHabitatDoesNotEqualQueenslandCriticalHabitat :
  FederalCriticalHabitatEqualsQueenslandCriticalHabitat → ⊥
federalCriticalHabitatDoesNotEqualQueenslandCriticalHabitat ()

largeLossDoesNotByItselfPayEssentiality :
  LargeHabitatLossAloneProvesEssentialToViablePopulation → ⊥
largeLossDoesNotByItselfPayEssentiality ()

corridorLabelDoesNotByItselfPaySection13 : CorridorLabelAlonePaysSection13 → ⊥
corridorLabelDoesNotByItselfPaySection13 ()

------------------------------------------------------------------------
-- Current dual-use bottleneck.
------------------------------------------------------------------------

record DualUseFrontier : Set where
  constructor dual-use-frontier
  field
    federalControllingMattersPaid : Bool
    exactDecisionDeadlinePaid : Bool
    exactDelegatePaid : Bool
    exactLotPrimarySourcePaid : Bool
    exactHabitatLossPrimarySourcePaid : Bool
    qldSection13SameParcelPaid : Bool
    highestValueNextAcquisition : String

currentDualUseFrontier : DualUseFrontier
currentDualUseFrontier = dual-use-frontier
  true
  true
  true
  false
  false
  false
  "Recover the final/proponent Preliminary Documentation pages and maps that bind Lot 9999 SP292760 to exact clearing, species habitat, retained habitat, connectivity, avoidance and offset propositions; then apply those same ecological coordinates independently to Queensland NCA s 13."
