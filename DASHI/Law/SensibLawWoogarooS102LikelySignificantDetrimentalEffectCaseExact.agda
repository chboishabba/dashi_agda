module DASHI.Law.SensibLawWoogarooS102LikelySignificantDetrimentalEffectCaseExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Core.AttributedSourceCore as Source
import DASHI.Law.SensibLawWoogarooS102StatutorySpatialRelationExact as S102
import DASHI.Law.SensibLawWoogaroo9281NegotiatedApprovedGeometryExact as Geometry
import DASHI.Law.SensibLawWoogaroo9281ExecutionStateResidualExact as Exec
import DASHI.Law.SensibLawWoogarooLegalConsumerAtomCompletionExact as Atom

------------------------------------------------------------------------
-- WOOGAROO NCA s 102 LIKELY-SIGNIFICANT-DETRIMENTAL-EFFECT CASE
--
-- This owner does not declare that s 102 is satisfied. It assembles the
-- strongest presently source-paid propositions for counsel/expert review,
-- retains the strongest contrary/limiting propositions, and isolates the
-- missing inference between the approved process and likely significant harm.
------------------------------------------------------------------------

data S102CasePropositionKind : Set where
  statutoryGateway : S102CasePropositionKind
  qualifyingWildlife : S102CasePropositionKind
  threateningProcess : S102CasePropositionKind
  ecologicalExposure : S102CasePropositionKind
  likelyEffectSupport : S102CasePropositionKind
  mitigationOrDefeater : S102CasePropositionKind
  executionState : S102CasePropositionKind
  ministerialInference : S102CasePropositionKind

data PropositionStatus : Set where
  sourcePaid : PropositionStatus
  stronglySupported : PropositionStatus
  partiallyPaid : PropositionStatus
  open : PropositionStatus
  adverseEvidence : PropositionStatus

record S102CaseProposition : Set where
  constructor s102-case-proposition
  field
    kind : S102CasePropositionKind
    status : PropositionStatus
    proposition : String
    sourceRole : String
    legalUse : String
    boundary : String

open S102CaseProposition public

koalaQualifyingWildlife : S102CaseProposition
koalaQualifyingWildlife = s102-case-proposition
  qualifyingWildlife
  sourcePaid
  "Koala (Phascolarctos cinereus) is listed as Endangered in Queensland."
  "Queensland Government conservation-status material / Nature Conservation framework"
  "Supports the direct s 102 threatened-wildlife gateway; prior s 13 critical-habitat identification is not required for this gateway."
  "Threatened status does not by itself prove that this population or habitat is subject to the approved threatening process or that significant detrimental effect is likely."

approvedClearingProcess : S102CaseProposition
approvedClearingProcess = s102-case-proposition
  threateningProcess
  sourcePaid
  "9281/2024/OW authorises an operational-works process involving earthworks, vegetation clearing and stormwater; A12705838 supplies the negotiated approved plan-scale works, bushfire-clearing, Open Space and tree-interface geometry."
  "Ipswich City Council negotiated decision and approved plans"
  "Provides a concrete candidate process capable of affecting protected wildlife/native wildlife habitat for the s 12/s 102 analysis."
  "An approved process is not automatically a 'threatening process' in the statutory application, and approval does not prove commencement."

sameProjectKoalaExposure : S102CaseProposition
sameProjectKoalaExposure = s102-case-proposition
  ecologicalExposure
  stronglySupported
  "The Springview project material records Koala scats, recognised food trees, habitat score 7/10, a >500 ha connectivity surface, about 136 ha direct habitat clearing and about 26 ha indirect habitat impact."
  "Saunders Havill Group / proponent-side 2019 ecology"
  "Supports ecological exposure, habitat-function loss and fragmentation pathways relevant to whether the approved process is likely to cause significant detrimental effect."
  "The 2019 ecology is historical and consultant-authored; the exact 2026 final proposal/current ecological state must not be assumed identical."

sameProjectSignificantImpactConclusion : S102CaseProposition
sameProjectSignificantImpactConclusion = s102-case-proposition
  likelyEffectSupport
  stronglySupported
  "The project consultant concluded that clearing and functional loss of about 136 ha of habitat score 7 would be a significant impact on Koala habitat critical to survival."
  "Saunders Havill Group / proponent-side federal ecology assessment"
  "This is unusually strong same-project evidence that the proposed clearing process could have serious ecological consequences; it is relevant but not conclusive under the differently worded Queensland s 102 test."
  "A federal guideline significant-impact conclusion is not a Queensland Ministerial opinion under s 102 and does not automatically satisfy 'likely significant detrimental effect'."

fragmentationPathway : S102CaseProposition
fragmentationPathway = s102-case-proposition
  likelyEffectSupport
  stronglySupported
  "The same project material records habitat connectivity and anticipates that surrounding development would increase fragmentation and reduce movement opportunities."
  "Saunders Havill Group / proponent-side ecology"
  "Supports a causal pathway from vegetation clearing/earthworks to reduced habitat function and movement connectivity, which fits the broad s 12 concept of a process affecting habitat capacity to sustain natural processes."
  "Connectivity evidence does not itself quantify the likelihood or magnitude of the s 102 detrimental effect."

currentExecutionUnknown : S102CaseProposition
currentExecutionUnknown = s102-case-proposition
  executionState
  open
  "Condition 6(a) satisfaction, prestart records, current fauna/arborist execution records and actual commencement are not in the present corpus."
  "Current corpus/public-surface audit"
  "These facts affect urgency, imminence and evidentiary preservation but are not textual prerequisites to identifying the approved process or ecological risk."
  "A record not located publicly is not proof that the record does not exist or that works have not commenced."

mitigationCase : S102CaseProposition
mitigationCase = s102-case-proposition
  mitigationOrDefeater
  adverseEvidence
  "The local approval contains tree-retention/protection, arborist, fauna spotter-catcher, pre-clearance planning, erosion/sediment and reporting requirements, and the project ecology relies on retained vegetation and mitigation."
  "Ipswich approval conditions plus SHG ecology"
  "Counsel/expert should test whether these measures materially reduce the likelihood or significance of detrimental effect."
  "The existence of mitigation conditions does not prove effectiveness, implementation or absence of significant effect."

recoveryValueAdverseCase : S102CaseProposition
recoveryValueAdverseCase = s102-case-proposition
  mitigationOrDefeater
  adverseEvidence
  "SHG assigned the site Koala recovery value 0 and argued that urban barriers/isolation reduced population-level recovery importance."
  "Saunders Havill Group / proponent-side ecology"
  "This is the strongest presently identified adverse proposition against a high-significance habitat/population inference and must be tested rather than omitted."
  "The recovery-value conclusion is not the s 102 statutory test and sits alongside the same report's >500 ha connectivity and significant habitat-impact conclusions."

ministerialEffectInference : S102CaseProposition
ministerialEffectInference = s102-case-proposition
  ministerialInference
  open
  "The remaining legal/ecological question is whether the approved vegetation-clearing/earthworks process is likely to have significant detrimental effect on qualifying threatened wildlife or other qualifying habitat/area."
  "cross-source legal/ecological inference for Ministerial opinion"
  "This is the live s 102 merits question."
  "No repository reconstruction, map overlap, consultant conclusion or threatened-species listing may be promoted into the Ministerial opinion automatically."

------------------------------------------------------------------------
-- Current case shape: enough to justify expert/counsel testing, not enough to
-- mark the statutory opinion as established.
------------------------------------------------------------------------

record S102CaseState : Set where
  constructor s102-case-state
  field
    threatenedWildlifeGatewayPaid : Bool
    concreteApprovedProcessPaid : Bool
    sameProjectExposurePaid : Bool
    seriousEffectEvidencePaid : Bool
    causalPathwaySupported : Bool
    mitigationAndAdverseCaseRetained : Bool
    currentExecutionKnown : Bool
    likelySignificantDetrimentalEffectEstablished : Bool
    nextEvidence : String

currentS102CaseState : S102CaseState
currentS102CaseState = s102-case-state
  true true true true true true
  false false
  "Obtain a short ecological opinion addressing the actual s 12/s 102 wording: identify the qualifying threatened wildlife, the approved clearing/earthworks process, the causal pathway, the likely magnitude/duration/reversibility of effect, the role of fragmentation/connectivity, and whether approval mitigation materially changes that conclusion. In parallel obtain Condition 6(a), prestart and commencement records to determine urgency."

------------------------------------------------------------------------
-- Primary source attribution for the two propositions not already owned by
-- project/council source modules.
------------------------------------------------------------------------

ncaActSource : Source.AttributedSource
ncaActSource = Source.mkNoDOISource
  "Queensland Parliamentary Counsel"
  "Nature Conservation Act 1992 — sections 12, 102 and 103"
  "Queensland Legislation — current in-force text"
  "2026"
  "https://www.legislation.qld.gov.au/view/whole/html/current/act-1992-020"
  Source.governmentSource
  "Primary statutory source for threatening process, the interim conservation order predicate, and off-site order capacity."
  Source.publicAttribution

koalaStatusSource : Source.AttributedSource
koalaStatusSource = Source.mkNoDOISource
  "Queensland Government"
  "Changes made to wildlife categories on 8 April 2022"
  "Queensland threatened-species conservation-status register/guidance"
  "2022"
  "https://www.qld.gov.au/environment/plants-animals/conservation/threatened-species/classes/conservation-status/changes-categories-april-2022"
  Source.governmentSource
  "Official Queensland source recording reclassification of Phascolarctos cinereus from Vulnerable to Endangered. Used only for the threatened-wildlife gateway/status proposition."
  Source.publicAttribution

s102EffectSourceAtlas : Source.AttributedSourceAtlas
s102EffectSourceAtlas = Source.mkSourceAtlas
  "Woogaroo s 102 likely-significant-detrimental-effect source atlas"
  "DASHI.Law.SensibLawWoogarooS102LikelySignificantDetrimentalEffectCaseExact"
  (ncaActSource ∷ koalaStatusSource ∷ [])
  "Project ecology, Council approval and execution-state sources are imported from existing Woogaroo owners. These primary sources do not themselves determine the Ministerial opinion or outcome."

------------------------------------------------------------------------
-- WrongType / no-promotion boundaries.
------------------------------------------------------------------------

data EndangeredStatusEqualsS102Satisfied : Set where
data FederalSignificantImpactEqualsS102DetrimentalEffect : Set where
data ApprovedClearingEqualsThreateningProcessConclusion : Set where
data MitigationConditionsEqualsNoSignificantEffect : Set where
data RecoveryValueZeroEqualsNoS102Route : Set where
data NoCommencementEvidenceEqualsNoUrgency : Set where

endangeredStatusDoesNotSatisfyS102 : EndangeredStatusEqualsS102Satisfied → ⊥
endangeredStatusDoesNotSatisfyS102 ()

federalConclusionDoesNotBecomeS102Conclusion : FederalSignificantImpactEqualsS102DetrimentalEffect → ⊥
federalConclusionDoesNotBecomeS102Conclusion ()

approvalDoesNotDetermineThreateningProcess : ApprovedClearingEqualsThreateningProcessConclusion → ⊥
approvalDoesNotDetermineThreateningProcess ()

mitigationDoesNotProveNoEffect : MitigationConditionsEqualsNoSignificantEffect → ⊥
mitigationDoesNotProveNoEffect ()

recoveryValueDoesNotForecloseS102 : RecoveryValueZeroEqualsNoS102Route → ⊥
recoveryValueDoesNotForecloseS102 ()

missingCommencementDoesNotRemoveUrgency : NoCommencementEvidenceEqualsNoUrgency → ⊥
missingCommencementDoesNotRemoveUrgency ()
