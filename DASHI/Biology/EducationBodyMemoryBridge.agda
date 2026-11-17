module DASHI.Biology.EducationBodyMemoryBridge where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Agda.Builtin.String using (String)
open import Agda.Builtin.Unit using (⊤; tt)

import DASHI.Core.CandidateOnlyCore as CandidateOnly
import DASHI.Biology.BodyMemoryBiologyRegression as Regression

------------------------------------------------------------------------
-- Education/body-memory bridge.
--
-- This module is candidate-only.  It tracks an education-thread surface
-- across body-memory residual formalism without promoting learning-proof,
-- diagnosis, treatment, or analytics authority.
--
-- The surface vocabulary is intentionally local:
--   - voice
--   - agency
--   - situated ethics
--   - partnership
--   - enactment
--   - engagement intelligence
--   - equity conditions
--
-- The bridge records typed rows, canonical receipts, and explicit blockers
-- for common collapse moves:
--   click = learning
--   survey = voice
--   access = equity
--   nudge = care

data Never : Set where

------------------------------------------------------------------------
-- Education-thread axes and residual kinds.

data EducationBridgeAxis : Set where
  voiceAxis : EducationBridgeAxis
  agencyAxis : EducationBridgeAxis
  situatedEthicsAxis : EducationBridgeAxis
  partnershipAxis : EducationBridgeAxis
  enactmentAxis : EducationBridgeAxis
  engagementIntelligenceAxis : EducationBridgeAxis
  equityConditionsAxis : EducationBridgeAxis

canonicalEducationBridgeAxes :
  List EducationBridgeAxis
canonicalEducationBridgeAxes =
  voiceAxis
  ∷ agencyAxis
  ∷ situatedEthicsAxis
  ∷ partnershipAxis
  ∷ enactmentAxis
  ∷ engagementIntelligenceAxis
  ∷ equityConditionsAxis
  ∷ []

educationBridgeAxisName :
  EducationBridgeAxis →
  String
educationBridgeAxisName voiceAxis =
  "voice"
educationBridgeAxisName agencyAxis =
  "agency"
educationBridgeAxisName situatedEthicsAxis =
  "situated ethics"
educationBridgeAxisName partnershipAxis =
  "partnership"
educationBridgeAxisName enactmentAxis =
  "enactment"
educationBridgeAxisName engagementIntelligenceAxis =
  "engagement intelligence"
educationBridgeAxisName equityConditionsAxis =
  "equity conditions"

educationBridgeAxisStatement :
  EducationBridgeAxis →
  String
educationBridgeAxisStatement voiceAxis =
  "Voice is tracked as a candidate residual surface, not as learning proof."
educationBridgeAxisStatement agencyAxis =
  "Agency is tracked as a candidate residual surface, not as diagnosis or treatment."
educationBridgeAxisStatement situatedEthicsAxis =
  "Situated ethics is tracked as a candidate residual surface, not as analytics authority."
educationBridgeAxisStatement partnershipAxis =
  "Partnership is tracked as a candidate residual surface, not as paternal control."
educationBridgeAxisStatement enactmentAxis =
  "Enactment is tracked as a candidate residual surface, not as performance authority."
educationBridgeAxisStatement engagementIntelligenceAxis =
  "Engagement intelligence is tracked as a candidate residual surface, not as learning proof."
educationBridgeAxisStatement equityConditionsAxis =
  "Equity conditions are tracked as a candidate residual surface, not as access=fate."

educationBridgeAxisGap :
  EducationBridgeAxis →
  String
educationBridgeAxisGap voiceAxis =
  "Voice remains candidate-only and does not collapse into diagnosis, treatment, or analytics authority."
educationBridgeAxisGap agencyAxis =
  "Agency remains candidate-only and does not collapse into diagnosis, treatment, or analytics authority."
educationBridgeAxisGap situatedEthicsAxis =
  "Situated ethics remains candidate-only and does not collapse into diagnosis, treatment, or analytics authority."
educationBridgeAxisGap partnershipAxis =
  "Partnership remains candidate-only and does not collapse into diagnosis, treatment, or analytics authority."
educationBridgeAxisGap enactmentAxis =
  "Enactment remains candidate-only and does not collapse into diagnosis, treatment, or analytics authority."
educationBridgeAxisGap engagementIntelligenceAxis =
  "Engagement intelligence remains candidate-only and does not collapse into diagnosis, treatment, or analytics authority."
educationBridgeAxisGap equityConditionsAxis =
  "Equity conditions remain candidate-only and do not collapse into diagnosis, treatment, or analytics authority."

data EducationResidualKind : Set where
  voiceResidualKind : EducationResidualKind
  agencyResidualKind : EducationResidualKind
  situatedEthicsResidualKind : EducationResidualKind
  partnershipResidualKind : EducationResidualKind
  enactmentResidualKind : EducationResidualKind
  engagementIntelligenceResidualKind : EducationResidualKind
  equityConditionsResidualKind : EducationResidualKind

educationResidualKindForAxis :
  EducationBridgeAxis →
  EducationResidualKind
educationResidualKindForAxis voiceAxis =
  voiceResidualKind
educationResidualKindForAxis agencyAxis =
  agencyResidualKind
educationResidualKindForAxis situatedEthicsAxis =
  situatedEthicsResidualKind
educationResidualKindForAxis partnershipAxis =
  partnershipResidualKind
educationResidualKindForAxis enactmentAxis =
  enactmentResidualKind
educationResidualKindForAxis engagementIntelligenceAxis =
  engagementIntelligenceResidualKind
educationResidualKindForAxis equityConditionsAxis =
  equityConditionsResidualKind

canonicalEducationResidualKinds :
  List EducationResidualKind
canonicalEducationResidualKinds =
  voiceResidualKind
  ∷ agencyResidualKind
  ∷ situatedEthicsResidualKind
  ∷ partnershipResidualKind
  ∷ enactmentResidualKind
  ∷ engagementIntelligenceResidualKind
  ∷ equityConditionsResidualKind
  ∷ []

educationResidualKindName :
  EducationResidualKind →
  String
educationResidualKindName voiceResidualKind =
  "voice residual kind"
educationResidualKindName agencyResidualKind =
  "agency residual kind"
educationResidualKindName situatedEthicsResidualKind =
  "situated ethics residual kind"
educationResidualKindName partnershipResidualKind =
  "partnership residual kind"
educationResidualKindName enactmentResidualKind =
  "enactment residual kind"
educationResidualKindName engagementIntelligenceResidualKind =
  "engagement intelligence residual kind"
educationResidualKindName equityConditionsResidualKind =
  "equity conditions residual kind"

------------------------------------------------------------------------
-- Collapse routes and their rejection lemmas.

data EducationCollapseRoute : Set where
  candidateOnlyEducationRoute : EducationCollapseRoute
  clickEqualsLearningRoute : EducationCollapseRoute
  surveyEqualsVoiceRoute : EducationCollapseRoute
  accessEqualsEquityRoute : EducationCollapseRoute
  nudgeEqualsCareRoute : EducationCollapseRoute

AdmissibleEducationCollapseRoute :
  EducationCollapseRoute →
  Set
AdmissibleEducationCollapseRoute candidateOnlyEducationRoute = ⊤
AdmissibleEducationCollapseRoute clickEqualsLearningRoute = Never
AdmissibleEducationCollapseRoute surveyEqualsVoiceRoute = Never
AdmissibleEducationCollapseRoute accessEqualsEquityRoute = Never
AdmissibleEducationCollapseRoute nudgeEqualsCareRoute = Never

clickEqualsLearningBlocked :
  AdmissibleEducationCollapseRoute clickEqualsLearningRoute →
  Never
clickEqualsLearningBlocked impossible = impossible

surveyEqualsVoiceBlocked :
  AdmissibleEducationCollapseRoute surveyEqualsVoiceRoute →
  Never
surveyEqualsVoiceBlocked impossible = impossible

accessEqualsEquityBlocked :
  AdmissibleEducationCollapseRoute accessEqualsEquityRoute →
  Never
accessEqualsEquityBlocked impossible = impossible

nudgeEqualsCareBlocked :
  AdmissibleEducationCollapseRoute nudgeEqualsCareRoute →
  Never
nudgeEqualsCareBlocked impossible = impossible

------------------------------------------------------------------------
-- Typed rows.

record EducationBodyMemoryRow : Set where
  constructor mkEducationBodyMemoryRow
  field
    rowIndex :
      Nat

    rowAxis :
      EducationBridgeAxis

    rowLabel :
      String

    rowSurface :
      String

    rowResidualKind :
      EducationResidualKind

    rowResidualReading :
      String

    rowCandidateOnly :
      Bool

    rowCandidateOnlyIsTrue :
      rowCandidateOnly ≡ true

    rowNoLearningProof :
      Bool

    rowNoLearningProofIsFalse :
      rowNoLearningProof ≡ false

    rowNoDiagnosis :
      Bool

    rowNoDiagnosisIsFalse :
      rowNoDiagnosis ≡ false

    rowNoTreatment :
      Bool

    rowNoTreatmentIsFalse :
      rowNoTreatment ≡ false

    rowNoAnalyticsAuthority :
      Bool

    rowNoAnalyticsAuthorityIsFalse :
      rowNoAnalyticsAuthority ≡ false

    rowNotes :
      List String

open EducationBodyMemoryRow public

record EducationBodyMemoryReceipt : Set where
  constructor mkEducationBodyMemoryReceipt
  field
    receiptLabel :
      String

    receiptAxis :
      EducationBridgeAxis

    receiptRow :
      EducationBodyMemoryRow

    receiptCandidateOnly :
      Bool

    receiptCandidateOnlyIsTrue :
      receiptCandidateOnly ≡ true

    receiptNoLearningProof :
      Bool

    receiptNoLearningProofIsFalse :
      receiptNoLearningProof ≡ false

    receiptNoDiagnosis :
      Bool

    receiptNoDiagnosisIsFalse :
      receiptNoDiagnosis ≡ false

    receiptNoTreatment :
      Bool

    receiptNoTreatmentIsFalse :
      receiptNoTreatment ≡ false

    receiptNoAnalyticsAuthority :
      Bool

    receiptNoAnalyticsAuthorityIsFalse :
      receiptNoAnalyticsAuthority ≡ false

    receiptSummary :
      String

open EducationBodyMemoryReceipt public

record EducationBodyMemoryBridge : Set where
  constructor mkEducationBodyMemoryBridge
  field
    bridgeLabel :
      String

    bridgeOwner :
      String

    bridgeAxes :
      List EducationBridgeAxis

    bridgeAxesAreCanonical :
      bridgeAxes ≡ canonicalEducationBridgeAxes

    bridgeResidualKinds :
      List EducationResidualKind

    bridgeResidualKindsAreCanonical :
      bridgeResidualKinds ≡ canonicalEducationResidualKinds

    bridgeRows :
      List EducationBodyMemoryRow

    bridgeReceipts :
      List EducationBodyMemoryReceipt

    bridgeCandidateOnly :
      Bool

    bridgeCandidateOnlyIsTrue :
      bridgeCandidateOnly ≡ true

    bridgeNoLearningProof :
      Bool

    bridgeNoLearningProofIsFalse :
      bridgeNoLearningProof ≡ false

    bridgeNoDiagnosis :
      Bool

    bridgeNoDiagnosisIsFalse :
      bridgeNoDiagnosis ≡ false

    bridgeNoTreatment :
      Bool

    bridgeNoTreatmentIsFalse :
      bridgeNoTreatment ≡ false

    bridgeNoAnalyticsAuthority :
      Bool

    bridgeNoAnalyticsAuthorityIsFalse :
      bridgeNoAnalyticsAuthority ≡ false

    bridgeReading :
      String

open EducationBodyMemoryBridge public

------------------------------------------------------------------------
-- Candidate-only row and receipt helpers.

educationBridgeOwner : String
educationBridgeOwner =
  "DASHI.Biology.EducationBodyMemoryBridge"

mkEducationCandidateRow :
  Nat →
  EducationBridgeAxis →
  String →
  String →
  EducationBodyMemoryRow
mkEducationCandidateRow index axis surface note =
  mkEducationBodyMemoryRow
    index
    axis
    (educationBridgeAxisName axis)
    surface
    (educationResidualKindForAxis axis)
    note
    true
    refl
    false
    refl
    false
    refl
    false
    refl
    false
    refl
    ( "candidate-only bridge row"
    ∷ "no learning-proof, diagnosis, treatment, or analytics authority"
    ∷ []
    )

mkEducationCandidateReceipt :
  String →
  EducationBridgeAxis →
  EducationBodyMemoryRow →
  String →
  EducationBodyMemoryReceipt
mkEducationCandidateReceipt label axis row summary =
  mkEducationBodyMemoryReceipt
    label
    axis
    row
    true
    refl
    false
    refl
    false
    refl
    false
    refl
    false
    refl
    summary

------------------------------------------------------------------------
-- Canonical examples.

canonicalVoiceRow :
  EducationBodyMemoryRow
canonicalVoiceRow =
  mkEducationCandidateRow
    zero
    voiceAxis
    "voice surface"
    "Voice is carried as a residual candidate surface in the body-memory lane."

canonicalAgencyRow :
  EducationBodyMemoryRow
canonicalAgencyRow =
  mkEducationCandidateRow
    (suc zero)
    agencyAxis
    "agency surface"
    "Agency is carried as a residual candidate surface in the body-memory lane."

canonicalSituatedEthicsRow :
  EducationBodyMemoryRow
canonicalSituatedEthicsRow =
  mkEducationCandidateRow
    (suc (suc zero))
    situatedEthicsAxis
    "situated ethics surface"
    "Situated ethics is carried as a residual candidate surface in the body-memory lane."

canonicalPartnershipRow :
  EducationBodyMemoryRow
canonicalPartnershipRow =
  mkEducationCandidateRow
    (suc (suc (suc zero)))
    partnershipAxis
    "partnership surface"
    "Partnership is carried as a residual candidate surface in the body-memory lane."

canonicalEnactmentRow :
  EducationBodyMemoryRow
canonicalEnactmentRow =
  mkEducationCandidateRow
    (suc (suc (suc (suc zero))))
    enactmentAxis
    "enactment surface"
    "Enactment is carried as a residual candidate surface in the body-memory lane."

canonicalEngagementIntelligenceRow :
  EducationBodyMemoryRow
canonicalEngagementIntelligenceRow =
  mkEducationCandidateRow
    (suc (suc (suc (suc (suc zero)))))
    engagementIntelligenceAxis
    "engagement intelligence surface"
    "Engagement intelligence is carried as a residual candidate surface in the body-memory lane."

canonicalEquityConditionsRow :
  EducationBodyMemoryRow
canonicalEquityConditionsRow =
  mkEducationCandidateRow
    (suc (suc (suc (suc (suc (suc zero))))))
    equityConditionsAxis
    "equity conditions surface"
    "Equity conditions are carried as a residual candidate surface in the body-memory lane."

canonicalEducationBridgeRows :
  List EducationBodyMemoryRow
canonicalEducationBridgeRows =
  canonicalVoiceRow
  ∷ canonicalAgencyRow
  ∷ canonicalSituatedEthicsRow
  ∷ canonicalPartnershipRow
  ∷ canonicalEnactmentRow
  ∷ canonicalEngagementIntelligenceRow
  ∷ canonicalEquityConditionsRow
  ∷ []

canonicalVoiceReceipt :
  EducationBodyMemoryReceipt
canonicalVoiceReceipt =
  mkEducationCandidateReceipt
    "voice receipt"
    voiceAxis
    canonicalVoiceRow
    "Voice remains candidate-only and does not become learning proof."

canonicalAgencyReceipt :
  EducationBodyMemoryReceipt
canonicalAgencyReceipt =
  mkEducationCandidateReceipt
    "agency receipt"
    agencyAxis
    canonicalAgencyRow
    "Agency remains candidate-only and does not become diagnosis or treatment."

canonicalSituatedEthicsReceipt :
  EducationBodyMemoryReceipt
canonicalSituatedEthicsReceipt =
  mkEducationCandidateReceipt
    "situated ethics receipt"
    situatedEthicsAxis
    canonicalSituatedEthicsRow
    "Situated ethics remains candidate-only and does not become analytics authority."

canonicalPartnershipReceipt :
  EducationBodyMemoryReceipt
canonicalPartnershipReceipt =
  mkEducationCandidateReceipt
    "partnership receipt"
    partnershipAxis
    canonicalPartnershipRow
    "Partnership remains candidate-only and does not become paternal control."

canonicalEnactmentReceipt :
  EducationBodyMemoryReceipt
canonicalEnactmentReceipt =
  mkEducationCandidateReceipt
    "enactment receipt"
    enactmentAxis
    canonicalEnactmentRow
    "Enactment remains candidate-only and does not become performance authority."

canonicalEngagementIntelligenceReceipt :
  EducationBodyMemoryReceipt
canonicalEngagementIntelligenceReceipt =
  mkEducationCandidateReceipt
    "engagement intelligence receipt"
    engagementIntelligenceAxis
    canonicalEngagementIntelligenceRow
    "Engagement intelligence remains candidate-only and does not become learning proof."

canonicalEquityConditionsReceipt :
  EducationBodyMemoryReceipt
canonicalEquityConditionsReceipt =
  mkEducationCandidateReceipt
    "equity conditions receipt"
    equityConditionsAxis
    canonicalEquityConditionsRow
    "Equity conditions remain candidate-only and do not become access=fate."

canonicalEducationBridgeReceipts :
  List EducationBodyMemoryReceipt
canonicalEducationBridgeReceipts =
  canonicalVoiceReceipt
  ∷ canonicalAgencyReceipt
  ∷ canonicalSituatedEthicsReceipt
  ∷ canonicalPartnershipReceipt
  ∷ canonicalEnactmentReceipt
  ∷ canonicalEngagementIntelligenceReceipt
  ∷ canonicalEquityConditionsReceipt
  ∷ []

------------------------------------------------------------------------
-- Canonical bridge.

canonicalEducationBodyMemoryBridge :
  EducationBodyMemoryBridge
canonicalEducationBodyMemoryBridge =
  mkEducationBodyMemoryBridge
    "education/body-memory candidate bridge"
    educationBridgeOwner
    canonicalEducationBridgeAxes
    refl
    canonicalEducationResidualKinds
    refl
    canonicalEducationBridgeRows
    canonicalEducationBridgeReceipts
    true
    refl
    false
    refl
    false
    refl
    false
    refl
    false
    refl
    "Candidate-only education-to-body-memory bridge aligned with BodyMemoryBiologyRegression: voice, agency, situated ethics, partnership, enactment, engagement intelligence, and equity conditions are tracked as residual surfaces, with learning-proof, diagnosis, treatment, and analytics authority explicitly blocked."

canonicalEducationBridgeCandidateOnly :
  bridgeCandidateOnly canonicalEducationBodyMemoryBridge ≡ true
canonicalEducationBridgeCandidateOnly =
  bridgeCandidateOnlyIsTrue canonicalEducationBodyMemoryBridge

canonicalEducationBridgeNoLearningProof :
  bridgeNoLearningProof canonicalEducationBodyMemoryBridge ≡ false
canonicalEducationBridgeNoLearningProof =
  bridgeNoLearningProofIsFalse canonicalEducationBodyMemoryBridge

canonicalEducationBridgeNoDiagnosis :
  bridgeNoDiagnosis canonicalEducationBodyMemoryBridge ≡ false
canonicalEducationBridgeNoDiagnosis =
  bridgeNoDiagnosisIsFalse canonicalEducationBodyMemoryBridge

canonicalEducationBridgeNoTreatment :
  bridgeNoTreatment canonicalEducationBodyMemoryBridge ≡ false
canonicalEducationBridgeNoTreatment =
  bridgeNoTreatmentIsFalse canonicalEducationBodyMemoryBridge

canonicalEducationBridgeNoAnalyticsAuthority :
  bridgeNoAnalyticsAuthority canonicalEducationBodyMemoryBridge ≡ false
canonicalEducationBridgeNoAnalyticsAuthority =
  bridgeNoAnalyticsAuthorityIsFalse canonicalEducationBodyMemoryBridge

------------------------------------------------------------------------
-- Candidate-only helper rows in the style of the core bridge records.

canonicalVoiceCandidateRow :
  CandidateOnly.CandidateOnlyRow
canonicalVoiceCandidateRow =
  CandidateOnly.candidateOnlyRow
    "voice residual candidate row"
    educationBridgeOwner
    "voice"
    CandidateOnly.bridgeCandidateKind
    CandidateOnly.bridgeCandidateOnlyStatus
    "voice is a candidate residual surface"
    "voice does not become learning proof or analytics authority"
    true
    false
    false
    false
    false
    false
    false
    false

canonicalAgencyCandidateRow :
  CandidateOnly.CandidateOnlyRow
canonicalAgencyCandidateRow =
  CandidateOnly.candidateOnlyRow
    "agency residual candidate row"
    educationBridgeOwner
    "agency"
    CandidateOnly.bridgeCandidateKind
    CandidateOnly.bridgeCandidateOnlyStatus
    "agency is a candidate residual surface"
    "agency does not become diagnosis, treatment, or analytics authority"
    true
    false
    false
    false
    false
    false
    false
    false

canonicalSituatedEthicsCandidateRow :
  CandidateOnly.CandidateOnlyRow
canonicalSituatedEthicsCandidateRow =
  CandidateOnly.candidateOnlyRow
    "situated ethics residual candidate row"
    educationBridgeOwner
    "situated ethics"
    CandidateOnly.bridgeCandidateKind
    CandidateOnly.bridgeCandidateOnlyStatus
    "situated ethics is a candidate residual surface"
    "situated ethics does not become analytics authority"
    true
    false
    false
    false
    false
    false
    false
    false

canonicalPartnershipCandidateRow :
  CandidateOnly.CandidateOnlyRow
canonicalPartnershipCandidateRow =
  CandidateOnly.candidateOnlyRow
    "partnership residual candidate row"
    educationBridgeOwner
    "partnership"
    CandidateOnly.bridgeCandidateKind
    CandidateOnly.bridgeCandidateOnlyStatus
    "partnership is a candidate residual surface"
    "partnership does not become paternal control or authority"
    true
    false
    false
    false
    false
    false
    false
    false

canonicalEnactmentCandidateRow :
  CandidateOnly.CandidateOnlyRow
canonicalEnactmentCandidateRow =
  CandidateOnly.candidateOnlyRow
    "enactment residual candidate row"
    educationBridgeOwner
    "enactment"
    CandidateOnly.bridgeCandidateKind
    CandidateOnly.bridgeCandidateOnlyStatus
    "enactment is a candidate residual surface"
    "enactment does not become performance authority"
    true
    false
    false
    false
    false
    false
    false
    false

canonicalEngagementIntelligenceCandidateRow :
  CandidateOnly.CandidateOnlyRow
canonicalEngagementIntelligenceCandidateRow =
  CandidateOnly.candidateOnlyRow
    "engagement intelligence residual candidate row"
    educationBridgeOwner
    "engagement intelligence"
    CandidateOnly.bridgeCandidateKind
    CandidateOnly.bridgeCandidateOnlyStatus
    "engagement intelligence is a candidate residual surface"
    "engagement intelligence does not become learning proof"
    true
    false
    false
    false
    false
    false
    false
    false

canonicalEquityConditionsCandidateRow :
  CandidateOnly.CandidateOnlyRow
canonicalEquityConditionsCandidateRow =
  CandidateOnly.candidateOnlyRow
    "equity conditions residual candidate row"
    educationBridgeOwner
    "equity conditions"
    CandidateOnly.bridgeCandidateKind
    CandidateOnly.bridgeCandidateOnlyStatus
    "equity conditions is a candidate residual surface"
    "equity conditions do not become access=fate or analytics authority"
    true
    false
    false
    false
    false
    false
    false
    false

------------------------------------------------------------------------
-- Receipts for the candidate-only row family.

canonicalVoiceCandidateReceipt :
  CandidateOnly.CandidateOnlyReceipt canonicalVoiceCandidateRow
canonicalVoiceCandidateReceipt =
  CandidateOnly.candidateOnlyReceipt
    refl
    refl
    refl
    refl
    refl
    refl
    refl
    refl

canonicalAgencyCandidateReceipt :
  CandidateOnly.CandidateOnlyReceipt canonicalAgencyCandidateRow
canonicalAgencyCandidateReceipt =
  CandidateOnly.candidateOnlyReceipt
    refl
    refl
    refl
    refl
    refl
    refl
    refl
    refl

canonicalSituatedEthicsCandidateReceipt :
  CandidateOnly.CandidateOnlyReceipt canonicalSituatedEthicsCandidateRow
canonicalSituatedEthicsCandidateReceipt =
  CandidateOnly.candidateOnlyReceipt
    refl
    refl
    refl
    refl
    refl
    refl
    refl
    refl

canonicalPartnershipCandidateReceipt :
  CandidateOnly.CandidateOnlyReceipt canonicalPartnershipCandidateRow
canonicalPartnershipCandidateReceipt =
  CandidateOnly.candidateOnlyReceipt
    refl
    refl
    refl
    refl
    refl
    refl
    refl
    refl

canonicalEnactmentCandidateReceipt :
  CandidateOnly.CandidateOnlyReceipt canonicalEnactmentCandidateRow
canonicalEnactmentCandidateReceipt =
  CandidateOnly.candidateOnlyReceipt
    refl
    refl
    refl
    refl
    refl
    refl
    refl
    refl

canonicalEngagementIntelligenceCandidateReceipt :
  CandidateOnly.CandidateOnlyReceipt canonicalEngagementIntelligenceCandidateRow
canonicalEngagementIntelligenceCandidateReceipt =
  CandidateOnly.candidateOnlyReceipt
    refl
    refl
    refl
    refl
    refl
    refl
    refl
    refl

canonicalEquityConditionsCandidateReceipt :
  CandidateOnly.CandidateOnlyReceipt canonicalEquityConditionsCandidateRow
canonicalEquityConditionsCandidateReceipt =
  CandidateOnly.candidateOnlyReceipt
    refl
    refl
    refl
    refl
    refl
    refl
    refl
    refl

canonicalEducationCandidateRows :
  List CandidateOnly.CandidateOnlyRow
canonicalEducationCandidateRows =
  canonicalVoiceCandidateRow
  ∷ canonicalAgencyCandidateRow
  ∷ canonicalSituatedEthicsCandidateRow
  ∷ canonicalPartnershipCandidateRow
  ∷ canonicalEnactmentCandidateRow
  ∷ canonicalEngagementIntelligenceCandidateRow
  ∷ canonicalEquityConditionsCandidateRow
  ∷ []

------------------------------------------------------------------------
-- Bridge summary rows for downstream readers.

canonicalEducationBridgeSummary :
  List String
canonicalEducationBridgeSummary =
  "voice is not learning proof"
  ∷ "agency is not diagnosis or treatment"
  ∷ "situated ethics is not analytics authority"
  ∷ "partnership is not paternal control"
  ∷ "enactment is not performance authority"
  ∷ "engagement intelligence is not learning proof"
  ∷ "equity conditions are not access=fate"
  ∷ "click = learning is blocked"
  ∷ "survey = voice is blocked"
  ∷ "access = equity is blocked"
  ∷ "nudge = care is blocked"
  ∷ []
