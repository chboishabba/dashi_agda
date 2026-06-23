module DASHI.Biology.StudentEngagementEvidenceBridge where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Agda.Builtin.String using (String)
open import Agda.Builtin.Unit using (⊤; tt)

------------------------------------------------------------------------
-- Student engagement evidence bridge.
--
-- Candidate-only and fail-closed.
--
-- This module records the page-1 education evidence lane for:
--   - online engagement
--   - course-specific nudging
--   - transition/success for underrepresented students
--   - student voice and agency
--   - click / survey / access / nudge non-authority
--   - data ecology / governance
--
-- The bridge keeps these as evidence surfaces rather than universal rules.
-- Clicks do not become learning proof, surveys do not become voice, access
-- does not become equity, nudges do not become care, and data ecology does
-- not become extraction or authority.

data Never : Set where

listCount : ∀ {A : Set} → List A → Nat
listCount [] = zero
listCount (_ ∷ xs) = suc (listCount xs)

------------------------------------------------------------------------
-- Evidence axes.

data StudentEngagementEvidenceAxis : Set where
  onlineEngagementAxis : StudentEngagementEvidenceAxis
  courseSpecificNudgingAxis : StudentEngagementEvidenceAxis
  underrepresentedTransitionSuccessAxis : StudentEngagementEvidenceAxis
  studentVoiceAgencyAxis : StudentEngagementEvidenceAxis
  clickSurveyAccessNudgeNonAuthorityAxis : StudentEngagementEvidenceAxis
  dataEcologyGovernanceAxis : StudentEngagementEvidenceAxis

canonicalStudentEngagementEvidenceAxes :
  List StudentEngagementEvidenceAxis
canonicalStudentEngagementEvidenceAxes =
  onlineEngagementAxis
  ∷ courseSpecificNudgingAxis
  ∷ underrepresentedTransitionSuccessAxis
  ∷ studentVoiceAgencyAxis
  ∷ clickSurveyAccessNudgeNonAuthorityAxis
  ∷ dataEcologyGovernanceAxis
  ∷ []

studentEngagementEvidenceAxisName :
  StudentEngagementEvidenceAxis →
  String
studentEngagementEvidenceAxisName onlineEngagementAxis =
  "online engagement"
studentEngagementEvidenceAxisName courseSpecificNudgingAxis =
  "course-specific nudging"
studentEngagementEvidenceAxisName underrepresentedTransitionSuccessAxis =
  "transition and success for underrepresented students"
studentEngagementEvidenceAxisName studentVoiceAgencyAxis =
  "student voice and agency"
studentEngagementEvidenceAxisName clickSurveyAccessNudgeNonAuthorityAxis =
  "click / survey / access / nudge non-authority"
studentEngagementEvidenceAxisName dataEcologyGovernanceAxis =
  "data ecology and governance"

studentEngagementEvidenceAxisStatement :
  StudentEngagementEvidenceAxis →
  String
studentEngagementEvidenceAxisStatement onlineEngagementAxis =
  "Online engagement is carried as a candidate evidence surface, not as learning proof."
studentEngagementEvidenceAxisStatement courseSpecificNudgingAxis =
  "Course-specific nudging is carried as a candidate evidence surface, not as authority or coercion."
studentEngagementEvidenceAxisStatement underrepresentedTransitionSuccessAxis =
  "Transition and success for underrepresented students are carried as candidate evidence, not as universal selection fate."
studentEngagementEvidenceAxisStatement studentVoiceAgencyAxis =
  "Student voice and agency are carried as candidate evidence surfaces, not as extractive data capture."
studentEngagementEvidenceAxisStatement clickSurveyAccessNudgeNonAuthorityAxis =
  "Clicks, surveys, access, and nudges remain non-authority signals."
studentEngagementEvidenceAxisStatement dataEcologyGovernanceAxis =
  "Data ecology is tracked through governance and custodianship, not extraction."

studentEngagementEvidenceAxisGap :
  StudentEngagementEvidenceAxis →
  String
studentEngagementEvidenceAxisGap onlineEngagementAxis =
  "Online engagement remains candidate-only and does not become learning proof."
studentEngagementEvidenceAxisGap courseSpecificNudgingAxis =
  "Course-specific nudging remains candidate-only and does not become care, coercion, or authority."
studentEngagementEvidenceAxisGap underrepresentedTransitionSuccessAxis =
  "Transition and success remain candidate-only and do not become universal pedagogy or selection fate."
studentEngagementEvidenceAxisGap studentVoiceAgencyAxis =
  "Student voice and agency remain candidate-only and do not become extraction or institutional authority."
studentEngagementEvidenceAxisGap clickSurveyAccessNudgeNonAuthorityAxis =
  "Clicks, surveys, access, and nudges remain non-authority signals."
studentEngagementEvidenceAxisGap dataEcologyGovernanceAxis =
  "Data ecology remains candidate-only and does not become extraction or analytics authority."

data StudentEngagementResidualKind : Set where
  onlineEngagementResidualKind : StudentEngagementResidualKind
  courseSpecificNudgingResidualKind : StudentEngagementResidualKind
  underrepresentedTransitionSuccessResidualKind : StudentEngagementResidualKind
  studentVoiceAgencyResidualKind : StudentEngagementResidualKind
  clickSurveyAccessNudgeNonAuthorityResidualKind : StudentEngagementResidualKind
  dataEcologyGovernanceResidualKind : StudentEngagementResidualKind

studentEngagementResidualKindForAxis :
  StudentEngagementEvidenceAxis →
  StudentEngagementResidualKind
studentEngagementResidualKindForAxis onlineEngagementAxis =
  onlineEngagementResidualKind
studentEngagementResidualKindForAxis courseSpecificNudgingAxis =
  courseSpecificNudgingResidualKind
studentEngagementResidualKindForAxis underrepresentedTransitionSuccessAxis =
  underrepresentedTransitionSuccessResidualKind
studentEngagementResidualKindForAxis studentVoiceAgencyAxis =
  studentVoiceAgencyResidualKind
studentEngagementResidualKindForAxis clickSurveyAccessNudgeNonAuthorityAxis =
  clickSurveyAccessNudgeNonAuthorityResidualKind
studentEngagementResidualKindForAxis dataEcologyGovernanceAxis =
  dataEcologyGovernanceResidualKind

canonicalStudentEngagementResidualKinds :
  List StudentEngagementResidualKind
canonicalStudentEngagementResidualKinds =
  onlineEngagementResidualKind
  ∷ courseSpecificNudgingResidualKind
  ∷ underrepresentedTransitionSuccessResidualKind
  ∷ studentVoiceAgencyResidualKind
  ∷ clickSurveyAccessNudgeNonAuthorityResidualKind
  ∷ dataEcologyGovernanceResidualKind
  ∷ []

studentEngagementResidualKindName :
  StudentEngagementResidualKind →
  String
studentEngagementResidualKindName onlineEngagementResidualKind =
  "online engagement residual kind"
studentEngagementResidualKindName courseSpecificNudgingResidualKind =
  "course-specific nudging residual kind"
studentEngagementResidualKindName underrepresentedTransitionSuccessResidualKind =
  "transition and success residual kind"
studentEngagementResidualKindName studentVoiceAgencyResidualKind =
  "student voice and agency residual kind"
studentEngagementResidualKindName clickSurveyAccessNudgeNonAuthorityResidualKind =
  "click / survey / access / nudge non-authority residual kind"
studentEngagementResidualKindName dataEcologyGovernanceResidualKind =
  "data ecology and governance residual kind"

------------------------------------------------------------------------
-- Collapse routes and their rejection lemmas.

data StudentEngagementCollapseRoute : Set where
  candidateOnlyStudentEngagementRoute : StudentEngagementCollapseRoute
  onlineEngagementEqualsLearningRoute : StudentEngagementCollapseRoute
  courseSpecificNudgeEqualsAuthorityRoute : StudentEngagementCollapseRoute
  transitionSuccessEqualsSelectionRoute : StudentEngagementCollapseRoute
  studentVoiceEqualsSurveyRoute : StudentEngagementCollapseRoute
  clickEqualsLearningRoute : StudentEngagementCollapseRoute
  surveyEqualsVoiceRoute : StudentEngagementCollapseRoute
  accessEqualsEquityRoute : StudentEngagementCollapseRoute
  nudgeEqualsCareRoute : StudentEngagementCollapseRoute
  dataEcologyEqualsExtractionRoute : StudentEngagementCollapseRoute

AdmissibleStudentEngagementCollapseRoute :
  StudentEngagementCollapseRoute →
  Set
AdmissibleStudentEngagementCollapseRoute candidateOnlyStudentEngagementRoute = ⊤
AdmissibleStudentEngagementCollapseRoute onlineEngagementEqualsLearningRoute = Never
AdmissibleStudentEngagementCollapseRoute courseSpecificNudgeEqualsAuthorityRoute = Never
AdmissibleStudentEngagementCollapseRoute transitionSuccessEqualsSelectionRoute = Never
AdmissibleStudentEngagementCollapseRoute studentVoiceEqualsSurveyRoute = Never
AdmissibleStudentEngagementCollapseRoute clickEqualsLearningRoute = Never
AdmissibleStudentEngagementCollapseRoute surveyEqualsVoiceRoute = Never
AdmissibleStudentEngagementCollapseRoute accessEqualsEquityRoute = Never
AdmissibleStudentEngagementCollapseRoute nudgeEqualsCareRoute = Never
AdmissibleStudentEngagementCollapseRoute dataEcologyEqualsExtractionRoute = Never

onlineEngagementEqualsLearningBlocked :
  AdmissibleStudentEngagementCollapseRoute onlineEngagementEqualsLearningRoute →
  Never
onlineEngagementEqualsLearningBlocked impossible = impossible

courseSpecificNudgeEqualsAuthorityBlocked :
  AdmissibleStudentEngagementCollapseRoute courseSpecificNudgeEqualsAuthorityRoute →
  Never
courseSpecificNudgeEqualsAuthorityBlocked impossible = impossible

transitionSuccessEqualsSelectionBlocked :
  AdmissibleStudentEngagementCollapseRoute transitionSuccessEqualsSelectionRoute →
  Never
transitionSuccessEqualsSelectionBlocked impossible = impossible

studentVoiceEqualsSurveyBlocked :
  AdmissibleStudentEngagementCollapseRoute studentVoiceEqualsSurveyRoute →
  Never
studentVoiceEqualsSurveyBlocked impossible = impossible

clickEqualsLearningBlocked :
  AdmissibleStudentEngagementCollapseRoute clickEqualsLearningRoute →
  Never
clickEqualsLearningBlocked impossible = impossible

surveyEqualsVoiceBlocked :
  AdmissibleStudentEngagementCollapseRoute surveyEqualsVoiceRoute →
  Never
surveyEqualsVoiceBlocked impossible = impossible

accessEqualsEquityBlocked :
  AdmissibleStudentEngagementCollapseRoute accessEqualsEquityRoute →
  Never
accessEqualsEquityBlocked impossible = impossible

nudgeEqualsCareBlocked :
  AdmissibleStudentEngagementCollapseRoute nudgeEqualsCareRoute →
  Never
nudgeEqualsCareBlocked impossible = impossible

dataEcologyEqualsExtractionBlocked :
  AdmissibleStudentEngagementCollapseRoute dataEcologyEqualsExtractionRoute →
  Never
dataEcologyEqualsExtractionBlocked impossible = impossible

------------------------------------------------------------------------
-- Typed rows.

record StudentEngagementEvidenceRow : Set where
  constructor mkStudentEngagementEvidenceRow
  field
    rowIndex :
      Nat

    rowAxis :
      StudentEngagementEvidenceAxis

    rowLabel :
      String

    rowSurface :
      String

    rowResidualKind :
      StudentEngagementResidualKind

    rowReading :
      String

    rowCandidateOnly :
      Bool

    rowCandidateOnlyIsTrue :
      rowCandidateOnly ≡ true

    rowNonAuthority :
      Bool

    rowNonAuthorityIsTrue :
      rowNonAuthority ≡ true

    rowNonExtraction :
      Bool

    rowNonExtractionIsTrue :
      rowNonExtraction ≡ true

    rowNonPromotion :
      Bool

    rowNonPromotionIsTrue :
      rowNonPromotion ≡ true

    rowNotes :
      List String

open StudentEngagementEvidenceRow public

record StudentEngagementEvidenceReceipt : Set where
  constructor mkStudentEngagementEvidenceReceipt
  field
    receiptLabel :
      String

    receiptAxis :
      StudentEngagementEvidenceAxis

    receiptRow :
      StudentEngagementEvidenceRow

    receiptCandidateOnly :
      Bool

    receiptCandidateOnlyIsTrue :
      receiptCandidateOnly ≡ true

    receiptNonAuthority :
      Bool

    receiptNonAuthorityIsTrue :
      receiptNonAuthority ≡ true

    receiptNonExtraction :
      Bool

    receiptNonExtractionIsTrue :
      receiptNonExtraction ≡ true

    receiptNonPromotion :
      Bool

    receiptNonPromotionIsTrue :
      receiptNonPromotion ≡ true

    receiptSummary :
      String

open StudentEngagementEvidenceReceipt public

record StudentEngagementEvidenceBridge : Set where
  constructor mkStudentEngagementEvidenceBridge
  field
    bridgeLabel :
      String

    bridgeOwner :
      String

    bridgeAxes :
      List StudentEngagementEvidenceAxis

    bridgeAxesAreCanonical :
      bridgeAxes ≡ canonicalStudentEngagementEvidenceAxes

    bridgeResidualKinds :
      List StudentEngagementResidualKind

    bridgeResidualKindsAreCanonical :
      bridgeResidualKinds ≡ canonicalStudentEngagementResidualKinds

    bridgeRows :
      List StudentEngagementEvidenceRow

    bridgeReceipts :
      List StudentEngagementEvidenceReceipt

    bridgeRoute :
      StudentEngagementCollapseRoute

    bridgeRouteIsCandidateOnly :
      bridgeRoute ≡ candidateOnlyStudentEngagementRoute

    bridgeRouteAdmissible :
      AdmissibleStudentEngagementCollapseRoute bridgeRoute

    bridgeCandidateOnly :
      Bool

    bridgeCandidateOnlyIsTrue :
      bridgeCandidateOnly ≡ true

    bridgeNonAuthority :
      Bool

    bridgeNonAuthorityIsTrue :
      bridgeNonAuthority ≡ true

    bridgeNonExtraction :
      Bool

    bridgeNonExtractionIsTrue :
      bridgeNonExtraction ≡ true

    bridgeNonPromotion :
      Bool

    bridgeNonPromotionIsTrue :
      bridgeNonPromotion ≡ true

    bridgeReading :
      String

open StudentEngagementEvidenceBridge public

------------------------------------------------------------------------
-- Helpers.

studentEngagementBridgeOwner : String
studentEngagementBridgeOwner =
  "DASHI.Biology.StudentEngagementEvidenceBridge"

buildStudentEngagementEvidenceRow :
  Nat →
  StudentEngagementEvidenceAxis →
  String →
  String →
  String →
  StudentEngagementEvidenceRow
buildStudentEngagementEvidenceRow index axis label surface reading =
  mkStudentEngagementEvidenceRow
    index
    axis
    label
    surface
    (studentEngagementResidualKindForAxis axis)
    reading
    true
    refl
    true
    refl
    true
    refl
    true
    refl
    ( "candidate-only evidence row"
    ∷ "non-authority, non-extraction, and non-promotion remain explicit"
    ∷ []
    )

buildStudentEngagementEvidenceReceipt :
  String →
  StudentEngagementEvidenceAxis →
  StudentEngagementEvidenceRow →
  String →
  StudentEngagementEvidenceReceipt
buildStudentEngagementEvidenceReceipt label axis row summary =
  mkStudentEngagementEvidenceReceipt
    label
    axis
    row
    true
    refl
    true
    refl
    true
    refl
    true
    refl
    summary

------------------------------------------------------------------------
-- Canonical rows.

canonicalOnlineEngagementRow :
  StudentEngagementEvidenceRow
canonicalOnlineEngagementRow =
  buildStudentEngagementEvidenceRow
    zero
    onlineEngagementAxis
    "online engagement"
    "online engagement evidence"
    "Low online engagement is treated as a candidate evidence surface, not as learning proof."

canonicalCourseSpecificNudgingRow :
  StudentEngagementEvidenceRow
canonicalCourseSpecificNudgingRow =
  buildStudentEngagementEvidenceRow
    (suc zero)
    courseSpecificNudgingAxis
    "course-specific nudging"
    "course-specific nudging evidence"
    "Course-specific nudges are support surfaces, not authority, coercion, or care claims."

canonicalUnderrepresentedTransitionSuccessRow :
  StudentEngagementEvidenceRow
canonicalUnderrepresentedTransitionSuccessRow =
  buildStudentEngagementEvidenceRow
    (suc (suc zero))
    underrepresentedTransitionSuccessAxis
    "transition and success for underrepresented students"
    "transition / success evidence"
    "Transition and success for underrepresented students is tracked without universalizing the pathway."

canonicalStudentVoiceAgencyRow :
  StudentEngagementEvidenceRow
canonicalStudentVoiceAgencyRow =
  buildStudentEngagementEvidenceRow
    (suc (suc (suc zero)))
    studentVoiceAgencyAxis
    "student voice and agency"
    "voice / agency evidence"
    "Student voice and agency remain distinct candidate surfaces, not survey capture or institutional authority."

canonicalClickSurveyAccessNudgeNonAuthorityRow :
  StudentEngagementEvidenceRow
canonicalClickSurveyAccessNudgeNonAuthorityRow =
  buildStudentEngagementEvidenceRow
    (suc (suc (suc (suc zero))))
    clickSurveyAccessNudgeNonAuthorityAxis
    "click / survey / access / nudge non-authority"
    "non-authority evidence"
    "Clicks, surveys, access, and nudges stay non-authority signals."

canonicalDataEcologyGovernanceRow :
  StudentEngagementEvidenceRow
canonicalDataEcologyGovernanceRow =
  buildStudentEngagementEvidenceRow
    (suc (suc (suc (suc (suc zero)))))
    dataEcologyGovernanceAxis
    "data ecology and governance"
    "data ecology governance evidence"
    "Learning-data ecology is custodial, governed, and not extractive."

canonicalStudentEngagementEvidenceRows :
  List StudentEngagementEvidenceRow
canonicalStudentEngagementEvidenceRows =
  canonicalOnlineEngagementRow
  ∷ canonicalCourseSpecificNudgingRow
  ∷ canonicalUnderrepresentedTransitionSuccessRow
  ∷ canonicalStudentVoiceAgencyRow
  ∷ canonicalClickSurveyAccessNudgeNonAuthorityRow
  ∷ canonicalDataEcologyGovernanceRow
  ∷ []

------------------------------------------------------------------------
-- Canonical receipts.

canonicalOnlineEngagementReceipt :
  StudentEngagementEvidenceReceipt
canonicalOnlineEngagementReceipt =
  buildStudentEngagementEvidenceReceipt
    "online engagement receipt"
    onlineEngagementAxis
    canonicalOnlineEngagementRow
    "Online engagement stays candidate-only and does not become learning proof."

canonicalCourseSpecificNudgingReceipt :
  StudentEngagementEvidenceReceipt
canonicalCourseSpecificNudgingReceipt =
  buildStudentEngagementEvidenceReceipt
    "course-specific nudging receipt"
    courseSpecificNudgingAxis
    canonicalCourseSpecificNudgingRow
    "Course-specific nudging stays candidate-only and does not become authority."

canonicalUnderrepresentedTransitionSuccessReceipt :
  StudentEngagementEvidenceReceipt
canonicalUnderrepresentedTransitionSuccessReceipt =
  buildStudentEngagementEvidenceReceipt
    "transition and success receipt"
    underrepresentedTransitionSuccessAxis
    canonicalUnderrepresentedTransitionSuccessRow
    "Transition and success for underrepresented students stays candidate-only and resists universalization."

canonicalStudentVoiceAgencyReceipt :
  StudentEngagementEvidenceReceipt
canonicalStudentVoiceAgencyReceipt =
  buildStudentEngagementEvidenceReceipt
    "student voice and agency receipt"
    studentVoiceAgencyAxis
    canonicalStudentVoiceAgencyRow
    "Voice and agency stay distinct candidate surfaces and do not become extraction."

canonicalClickSurveyAccessNudgeNonAuthorityReceipt :
  StudentEngagementEvidenceReceipt
canonicalClickSurveyAccessNudgeNonAuthorityReceipt =
  buildStudentEngagementEvidenceReceipt
    "click / survey / access / nudge non-authority receipt"
    clickSurveyAccessNudgeNonAuthorityAxis
    canonicalClickSurveyAccessNudgeNonAuthorityRow
    "Clicks, surveys, access, and nudges remain non-authority signals."

canonicalDataEcologyGovernanceReceipt :
  StudentEngagementEvidenceReceipt
canonicalDataEcologyGovernanceReceipt =
  buildStudentEngagementEvidenceReceipt
    "data ecology and governance receipt"
    dataEcologyGovernanceAxis
    canonicalDataEcologyGovernanceRow
    "Learning-data ecology remains custodial and non-extractive."

canonicalStudentEngagementEvidenceReceipts :
  List StudentEngagementEvidenceReceipt
canonicalStudentEngagementEvidenceReceipts =
  canonicalOnlineEngagementReceipt
  ∷ canonicalCourseSpecificNudgingReceipt
  ∷ canonicalUnderrepresentedTransitionSuccessReceipt
  ∷ canonicalStudentVoiceAgencyReceipt
  ∷ canonicalClickSurveyAccessNudgeNonAuthorityReceipt
  ∷ canonicalDataEcologyGovernanceReceipt
  ∷ []

------------------------------------------------------------------------
-- Canonical bridge.

canonicalStudentEngagementEvidenceBridge :
  StudentEngagementEvidenceBridge
canonicalStudentEngagementEvidenceBridge =
  mkStudentEngagementEvidenceBridge
    "student engagement evidence bridge"
    studentEngagementBridgeOwner
    canonicalStudentEngagementEvidenceAxes
    refl
    canonicalStudentEngagementResidualKinds
    refl
    canonicalStudentEngagementEvidenceRows
    canonicalStudentEngagementEvidenceReceipts
    candidateOnlyStudentEngagementRoute
    refl
    tt
    true
    refl
    true
    refl
    true
    refl
    true
    refl
    "Candidate-only student engagement evidence bridge: online engagement, course-specific nudging, transition/success for underrepresented students, student voice and agency, click/survey/access/nudge non-authority, and custodial data ecology are retained as evidence surfaces without authority promotion."

canonicalStudentEngagementBridgeCandidateOnly :
  bridgeCandidateOnly canonicalStudentEngagementEvidenceBridge ≡ true
canonicalStudentEngagementBridgeCandidateOnly =
  bridgeCandidateOnlyIsTrue canonicalStudentEngagementEvidenceBridge

canonicalStudentEngagementBridgeNonAuthority :
  bridgeNonAuthority canonicalStudentEngagementEvidenceBridge ≡ true
canonicalStudentEngagementBridgeNonAuthority =
  bridgeNonAuthorityIsTrue canonicalStudentEngagementEvidenceBridge

canonicalStudentEngagementBridgeNonExtraction :
  bridgeNonExtraction canonicalStudentEngagementEvidenceBridge ≡ true
canonicalStudentEngagementBridgeNonExtraction =
  bridgeNonExtractionIsTrue canonicalStudentEngagementEvidenceBridge

canonicalStudentEngagementBridgeNonPromotion :
  bridgeNonPromotion canonicalStudentEngagementEvidenceBridge ≡ true
canonicalStudentEngagementBridgeNonPromotion =
  bridgeNonPromotionIsTrue canonicalStudentEngagementEvidenceBridge
