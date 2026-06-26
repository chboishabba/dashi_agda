module DASHI.Biology.RelationalEducationAgencyEcologyReceipt where

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Agda.Builtin.String using (String)
open import Agda.Builtin.Unit using (⊤; tt)

------------------------------------------------------------------------
-- Relational education / agency / ecology receipt.
--
-- Candidate-only surface.
--
-- Learning support is formalized as:
--   access x voice x agency x scaffold x relation
--
-- The student is not collapsed into a single role:
--   student-as-data != voice != partner != co-designer != custodian.
--
-- The bridge keeps feedback anti-extractive, scaffold/autonomy compatible,
-- parent allyship expert, and the learning-data ecology custodial.
-- Online learning remains tied to autonomy, access, interaction, and
-- scaffold.  Hard boundaries block universal pedagogy, analytics authority,
-- clinical dyslexia/support theorems, and institutional policy authority.

data Never : Set where

listCount : ∀ {A : Set} → List A → Nat
listCount [] = zero
listCount (_ ∷ xs) = suc (listCount xs)

------------------------------------------------------------------------
-- Route vocabulary and admissibility.

data RelationalEducationAgencyRoute : Set where
  candidateOnlyRoute : RelationalEducationAgencyRoute
  universalPedagogyRoute : RelationalEducationAgencyRoute
  analyticsAuthorityRoute : RelationalEducationAgencyRoute
  clinicalDyslexiaSupportTheoremRoute : RelationalEducationAgencyRoute
  institutionalPolicyAuthorityRoute : RelationalEducationAgencyRoute
  extractiveFeedbackRoute : RelationalEducationAgencyRoute

AdmissibleRelationalEducationAgencyRoute :
  RelationalEducationAgencyRoute →
  Set
AdmissibleRelationalEducationAgencyRoute candidateOnlyRoute = ⊤
AdmissibleRelationalEducationAgencyRoute universalPedagogyRoute = Never
AdmissibleRelationalEducationAgencyRoute analyticsAuthorityRoute = Never
AdmissibleRelationalEducationAgencyRoute clinicalDyslexiaSupportTheoremRoute = Never
AdmissibleRelationalEducationAgencyRoute institutionalPolicyAuthorityRoute = Never
AdmissibleRelationalEducationAgencyRoute extractiveFeedbackRoute = Never

universalPedagogyRouteRejected :
  AdmissibleRelationalEducationAgencyRoute universalPedagogyRoute →
  Never
universalPedagogyRouteRejected impossible = impossible

analyticsAuthorityRouteRejected :
  AdmissibleRelationalEducationAgencyRoute analyticsAuthorityRoute →
  Never
analyticsAuthorityRouteRejected impossible = impossible

clinicalDyslexiaSupportTheoremRouteRejected :
  AdmissibleRelationalEducationAgencyRoute clinicalDyslexiaSupportTheoremRoute →
  Never
clinicalDyslexiaSupportTheoremRouteRejected impossible = impossible

institutionalPolicyAuthorityRouteRejected :
  AdmissibleRelationalEducationAgencyRoute institutionalPolicyAuthorityRoute →
  Never
institutionalPolicyAuthorityRouteRejected impossible = impossible

extractiveFeedbackRouteRejected :
  AdmissibleRelationalEducationAgencyRoute extractiveFeedbackRoute →
  Never
extractiveFeedbackRouteRejected impossible = impossible

------------------------------------------------------------------------
-- Learning-support vocabulary.

data LearningSupportFactor : Set where
  accessFactor : LearningSupportFactor
  voiceFactor : LearningSupportFactor
  agencyFactor : LearningSupportFactor
  scaffoldFactor : LearningSupportFactor
  relationFactor : LearningSupportFactor

data StudentRoleKind : Set where
  studentAsDataRole : StudentRoleKind
  studentVoiceRole : StudentRoleKind
  studentPartnerRole : StudentRoleKind
  studentCodesignerRole : StudentRoleKind
  studentCustodianRole : StudentRoleKind

data RelationalEducationRoleKind : Set where
  learningSupportRole : RelationalEducationRoleKind
  antiExtractiveFeedbackRole : RelationalEducationRoleKind
  scaffoldAutonomyCompatibilityRole : RelationalEducationRoleKind
  parentAllyshipExpertiseRole : RelationalEducationRoleKind
  custodialEcologyRole : RelationalEducationRoleKind
  onlineLearningRole : RelationalEducationRoleKind
  studentAsDataDistinctRole : RelationalEducationRoleKind
  voiceDistinctRole : RelationalEducationRoleKind
  partnerDistinctRole : RelationalEducationRoleKind
  codesignerDistinctRole : RelationalEducationRoleKind
  custodianDistinctRole : RelationalEducationRoleKind
  universalPedagogyBlockedRole : RelationalEducationRoleKind
  analyticsAuthorityBlockedRole : RelationalEducationRoleKind
  clinicalDyslexiaSupportTheoremBlockedRole : RelationalEducationRoleKind
  institutionalPolicyAuthorityBlockedRole : RelationalEducationRoleKind

data RelationalEducationResidualKind : Set where
  learningSupportResidual : RelationalEducationResidualKind
  antiExtractiveFeedbackResidual : RelationalEducationResidualKind
  scaffoldAutonomyResidual : RelationalEducationResidualKind
  parentAllyshipResidual : RelationalEducationResidualKind
  custodialDataEcologyResidual : RelationalEducationResidualKind
  onlineLearningResidual : RelationalEducationResidualKind
  policyAuthorityBlockedResidual : RelationalEducationResidualKind

canonicalLearningSupportFactors :
  List LearningSupportFactor
canonicalLearningSupportFactors =
  accessFactor
  ∷ voiceFactor
  ∷ agencyFactor
  ∷ scaffoldFactor
  ∷ relationFactor
  ∷ []

canonicalStudentRoleKinds :
  List StudentRoleKind
canonicalStudentRoleKinds =
  studentAsDataRole
  ∷ studentVoiceRole
  ∷ studentPartnerRole
  ∷ studentCodesignerRole
  ∷ studentCustodianRole
  ∷ []

canonicalRelationalEducationRoleKinds :
  List RelationalEducationRoleKind
canonicalRelationalEducationRoleKinds =
  learningSupportRole
  ∷ antiExtractiveFeedbackRole
  ∷ scaffoldAutonomyCompatibilityRole
  ∷ parentAllyshipExpertiseRole
  ∷ custodialEcologyRole
  ∷ onlineLearningRole
  ∷ studentAsDataDistinctRole
  ∷ voiceDistinctRole
  ∷ partnerDistinctRole
  ∷ codesignerDistinctRole
  ∷ custodianDistinctRole
  ∷ universalPedagogyBlockedRole
  ∷ analyticsAuthorityBlockedRole
  ∷ clinicalDyslexiaSupportTheoremBlockedRole
  ∷ institutionalPolicyAuthorityBlockedRole
  ∷ []

canonicalRelationalEducationResidualKinds :
  List RelationalEducationResidualKind
canonicalRelationalEducationResidualKinds =
  learningSupportResidual
  ∷ antiExtractiveFeedbackResidual
  ∷ scaffoldAutonomyResidual
  ∷ parentAllyshipResidual
  ∷ custodialDataEcologyResidual
  ∷ onlineLearningResidual
  ∷ policyAuthorityBlockedResidual
  ∷ []

------------------------------------------------------------------------
-- Rows.

record RelationalEducationAgencyRow : Setω where
  constructor mkRelationalEducationAgencyRow
  field
    rowIndex :
      Nat

    rowLabel :
      String

    rowRoleKind :
      RelationalEducationRoleKind

    rowStudentRoleKind :
      StudentRoleKind

    rowSupportFactors :
      List LearningSupportFactor

    rowSupportFactorsAreCanonical :
      rowSupportFactors ≡ canonicalLearningSupportFactors

    rowResidualKind :
      RelationalEducationResidualKind

    rowResidualKindIsCanonical :
      rowResidualKind ≡ learningSupportResidual

    rowSurface :
      String

    rowReading :
      String

    rowCandidateOnly :
      Bool

    rowCandidateOnlyIsTrue :
      rowCandidateOnly ≡ true

    rowStudentAsDataDistinct :
      Bool

    rowStudentAsDataDistinctIsTrue :
      rowStudentAsDataDistinct ≡ true

    rowVoiceDistinct :
      Bool

    rowVoiceDistinctIsTrue :
      rowVoiceDistinct ≡ true

    rowPartnerDistinct :
      Bool

    rowPartnerDistinctIsTrue :
      rowPartnerDistinct ≡ true

    rowCodesignerDistinct :
      Bool

    rowCodesignerDistinctIsTrue :
      rowCodesignerDistinct ≡ true

    rowCustodianDistinct :
      Bool

    rowCustodianDistinctIsTrue :
      rowCustodianDistinct ≡ true

    rowAntiExtractiveFeedbackGate :
      Bool

    rowAntiExtractiveFeedbackGateIsTrue :
      rowAntiExtractiveFeedbackGate ≡ true

    rowScaffoldAutonomyCompatible :
      Bool

    rowScaffoldAutonomyCompatibleIsTrue :
      rowScaffoldAutonomyCompatible ≡ true

    rowParentAllyshipExpertise :
      Bool

    rowParentAllyshipExpertiseIsTrue :
      rowParentAllyshipExpertise ≡ true

    rowCustodialEcologyOfData :
      Bool

    rowCustodialEcologyOfDataIsTrue :
      rowCustodialEcologyOfData ≡ true

    rowOnlineLearningAutonomy :
      Bool

    rowOnlineLearningAutonomyIsTrue :
      rowOnlineLearningAutonomy ≡ true

    rowOnlineLearningAccess :
      Bool

    rowOnlineLearningAccessIsTrue :
      rowOnlineLearningAccess ≡ true

    rowOnlineLearningInteraction :
      Bool

    rowOnlineLearningInteractionIsTrue :
      rowOnlineLearningInteraction ≡ true

    rowOnlineLearningScaffold :
      Bool

    rowOnlineLearningScaffoldIsTrue :
      rowOnlineLearningScaffold ≡ true

    rowNoUniversalPedagogy :
      Bool

    rowNoUniversalPedagogyIsFalse :
      rowNoUniversalPedagogy ≡ false

    rowNoAnalyticsAuthority :
      Bool

    rowNoAnalyticsAuthorityIsFalse :
      rowNoAnalyticsAuthority ≡ false

    rowNoClinicalDyslexiaSupportTheorem :
      Bool

    rowNoClinicalDyslexiaSupportTheoremIsFalse :
      rowNoClinicalDyslexiaSupportTheorem ≡ false

    rowNoInstitutionalPolicyAuthority :
      Bool

    rowNoInstitutionalPolicyAuthorityIsFalse :
      rowNoInstitutionalPolicyAuthority ≡ false

open RelationalEducationAgencyRow public

------------------------------------------------------------------------
-- Receipts and aggregate object.

record RelationalEducationAgencyReceipt : Setω where
  constructor mkRelationalEducationAgencyReceipt
  field
    receiptLabel :
      String

    receiptRoute :
      RelationalEducationAgencyRoute

    receiptRouteIsCandidateOnly :
      receiptRoute ≡ candidateOnlyRoute

    receiptRouteAdmissible :
      AdmissibleRelationalEducationAgencyRoute receiptRoute

    receiptRow :
      RelationalEducationAgencyRow

    receiptCandidateOnly :
      Bool

    receiptCandidateOnlyIsTrue :
      receiptCandidateOnly ≡ true

    receiptNoUniversalPedagogy :
      Bool

    receiptNoUniversalPedagogyIsFalse :
      receiptNoUniversalPedagogy ≡ false

    receiptNoAnalyticsAuthority :
      Bool

    receiptNoAnalyticsAuthorityIsFalse :
      receiptNoAnalyticsAuthority ≡ false

    receiptNoClinicalDyslexiaSupportTheorem :
      Bool

    receiptNoClinicalDyslexiaSupportTheoremIsFalse :
      receiptNoClinicalDyslexiaSupportTheorem ≡ false

    receiptNoInstitutionalPolicyAuthority :
      Bool

    receiptNoInstitutionalPolicyAuthorityIsFalse :
      receiptNoInstitutionalPolicyAuthority ≡ false

    receiptReading :
      String

open RelationalEducationAgencyReceipt public

record RelationalEducationAgencyEcologyReceipt : Setω where
  constructor mkRelationalEducationAgencyEcologyReceipt
  field
    ecologyLabel :
      String

    ecologyOwner :
      String

    ecologyRoute :
      RelationalEducationAgencyRoute

    ecologyRouteIsCandidateOnly :
      ecologyRoute ≡ candidateOnlyRoute

    ecologyRouteAdmissible :
      AdmissibleRelationalEducationAgencyRoute ecologyRoute

    ecologyLearningSupportFactors :
      List LearningSupportFactor

    ecologyLearningSupportFactorsAreCanonical :
      ecologyLearningSupportFactors ≡ canonicalLearningSupportFactors

    ecologyStudentRoles :
      List StudentRoleKind

    ecologyStudentRolesAreCanonical :
      ecologyStudentRoles ≡ canonicalStudentRoleKinds

    ecologyRoleKinds :
      List RelationalEducationRoleKind

    ecologyRoleKindsAreCanonical :
      ecologyRoleKinds ≡ canonicalRelationalEducationRoleKinds

    ecologyResidualKinds :
      List RelationalEducationResidualKind

    ecologyResidualKindsAreCanonical :
      ecologyResidualKinds ≡ canonicalRelationalEducationResidualKinds

    ecologyRows :
      List RelationalEducationAgencyRow

    ecologyRowsAreCanonical :
      ecologyRows ≡ canonicalRelationalEducationAgencyRows

    ecologyReceipts :
      List RelationalEducationAgencyReceipt

    ecologyReceiptsAreCanonical :
      ecologyReceipts ≡ canonicalRelationalEducationAgencyReceipts

    ecologyCandidateOnly :
      Bool

    ecologyCandidateOnlyIsTrue :
      ecologyCandidateOnly ≡ true

    ecologyNoUniversalPedagogy :
      Bool

    ecologyNoUniversalPedagogyIsFalse :
      ecologyNoUniversalPedagogy ≡ false

    ecologyNoAnalyticsAuthority :
      Bool

    ecologyNoAnalyticsAuthorityIsFalse :
      ecologyNoAnalyticsAuthority ≡ false

    ecologyNoClinicalDyslexiaSupportTheorem :
      Bool

    ecologyNoClinicalDyslexiaSupportTheoremIsFalse :
      ecologyNoClinicalDyslexiaSupportTheorem ≡ false

    ecologyNoInstitutionalPolicyAuthority :
      Bool

    ecologyNoInstitutionalPolicyAuthorityIsFalse :
      ecologyNoInstitutionalPolicyAuthority ≡ false

    ecologyReading :
      String

open RelationalEducationAgencyEcologyReceipt public

------------------------------------------------------------------------
-- Canonical rows.

makeRelationalEducationAgencyRow :
  Nat →
  String →
  RelationalEducationRoleKind →
  StudentRoleKind →
  String →
  String →
  Bool →
  RelationalEducationAgencyRow
makeRelationalEducationAgencyRow index label role studentRole surface reading candidateOnly =
  record
    { rowIndex = index
    ; rowLabel = label
    ; rowRoleKind = role
    ; rowStudentRoleKind = studentRole
    ; rowSupportFactors = canonicalLearningSupportFactors
    ; rowSupportFactorsAreCanonical = refl
    ; rowResidualKind = learningSupportResidual
    ; rowResidualKindIsCanonical = refl
    ; rowSurface = surface
    ; rowReading = reading
    ; rowCandidateOnly = candidateOnly
    ; rowCandidateOnlyIsTrue = refl
    ; rowStudentAsDataDistinct = true
    ; rowStudentAsDataDistinctIsTrue = refl
    ; rowVoiceDistinct = true
    ; rowVoiceDistinctIsTrue = refl
    ; rowPartnerDistinct = true
    ; rowPartnerDistinctIsTrue = refl
    ; rowCodesignerDistinct = true
    ; rowCodesignerDistinctIsTrue = refl
    ; rowCustodianDistinct = true
    ; rowCustodianDistinctIsTrue = refl
    ; rowAntiExtractiveFeedbackGate = true
    ; rowAntiExtractiveFeedbackGateIsTrue = refl
    ; rowScaffoldAutonomyCompatible = true
    ; rowScaffoldAutonomyCompatibleIsTrue = refl
    ; rowParentAllyshipExpertise = true
    ; rowParentAllyshipExpertiseIsTrue = refl
    ; rowCustodialEcologyOfData = true
    ; rowCustodialEcologyOfDataIsTrue = refl
    ; rowOnlineLearningAutonomy = true
    ; rowOnlineLearningAutonomyIsTrue = refl
    ; rowOnlineLearningAccess = true
    ; rowOnlineLearningAccessIsTrue = refl
    ; rowOnlineLearningInteraction = true
    ; rowOnlineLearningInteractionIsTrue = refl
    ; rowOnlineLearningScaffold = true
    ; rowOnlineLearningScaffoldIsTrue = refl
    ; rowNoUniversalPedagogy = false
    ; rowNoUniversalPedagogyIsFalse = refl
    ; rowNoAnalyticsAuthority = false
    ; rowNoAnalyticsAuthorityIsFalse = refl
    ; rowNoClinicalDyslexiaSupportTheorem = false
    ; rowNoClinicalDyslexiaSupportTheoremIsFalse = refl
    ; rowNoInstitutionalPolicyAuthority = false
    ; rowNoInstitutionalPolicyAuthorityIsFalse = refl
    }

canonicalLearningSupportRow :
  RelationalEducationAgencyRow
canonicalLearningSupportRow =
  makeRelationalEducationAgencyRow
    zero
    "learning support"
    learningSupportRole
    studentAsDataRole
    "LearningSupport = access x voice x agency x scaffold x relation."
    "Learning support is candidate-only and keeps access, voice, agency, scaffold, and relation explicit."
    true

canonicalAntiExtractiveFeedbackRow :
  RelationalEducationAgencyRow
canonicalAntiExtractiveFeedbackRow =
  makeRelationalEducationAgencyRow
    (suc zero)
    "anti-extractive feedback"
    antiExtractiveFeedbackRole
    studentVoiceRole
    "feedback gate"
    "Feedback remains anti-extractive: it listens, does not mine."
    true

canonicalScaffoldAutonomyCompatibilityRow :
  RelationalEducationAgencyRow
canonicalScaffoldAutonomyCompatibilityRow =
  makeRelationalEducationAgencyRow
    (suc (suc zero))
    "scaffold/autonomy compatibility"
    scaffoldAutonomyCompatibilityRole
    studentPartnerRole
    "scaffold compatibility"
    "Scaffold and autonomy are compatible; support does not cancel agency."
    true

canonicalParentAllyshipExpertiseRow :
  RelationalEducationAgencyRow
canonicalParentAllyshipExpertiseRow =
  makeRelationalEducationAgencyRow
    (suc (suc (suc zero)))
    "parent allyship expertise"
    parentAllyshipExpertiseRole
    studentCodesignerRole
    "parent allyship"
    "Parents are treated as ally experts, not policy owners."
    true

canonicalCustodialEcologyRow :
  RelationalEducationAgencyRow
canonicalCustodialEcologyRow =
  makeRelationalEducationAgencyRow
    (suc (suc (suc (suc zero))))
    "custodial ecology of data"
    custodialEcologyRole
    studentCustodianRole
    "custodial data ecology"
    "Learning data lives in a custodial ecology, not an extractive pipeline."
    true

canonicalOnlineLearningRow :
  RelationalEducationAgencyRow
canonicalOnlineLearningRow =
  makeRelationalEducationAgencyRow
    (suc (suc (suc (suc (suc zero)))))
    "online learning"
    onlineLearningRole
    studentAsDataRole
    "online learning autonomy/access/interaction/scaffold"
    "Online learning is modeled through autonomy, access, interaction, and scaffold."
    true

canonicalBoundaryRow :
  RelationalEducationAgencyRow
canonicalBoundaryRow =
  makeRelationalEducationAgencyRow
    (suc (suc (suc (suc (suc (suc zero))))))
    "boundary row"
    universalPedagogyBlockedRole
    studentAsDataRole
    "boundary of authority"
    "No universal pedagogy, analytics authority, clinical dyslexia/support theorem, or institutional policy authority is promoted."
    true

canonicalRelationalEducationAgencyRows :
  List RelationalEducationAgencyRow
canonicalRelationalEducationAgencyRows =
  canonicalLearningSupportRow
  ∷ canonicalAntiExtractiveFeedbackRow
  ∷ canonicalScaffoldAutonomyCompatibilityRow
  ∷ canonicalParentAllyshipExpertiseRow
  ∷ canonicalCustodialEcologyRow
  ∷ canonicalOnlineLearningRow
  ∷ canonicalBoundaryRow
  ∷ []

canonicalRelationalEducationAgencyReceipts :
  List RelationalEducationAgencyReceipt
canonicalRelationalEducationAgencyReceipts =
  mkRelationalEducationAgencyReceipt
    "learning support receipt"
    candidateOnlyRoute
    refl
    tt
    canonicalLearningSupportRow
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
    "Learning support is access x voice x agency x scaffold x relation."
  ∷ mkRelationalEducationAgencyReceipt
      "anti-extractive feedback receipt"
      candidateOnlyRoute
      refl
      tt
      canonicalAntiExtractiveFeedbackRow
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
      "Feedback remains anti-extractive and does not become data extraction."
  ∷ mkRelationalEducationAgencyReceipt
      "online learning receipt"
      candidateOnlyRoute
      refl
      tt
      canonicalOnlineLearningRow
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
      "Online learning keeps autonomy, access, interaction, and scaffold explicit."
  ∷ []

canonicalRelationalEducationAgencyObject :
  RelationalEducationAgencyEcologyReceipt
canonicalRelationalEducationAgencyObject =
  mkRelationalEducationAgencyEcologyReceipt
    "relational education agency ecology receipt"
    "DASHI.Biology.RelationalEducationAgencyEcologyReceipt"
    candidateOnlyRoute
    refl
    tt
    canonicalLearningSupportFactors
    refl
    canonicalStudentRoleKinds
    refl
    canonicalRelationalEducationRoleKinds
    refl
    canonicalRelationalEducationResidualKinds
    refl
    canonicalRelationalEducationAgencyRows
    refl
    canonicalRelationalEducationAgencyReceipts
    refl
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
    "Candidate-only relational education agency ecology: support is access x voice x agency x scaffold x relation, while data, voice, partnership, co-design, and custodianship remain distinct roles."

------------------------------------------------------------------------
-- Top-level lemmas.

canonicalObjectRouteIsCandidateOnly :
  ecologyRoute canonicalRelationalEducationAgencyObject ≡ candidateOnlyRoute
canonicalObjectRouteIsCandidateOnly =
  ecologyRouteIsCandidateOnly canonicalRelationalEducationAgencyObject

canonicalObjectCandidateOnlyIsTrue :
  ecologyCandidateOnly canonicalRelationalEducationAgencyObject ≡ true
canonicalObjectCandidateOnlyIsTrue =
  ecologyCandidateOnlyIsTrue canonicalRelationalEducationAgencyObject

canonicalObjectNoUniversalPedagogyIsFalse :
  ecologyNoUniversalPedagogy canonicalRelationalEducationAgencyObject ≡ false
canonicalObjectNoUniversalPedagogyIsFalse =
  ecologyNoUniversalPedagogyIsFalse canonicalRelationalEducationAgencyObject

canonicalObjectNoAnalyticsAuthorityIsFalse :
  ecologyNoAnalyticsAuthority canonicalRelationalEducationAgencyObject ≡ false
canonicalObjectNoAnalyticsAuthorityIsFalse =
  ecologyNoAnalyticsAuthorityIsFalse canonicalRelationalEducationAgencyObject

canonicalObjectNoClinicalDyslexiaSupportTheoremIsFalse :
  ecologyNoClinicalDyslexiaSupportTheorem canonicalRelationalEducationAgencyObject ≡ false
canonicalObjectNoClinicalDyslexiaSupportTheoremIsFalse =
  ecologyNoClinicalDyslexiaSupportTheoremIsFalse canonicalRelationalEducationAgencyObject

canonicalObjectNoInstitutionalPolicyAuthorityIsFalse :
  ecologyNoInstitutionalPolicyAuthority canonicalRelationalEducationAgencyObject ≡ false
canonicalObjectNoInstitutionalPolicyAuthorityIsFalse =
  ecologyNoInstitutionalPolicyAuthorityIsFalse canonicalRelationalEducationAgencyObject

canonicalObjectRowsAreCanonical :
  ecologyRows canonicalRelationalEducationAgencyObject ≡
  canonicalRelationalEducationAgencyRows
canonicalObjectRowsAreCanonical =
  ecologyRowsAreCanonical canonicalRelationalEducationAgencyObject

canonicalObjectReceiptsAreCanonical :
  ecologyReceipts canonicalRelationalEducationAgencyObject ≡
  canonicalRelationalEducationAgencyReceipts
canonicalObjectReceiptsAreCanonical =
  ecologyReceiptsAreCanonical canonicalRelationalEducationAgencyObject

canonicalObjectSupportFactorsAreCanonical :
  ecologyLearningSupportFactors canonicalRelationalEducationAgencyObject ≡
  canonicalLearningSupportFactors
canonicalObjectSupportFactorsAreCanonical =
  ecologyLearningSupportFactorsAreCanonical canonicalRelationalEducationAgencyObject
