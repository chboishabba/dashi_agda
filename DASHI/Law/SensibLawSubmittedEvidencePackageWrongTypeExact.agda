module DASHI.Law.SensibLawSubmittedEvidencePackageWrongTypeExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Law.SensibLawTemporalHealthEvidenceWrongTypeExact as Temporal
import DASHI.Law.SensibLawWrongTypeCausationElementExact as Element

------------------------------------------------------------------------
-- SUBMITTED MULTIMODAL EVIDENCE PACKAGE -> WRONGTYPE BOUNDARY
--
-- This owner sits above the single-observation temporal-health layer.
-- It represents one submitted legal carrier containing several distinct
-- evidentiary modalities without collapsing their authority or silently
-- promoting mutual consistency into medical/legal causation.
------------------------------------------------------------------------

data EvidenceModality : Set where
  narrativeModality : EvidenceModality
  recordingModality : EvidenceModality
  physiologicalModality : EvidenceModality
  damagesModality : EvidenceModality
  medicalModality : EvidenceModality

record SubmittedEvidenceComponent : Set₁ where
  constructor submittedEvidenceComponent
  field
    modality : EvidenceModality
    componentReference : String
    carrierReference : String
    pageOrRangeReference : String

open SubmittedEvidenceComponent public

record SubmittedEvidencePackage : Set₁ where
  constructor submittedEvidencePackage
  field
    packageReference : String
    carrierReference : String
    components : List SubmittedEvidenceComponent
    temporalHealthLayerReference : String

open SubmittedEvidencePackage public

record WrongTypeSubmittedEvidencePackage
    {declaration : Element.WrongTypeCausationElementDeclaration}
    (weld : Element.ViolationWrongTypeCausationElementWeld declaration) : Set₁ where
  constructor wrongTypeSubmittedEvidencePackage
  field
    submittedPackage : SubmittedEvidencePackage
    temporalEvidence : Temporal.WrongTypeTemporalHealthEvidence weld
    sameWrongTypeAndElementWeld :
      Element.ViolationWrongTypeCausationElementWeld declaration
    sameWeldReceipt : sameWrongTypeAndElementWeld ≡ weld
    packageAdmissionReference : String

open WrongTypeSubmittedEvidencePackage public

record SubmittedEvidencePackagePayment
    {declaration : Element.WrongTypeCausationElementDeclaration}
    {weld : Element.ViolationWrongTypeCausationElementWeld declaration}
    (evidence : WrongTypeSubmittedEvidencePackage weld) : Set₁ where
  constructor submittedEvidencePackagePayment
  field
    factualPayment : Element.FactualCausationElementPayment weld
    paymentReference : String

open SubmittedEvidencePackagePayment public

------------------------------------------------------------------------
-- Package-level authority boundary.
------------------------------------------------------------------------

record SubmittedEvidencePackageBoundary : Set where
  constructor submittedEvidencePackageBoundary
  field
    commonCarrierCreatesCommonAuthority : Bool
    commonCarrierCreatesCommonAuthorityIsFalse :
      commonCarrierCreatesCommonAuthority ≡ false

    mutuallyConsistentModalitiesAutomaticallyCause : Bool
    mutuallyConsistentModalitiesAutomaticallyCauseIsFalse :
      mutuallyConsistentModalitiesAutomaticallyCause ≡ false

    damagesClaimAutomaticallyProvesExpenditure : Bool
    damagesClaimAutomaticallyProvesExpenditureIsFalse :
      damagesClaimAutomaticallyProvesExpenditure ≡ false

    narrativeHypertensionAutomaticallyCreatesDiagnosis : Bool
    narrativeHypertensionAutomaticallyCreatesDiagnosisIsFalse :
      narrativeHypertensionAutomaticallyCreatesDiagnosis ≡ false

    missingLaterMedicalCarrierErasesSubmittedInjuryCase : Bool
    missingLaterMedicalCarrierErasesSubmittedInjuryCaseIsFalse :
      missingLaterMedicalCarrierErasesSubmittedInjuryCase ≡ false

    factualCausationStillRequiresWrongTypePayment : Bool
    factualCausationStillRequiresWrongTypePaymentIsTrue :
      factualCausationStillRequiresWrongTypePayment ≡ true

canonicalSubmittedEvidencePackageBoundary : SubmittedEvidencePackageBoundary
canonicalSubmittedEvidencePackageBoundary =
  submittedEvidencePackageBoundary
    false refl
    false refl
    false refl
    false refl
    false refl
    true refl

------------------------------------------------------------------------
-- Firewalls.
------------------------------------------------------------------------

data CommonCarrierCreatesCommonAuthority : Set where
data MutuallyConsistentModalitiesAutomaticallyCause : Set where
data DamagesClaimAutomaticallyProvesExpenditure : Set where
data NarrativeHypertensionAutomaticallyDiagnosis : Set where
data MissingLaterMedicalCarrierErasesSubmittedInjuryCase : Set where

commonCarrierDoesNotCreateCommonAuthority :
  CommonCarrierCreatesCommonAuthority → ⊥
commonCarrierDoesNotCreateCommonAuthority ()

consistentModalitiesDoNotAutoCause :
  MutuallyConsistentModalitiesAutomaticallyCause → ⊥
consistentModalitiesDoNotAutoCause ()

damagesClaimDoesNotAutoProveExpenditure :
  DamagesClaimAutomaticallyProvesExpenditure → ⊥
damagesClaimDoesNotAutoProveExpenditure ()

hypertensionNarrativeDoesNotAutoDiagnose :
  NarrativeHypertensionAutomaticallyDiagnosis → ⊥
hypertensionNarrativeDoesNotAutoDiagnose ()

missingLaterMedicalCarrierDoesNotEraseSubmittedCase :
  MissingLaterMedicalCarrierErasesSubmittedInjuryCase → ⊥
missingLaterMedicalCarrierDoesNotEraseSubmittedInjuryCase ()

------------------------------------------------------------------------
-- QCAT 0096/22 submitted-package regression fixture.
--
-- The carrier references are intentionally evidentiary, not medical opinions.
-- May 2022 is closed at the submitted-package level.  The separately named
-- 30.6.2022 J. Brown medical report remains a later-carrier residual and is
-- not asserted to be inside the May 83-page carrier.
------------------------------------------------------------------------

qcat0096PackageReference : String
qcat0096PackageReference =
  "QCAT:0096/22 final 83-page submitted multimodal evidence package"

qcat0096NarrativeComponent : SubmittedEvidenceComponent
qcat0096NarrativeComponent =
  submittedEvidenceComponent
    narrativeModality
    "stress/injury narrative plus hypertension statement"
    Temporal.qcat0096FinalBundle
    "case outline/orders sought/page 43 narrative"

qcat0096RecordingComponent : SubmittedEvidenceComponent
qcat0096RecordingComponent =
  submittedEvidenceComponent
    recordingModality
    "transcripts of recorded interactions including health/injury material"
    Temporal.qcat0096FinalBundle
    "transcript section pages 44-79"

qcat0096PhysiologicalComponent : SubmittedEvidenceComponent
qcat0096PhysiologicalComponent =
  submittedEvidenceComponent
    physiologicalModality
    "embedded physiological tables and charts"
    Temporal.qcat0096FinalBundle
    "pages 82-83"

qcat0096DamagesComponent : SubmittedEvidenceComponent
qcat0096DamagesComponent =
  submittedEvidenceComponent
    damagesModality
    "requested damages including psychology medication GP specialist carer and per-diem components"
    Temporal.qcat0096FinalBundle
    "page 80"

qcat0096MayPackage : SubmittedEvidencePackage
qcat0096MayPackage =
  submittedEvidencePackage
    qcat0096PackageReference
    Temporal.qcat0096FinalBundle
    (qcat0096NarrativeComponent ∷
     qcat0096RecordingComponent ∷
     qcat0096DamagesComponent ∷
     qcat0096PhysiologicalComponent ∷ [])
    "SensibLawTemporalHealthEvidenceWrongTypeExact"

qcat0096LaterMedicalResidual : String
qcat0096LaterMedicalResidual =
  "30.6.2022 J. Brown Med Report is a later Russell-carrier residual; relation to later submission unresolved"

record QCAT0096SubmittedPackageFixture : Set where
  constructor qcat0096SubmittedPackageFixture
  field
    submittedPackage : SubmittedEvidencePackage
    healthPackageSubmittedInSubstance : Bool
    healthPackageSubmittedInSubstanceIsTrue :
      healthPackageSubmittedInSubstance ≡ true
    quantifiedDamagesPresent : Bool
    quantifiedDamagesPresentIsTrue : quantifiedDamagesPresent ≡ true
    embeddedPhysiologicalChartsPresent : Bool
    embeddedPhysiologicalChartsPresentIsTrue :
      embeddedPhysiologicalChartsPresent ≡ true
    laterMedicalCarrierReference : String
    laterMedicalCarrierInsideMayBundle : Bool
    laterMedicalCarrierInsideMayBundleIsFalse :
      laterMedicalCarrierInsideMayBundle ≡ false
    laterMedicalCarrierSubmissionRelationResolved : Bool
    laterMedicalCarrierSubmissionRelationResolvedIsFalse :
      laterMedicalCarrierSubmissionRelationResolved ≡ false

open QCAT0096SubmittedPackageFixture public

qcat0096SubmittedPackageFixture : QCAT0096SubmittedPackageFixture
qcat0096SubmittedPackageFixture =
  qcat0096SubmittedPackageFixture
    qcat0096MayPackage
    true refl
    true refl
    true refl
    qcat0096LaterMedicalResidual
    false refl
    false refl
