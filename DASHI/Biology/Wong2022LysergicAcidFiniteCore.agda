{-# OPTIONS --safe #-}
module DASHI.Biology.Wong2022LysergicAcidFiniteCore where

open import Agda.Builtin.Equality using (_≡_; refl)

------------------------------------------------------------------------
-- GOLDEN FINITE EVIDENCE CORE
-- No postulates, assumed facts, metas, or termination escape hatches.
--
-- Theorems concern disjoint constructors in a finite grammar only.
-- They are NOT proofs of molecular identity, experiment reproducibility,
-- biological kinetics, or any efficacy/production result.
------------------------------------------------------------------------

data NoWitness : Set where

data NamedMolecule : Set where
  dLysergicAcid : NamedMolecule
  lysergicAcidDiethylamide : NamedMolecule

data EvidenceDomain : Set where
  yeastBiosynthesisReport : EvidenceDomain
  humanReceptorStructure : EvidenceDomain
  monoamineBiosynthesis : EvidenceDomain

data ReportedScale : Set where
  oneLitreBioreactor : ReportedScale
  fourLitreBioreactor : ReportedScale

data ValidationStatus : Set where
  reportedInPrimaryPaper : ValidationStatus
  independentlyValidated : ValidationStatus

data PaperEvidenceKind : Set where
  massSpectrometricIdentityComparison : PaperEvidenceKind
  stableIsotopeOriginObservation : PaperEvidenceKind
  nmrIdentityComparison : PaperEvidenceKind
  scaleSpecificEndpointMeasurement : PaperEvidenceKind

dLaTagDistinctFromLsdTag :
  dLysergicAcid ≡ lysergicAcidDiethylamide → NoWitness
dLaTagDistinctFromLsdTag ()

productionEvidenceNotReceptorEvidence :
  yeastBiosynthesisReport ≡ humanReceptorStructure → NoWitness
productionEvidenceNotReceptorEvidence ()

productionEvidenceNotMonoaminePath :
  yeastBiosynthesisReport ≡ monoamineBiosynthesis → NoWitness
productionEvidenceNotMonoaminePath ()

reportedStatusNotIndependentValidation :
  reportedInPrimaryPaper ≡ independentlyValidated → NoWitness
reportedStatusNotIndependentValidation ()

------------------------------------------------------------------------
-- TYPE-INDEXED EVIDENCE ADMISSION.
--
-- Existing source attribution and scientific mechanism owners remain the
-- authoritative metadata carriers.  These minimal local proof gates only
-- prevent an unreviewed report from being used as a proof of independent
-- verification or sample-level chemical identity.
------------------------------------------------------------------------

data EvidenceReviewTier : Set where
  authorReported : EvidenceReviewTier
  sourceDataReviewed : EvidenceReviewTier
  independentlyReanalysed : EvidenceReviewTier

data MayAdmitForIndependentValidation : EvidenceReviewTier → Set where
  independentReanalysisReceipt :
    MayAdmitForIndependentValidation independentlyReanalysed

authorReportCannotCertifyIndependentValidation :
  MayAdmitForIndependentValidation authorReported → NoWitness
authorReportCannotCertifyIndependentValidation ()

sourceDataReviewCannotCertifyIndependentValidation :
  MayAdmitForIndependentValidation sourceDataReviewed → NoWitness
sourceDataReviewCannotCertifyIndependentValidation ()

data IdentityCarrier : Set where
  publishedCompoundRegistry : IdentityCarrier
  authorReportedAssaySpecimen : IdentityCarrier
  receptorBoundLigand : IdentityCarrier

data IdentityEvidence : IdentityCarrier → IdentityCarrier → Set where
  registryReflexive :
    IdentityEvidence publishedCompoundRegistry publishedCompoundRegistry
  specimenReflexive :
    IdentityEvidence authorReportedAssaySpecimen authorReportedAssaySpecimen
  receptorReflexive :
    IdentityEvidence receptorBoundLigand receptorBoundLigand

registryTagCannotCertifyAssaySample :
  IdentityEvidence publishedCompoundRegistry authorReportedAssaySpecimen →
  NoWitness
registryTagCannotCertifyAssaySample ()

assaySampleTagCannotCertifyReceptorIdentity :
  IdentityEvidence authorReportedAssaySpecimen receptorBoundLigand →
  NoWitness
assaySampleTagCannotCertifyReceptorIdentity ()

data FigureObservationKind : Set where
  experimentalEndpoint : FigureObservationKind
  authorScenarioProjection : FigureObservationKind

experimentNotAuthorProjection :
  experimentalEndpoint ≡ authorScenarioProjection → NoWitness
experimentNotAuthorProjection ()
