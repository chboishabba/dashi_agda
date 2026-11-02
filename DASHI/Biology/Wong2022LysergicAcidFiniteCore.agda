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
