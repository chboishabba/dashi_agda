module DASHI.Law.SensibLawExpertInferenceAncestryRegression where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (false)
open import Agda.Builtin.Equality using (_≡_)
open import Data.Empty using (⊥)

import DASHI.Law.SensibLawExpertInferenceAncestryExact as Ancestry
import DASHI.Core.ObserverRefinementLatticeExact as Observer
import DASHI.Core.AttributedSourceCore as Attribution

------------------------------------------------------------------------
-- RED contract: prior-opinion exposure / inference ancestry.
--
-- Two expert reports may be distinct documents and may agree while one expert
-- has consumed an earlier expert opinion before forming their own inference.
-- Document count and agreement therefore cannot manufacture independent
-- inference ancestry.  Conversely, observed exposure alone cannot prove causal
-- influence.  The repair is to retain ancestry/influence as their own axes.
------------------------------------------------------------------------

ancestryDefectIsPresent : Ancestry.InferenceAncestryQueryAdequacyDefect
ancestryDefectIsPresent = Ancestry.inferenceAncestryQueryAdequacyDefect

agreementCannotFactorIndependentAncestry :
  Ancestry.InferenceAncestryQueryAdequate → ⊥
agreementCannotFactorIndependentAncestry =
  Ancestry.inferenceAncestryQueryNotAdequate

joinedAncestryRefinesAgreement :
  Observer.Refines
    Ancestry.nominalReportAgreementSurface
    Ancestry.reportAgreementPlusInferenceAncestry
joinedAncestryRefinesAgreement =
  Ancestry.reportAgreementPlusInferenceAncestryRefinesAgreement

joinedAncestryIsStrictRepair :
  Observer.StrictRefinement
    Ancestry.nominalReportAgreementSurface
    Ancestry.reportAgreementPlusInferenceAncestry
joinedAncestryIsStrictRepair =
  Ancestry.reportAgreementPlusInferenceAncestryStrictRefinement

exposureInfluenceDefectIsPresent :
  Ancestry.ExposureInfluenceQueryAdequacyDefect
exposureInfluenceDefectIsPresent =
  Ancestry.exposureInfluenceQueryAdequacyDefect

exposureCannotFactorCausalInfluence :
  Ancestry.ExposureInfluenceQueryAdequate → ⊥
exposureCannotFactorCausalInfluence =
  Ancestry.exposureInfluenceQueryNotAdequate

priorOpinionExposureDoesNotAutomaticallyDestroyEvidence :
  Ancestry.PriorOpinionExposureMeansNoEvidence → ⊥
priorOpinionExposureDoesNotAutomaticallyDestroyEvidence =
  Ancestry.priorOpinionExposureDoesNotMeanNoEvidence

separateDocumentsDoNotAutomaticallyProveIndependentInference :
  Ancestry.SeparateDocumentsAutomaticallyIndependentInference → ⊥
separateDocumentsDoNotAutomaticallyProveIndependentInference =
  Ancestry.separateDocumentsDoNotAutomaticallyProveIndependentInference

agreementDoesNotAutomaticallyProveIndependentInference :
  Ancestry.AgreementAutomaticallyIndependentInference → ⊥
agreementDoesNotAutomaticallyProveIndependentInference =
  Ancestry.agreementDoesNotAutomaticallyProveIndependentInference

exposureDoesNotAutomaticallyProveCausalDependence :
  Ancestry.PriorOpinionExposureAutomaticallyProvesCausalDependence → ⊥
exposureDoesNotAutomaticallyProveCausalDependence =
  Ancestry.priorOpinionExposureDoesNotAutomaticallyProveCausalDependence

noRecordedExposureDoesNotAutomaticallyProveIndependence :
  Ancestry.NoRecordedExposureAutomaticallyIndependentInference → ⊥
noRecordedExposureDoesNotAutomaticallyProveIndependence =
  Ancestry.noRecordedExposureDoesNotAutomaticallyProveIndependentInference

citationDoesNotCreateLegalAuthority :
  Ancestry.CitationCreatesLegalAuthority → ⊥
citationDoesNotCreateLegalAuthority =
  Ancestry.citationDoesNotCreateLegalAuthority

pilditchCitationIsNonPromoting :
  Attribution.citationCreatesAuthority Ancestry.pilditchDependencySource ≡ false
pilditchCitationIsNonPromoting =
  Attribution.citationCreatesAuthorityIsFalse Ancestry.pilditchDependencySource

parentStructuralPrecedentIsExplicit : Ancestry.ParentStructuralPrecedent
parentStructuralPrecedentIsExplicit = Ancestry.parentStructuralPrecedent
