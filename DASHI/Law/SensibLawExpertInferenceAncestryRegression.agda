module DASHI.Law.SensibLawExpertInferenceAncestryRegression where

open import DASHI.Core.Prelude
open import Data.Empty using (⊥)

import DASHI.Law.SensibLawExpertInferenceAncestryExact as Ancestry
import DASHI.Core.QueryIndexedProjectionAdequacyExact as Query
import DASHI.Core.ObserverRefinementLatticeExact as Observer

------------------------------------------------------------------------
-- RED contract: prior-opinion exposure / inference ancestry.
--
-- Two expert reports may be distinct documents and may agree while one expert
-- has consumed an earlier expert opinion before forming their own inference.
-- Document count and agreement therefore cannot manufacture independent
-- inference ancestry.  The repair is to retain the ancestry coordinate.
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

citationDoesNotCreateLegalAuthority :
  Ancestry.CitationCreatesLegalAuthority → ⊥
citationDoesNotCreateLegalAuthority =
  Ancestry.citationDoesNotCreateLegalAuthority

parentStructuralPrecedentIsExplicit : Ancestry.ParentStructuralPrecedent
parentStructuralPrecedentIsExplicit = Ancestry.parentStructuralPrecedent
