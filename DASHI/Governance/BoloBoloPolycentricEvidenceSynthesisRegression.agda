module DASHI.Governance.BoloBoloPolycentricEvidenceSynthesisRegression where

open import DASHI.Core.Prelude

import DASHI.Governance.BoloBoloPolycentricEvidenceSynthesisExact as Synthesis

empiricalSamplePinned :
  Synthesis.initialEmpiricalPeerReviewedArticleCount Synthesis.canonicalPolycentricEvidenceSynthesis ≡ 179
empiricalSamplePinned = refl

coreSubsetPinned :
  Synthesis.coreFunctioningPerformanceArticleCount Synthesis.canonicalPolycentricEvidenceSynthesis ≡ 112
coreSubsetPinned = refl

positiveAndNegativeFeatures :
  Synthesis.positiveFeaturesObservedInLiterature Synthesis.canonicalPolycentricEvidenceSynthesis ≡ true
  × Synthesis.negativeFeaturesObservedInLiterature Synthesis.canonicalPolycentricEvidenceSynthesis ≡ true
positiveAndNegativeFeatures = refl , refl

ostromNestedEnterpriseMotifPinned :
  Synthesis.ostromNestedEnterprisesPrinciplePresent Synthesis.canonicalPolycentricEvidenceSynthesis ≡ true
ostromNestedEnterpriseMotifPinned = refl

baldwinDynamicFeedbackPinned :
  Synthesis.baldwinCOOFFrameworkProposed Synthesis.canonicalPolycentricEvidenceSynthesis ≡ true
  × Synthesis.baldwinFeedbackAdjustmentMechanismsExplicit Synthesis.canonicalPolycentricEvidenceSynthesis ≡ true
baldwinDynamicFeedbackPinned = refl , refl

notPanacea :
  Synthesis.polycentricityIsEmpiricalPanacea Synthesis.canonicalPolycentricEvidenceSynthesis ≡ false
notPanacea = refl

ostromNotBoloOptimum :
  Synthesis.ostromPrincipleIsBoloEmpiricalOptimum Synthesis.canonicalPolycentricEvidenceSynthesis ≡ false
ostromNotBoloOptimum = refl

baldwinDoesNotValidateBolo :
  Synthesis.baldwinFrameworkDirectlyValidatesBolo Synthesis.canonicalPolycentricEvidenceSynthesis ≡ false
baldwinDoesNotValidateBolo = refl

attributionDoesNotCollapse :
  Synthesis.structuralAlignmentMayBeStudiedWithoutAuthorshipCollapse Synthesis.canonicalPolycentricSourceAttributionBoundary ≡ true
attributionDoesNotCollapse = refl

noDirectBoloBound :
  Synthesis.directBoloCostBoundPaid Synthesis.canonicalPolycentricEvidenceSynthesis ≡ false
noDirectBoloBound = refl
