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

notPanacea :
  Synthesis.polycentricityIsEmpiricalPanacea Synthesis.canonicalPolycentricEvidenceSynthesis ≡ false
notPanacea = refl

noDirectBoloBound :
  Synthesis.directBoloCostBoundPaid Synthesis.canonicalPolycentricEvidenceSynthesis ≡ false
noDirectBoloBound = refl
