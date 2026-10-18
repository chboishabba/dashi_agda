module DASHI.Law.ReviewedTreatmentBundleSemanticDedupRegression where

open import Agda.Builtin.Bool using (false; true)
open import Agda.Builtin.Equality using (_≡_)

import DASHI.Law.ReviewedTreatmentBundleSemanticDedupExact as Bundle

boundary : Bundle.ReviewedTreatmentBundleBoundary
boundary =
  Bundle.canonicalReviewedTreatmentBundleBoundary

corroborationCanShareSemanticEdge :
  Bundle.twoReviewedUnitsMaySupportOneSemanticEdge boundary ≡ true
corroborationCanShareSemanticEdge =
  Bundle.twoReviewedUnitsMaySupportOneSemanticEdgeIsTrue boundary

evidenceCountIsNotHopCount :
  Bundle.semanticHopCountMustEqualEvidenceUnitCount boundary ≡ false
evidenceCountIsNotHopCount =
  Bundle.semanticHopCountMustEqualEvidenceUnitCountIsFalse boundary

provenanceIsRetained :
  Bundle.allSupportingReviewUnitProvenanceRetained boundary ≡ true
provenanceIsRetained =
  Bundle.allSupportingReviewUnitProvenanceRetainedIsTrue boundary

residualsSurviveDedup :
  Bundle.deduplicationMayDiscardUnsupportedResiduals boundary ≡ false
residualsSurviveDedup =
  Bundle.deduplicationMayDiscardUnsupportedResidualsIsFalse boundary

bundleCreatesNoAuthority :
  Bundle.bundledTreatmentCreatesLegalAuthority boundary ≡ false
bundleCreatesNoAuthority =
  Bundle.bundledTreatmentCreatesLegalAuthorityIsFalse boundary
