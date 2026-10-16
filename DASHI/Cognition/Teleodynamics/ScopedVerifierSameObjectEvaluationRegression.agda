module DASHI.Cognition.Teleodynamics.ScopedVerifierSameObjectEvaluationRegression where

open import Agda.Builtin.Bool using (false; true)
open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Cognition.Teleodynamics.ScopedVerifierSameObjectEvaluationExact as Same

eligibilityAloneIsNotHeldOutEvidence :
  Same.SameObjectEvaluationBoundary.eligibilityAloneImpliesMatchedHeldOutExperiment
    Same.canonicalSameObjectEvaluationBoundary ≡ false
eligibilityAloneIsNotHeldOutEvidence = refl

sameCasesAreRequired :
  Same.SameObjectEvaluationBoundary.sameCandidateBaselineCaseRequired
    Same.canonicalSameObjectEvaluationBoundary ≡ true
sameCasesAreRequired = refl

sameInterventionIsRequired :
  Same.SameObjectEvaluationBoundary.sameCandidateBaselineInterventionRequired
    Same.canonicalSameObjectEvaluationBoundary ≡ true
sameInterventionIsRequired = refl

allHoldoutAxesAreRequired :
  Same.SameObjectEvaluationBoundary.completeHeldOutAxisCoverageRequired
    Same.canonicalSameObjectEvaluationBoundary ≡ true
allHoldoutAxesAreRequired = refl

consumerAdequacyIsNotWorldCompleteness :
  Same.SameObjectEvaluationBoundary.consumerAdequacyImpliesWorldCompleteness
    Same.canonicalSameObjectEvaluationBoundary ≡ false
consumerAdequacyIsNotWorldCompleteness = refl

matchedFitIsNotMechanism :
  Same.SameObjectEvaluationBoundary.matchedHeldOutFitImpliesMechanism
    Same.canonicalSameObjectEvaluationBoundary ≡ false
matchedFitIsNotMechanism = refl
