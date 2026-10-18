module DASHI.Education.DigitalESDTransferablePrincipleDerivationMethodRegression where

open import Agda.Builtin.Bool using (false; true)
open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Education.DigitalESDTransferablePrincipleDerivationMethodExact as Method

stageCountRegression : Method.principleDerivationStageCount ≡ 6
stageCountRegression = refl

preSearchGenerationAllowedRegression :
  Method.PrincipleDerivationBoundary.candidatePrincipleGenerationMayPrecedeSearchClosure
    Method.canonicalPrincipleDerivationBoundary
  ≡ true
preSearchGenerationAllowedRegression = refl

structuredCorpusChallengeStillUnobservedRegression :
  Method.PrincipleDerivationBoundary.structuredCorpusChallengeObserved
    Method.canonicalPrincipleDerivationBoundary
  ≡ false
structuredCorpusChallengeStillUnobservedRegression = refl

finalPromotionBlockedBeforeSearchClosureRegression :
  Method.PrincipleDerivationBoundary.finalPrinciplePromotionBeforeSearchClosure
    Method.canonicalPrincipleDerivationBoundary
  ≡ false
finalPromotionBlockedBeforeSearchClosureRegression = refl

revisionRequiredAfterScreeningRegression :
  Method.PrincipleDerivationBoundary.revisionAfterScreenedCorpusRequired
    Method.canonicalPrincipleDerivationBoundary
  ≡ true
revisionRequiredAfterScreeningRegression = refl
