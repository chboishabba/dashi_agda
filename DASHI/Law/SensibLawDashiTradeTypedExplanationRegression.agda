module DASHI.Law.SensibLawDashiTradeTypedExplanationRegression where

open import Agda.Builtin.Bool using (false; true)
open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Law.SensibLawChangeLocusExact as Locus
import DASHI.Law.SensibLawDashiTradeTypedExplanationExact as T
import DASHI.Law.SensibLawTypedAnswerChangingExplanationExact as Explain

boundary : T.DashiTradeTypedExplanationBoundary
boundary = T.canonicalDashiTradeTypedExplanationBoundary

phase9StillApplicability :
  Explain.layer T.phase9AnswerChangeStep ≡ Locus.applicabilityLayer
phase9StillApplicability = refl

sharedAbiStillUsed :
  T.usesSharedTypedExplanationAbi boundary ≡ true
sharedAbiStillUsed = refl

justificationStillRetained :
  T.justificationRefsRetained boundary ≡ true
justificationStillRetained = refl

predictionStillForbidden :
  T.explanationPredictsMarketOutcome boundary ≡ false
predictionStillForbidden = refl

truthPromotionStillForbidden :
  T.explanationCreatesClaimTruth boundary ≡ false
truthPromotionStillForbidden = refl
