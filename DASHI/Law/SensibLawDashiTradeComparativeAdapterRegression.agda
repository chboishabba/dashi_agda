module DASHI.Law.SensibLawDashiTradeComparativeAdapterRegression where

open import Agda.Builtin.Bool using (false; true)
open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Law.SensibLawDashiTradeComparativeAdapterExact as T

boundary : T.DashiTradeComparativeBoundary
boundary = T.canonicalDashiTradeComparativeBoundary

quotientStillRepresentation :
  T.quotientIsRepresentationNotWorldIdentity boundary ≡ true
quotientStillRepresentation = refl

richerQueryStillMayNotFactor :
  T.richerQueryMayFailToFactorThroughQuotient boundary ≡ true
richerQueryStillMayNotFactor = refl

beliefStillSeparate :
  T.beliefIsSeparateChangeLayer boundary ≡ true
beliefStillSeparate = refl

sameWorldDifferentPolicyStillPossible :
  T.sameWorldDifferentPolicyRepresentationPossible boundary ≡ true
sameWorldDifferentPolicyStillPossible = refl

actionStillNotWorldInput :
  T.actionOutcomeIsNotWorldInput boundary ≡ true
actionStillNotWorldInput = refl

justificationStillNotCausalProof :
  T.justificationChainCreatesCausalProof boundary ≡ false
justificationStillNotCausalProof = refl
