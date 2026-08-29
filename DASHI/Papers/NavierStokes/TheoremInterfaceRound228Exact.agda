module DASHI.Papers.NavierStokes.TheoremInterfaceRound228Exact where

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Physics.Closure.NSTriadKNClayFrontierRound228Exact as Frontier

------------------------------------------------------------------------
-- PAPER-FACING STATUS / ROUND228
--
-- Exact new identity on the complete physical quadratic companion:
--
--   K_pq = mixed-helicity only,
--
-- and after fixed-output swap reindexing and rational L2 aggregation,
--
--   Q_companion(N,t)
--     = 16 * sum_k || sum_{p+q=k} u_p+(t) x u_q-(t) ||^2.
--
-- Therefore FL/HH/CC are retained as possible proof tactics for estimating
-- this one object, but they are no longer three independent research leaves.
--
-- The remaining arbitrary-data mathematical theorem is a cutoff-uniform
-- time-integrated bound on that mixed-helicity convolution mass, with a
-- separately authorised physical time integration operator.
------------------------------------------------------------------------

round228ExactMixedHelicityRepresentationClosed : Bool
round228ExactMixedHelicityRepresentationClosed =
  Frontier.round228GlobalCompanionMixedHelicityIdentityClosed

round228OnlyMixedHelicitySpacetimeEstimateRemains : Bool
round228OnlyMixedHelicitySpacetimeEstimateRemains = true

round228MixedHelicitySpacetimeEstimateProved : Bool
round228MixedHelicitySpacetimeEstimateProved =
  Frontier.round228MixedHelicitySpacetimeBudgetClosed

round228PackageA : Bool
round228PackageA = Frontier.round228PackageAClosed

round228Clay : Bool
round228Clay = Frontier.round228ClayPromotion

round228ExactMixedHelicityRepresentationClosedIsTrue :
  round228ExactMixedHelicityRepresentationClosed ≡ true
round228ExactMixedHelicityRepresentationClosedIsTrue = refl

round228OnlyMixedHelicitySpacetimeEstimateRemainsIsTrue :
  round228OnlyMixedHelicitySpacetimeEstimateRemains ≡ true
round228OnlyMixedHelicitySpacetimeEstimateRemainsIsTrue = refl

round228MixedHelicitySpacetimeEstimateProvedIsFalse :
  round228MixedHelicitySpacetimeEstimateProved ≡ false
round228MixedHelicitySpacetimeEstimateProvedIsFalse = refl

round228PackageAIsFalse : round228PackageA ≡ false
round228PackageAIsFalse = refl

round228ClayIsFalse : round228Clay ≡ false
round228ClayIsFalse = refl
