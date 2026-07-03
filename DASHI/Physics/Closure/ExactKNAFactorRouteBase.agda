module DASHI.Physics.Closure.ExactKNAFactorRouteBase where

open import Level using (zero)
open import Relation.Binary.PropositionalEquality
  using (_≡_; subst; sym)
open import DASHI.MDL.MDLDescentTradeoff
  using (AddMonoid; OrderedMonoid)
open import DASHI.Physics.Closure.DirectionalFactorTransportBase
  using (DirectionalFactorTransportModel)

----------------------------------------------------------------------
-- Exact K_N(A) factor-route kernel.
--
-- This packages the live Gate 2 transfer strategy at the factor level:
--
--   transported-ratio = directional-factor * seam-rayleigh-ratio
--   coarse-transport  = coarse-factor      * seam-rayleigh-ratio
--
-- If the directional factor is no larger than the coarse factor, then the
-- directional transport is no larger than the coarse transport.  If the
-- coarse transport is already quarter-bounded, then the exact K_N(A) ratio
-- closes as soon as it is identified with the directional transport.

record ExactKNAFactorRouteModel : Set₁ where
  constructor mkExactKNAFactorRouteModel
  field
    factorTransportModel : DirectionalFactorTransportModel

  open DirectionalFactorTransportModel factorTransportModel public

  field
    exact-kna-ratio : N
    quarter-threshold : N

    exactRestrictionIdentity :
      exact-kna-ratio ≡ transported-ratio

    coarseTransport≤quarter :
      coarse-transport ≤ quarter-threshold

  transported≤quarter : transported-ratio ≤ quarter-threshold
  transported≤quarter =
    trans≤
      transported-ratio
      coarse-transport
      quarter-threshold
      transported≤coarse
      coarseTransport≤quarter

  exactKNA≤quarter : exact-kna-ratio ≤ quarter-threshold
  exactKNA≤quarter =
    subst
      (λ t → t ≤ quarter-threshold)
      (sym exactRestrictionIdentity)
      transported≤quarter

open ExactKNAFactorRouteModel public
