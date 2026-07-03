module DASHI.Physics.Closure.NSTriadKNGate2ExactFactorRouteArithmetic where

open import Agda.Builtin.Equality using (_≡_; refl)
open import DASHI.Physics.Closure.DirectionalFactorTransportBase
  as FactorTransport
open import DASHI.Physics.Closure.ExactKNAFactorRouteBase
  as FactorRoute
open import DASHI.Physics.Closure.NSTriadKNGate2ExactFactorRouteHypotheses
  using ( NSTriadKNGate2ExactFactorRouteHypotheses
        ; mkNSTriadKNGate2ExactFactorRouteHypotheses
        )
open import DASHI.Physics.Closure.NSTriadKNGate2ExactKNAOperatorTransfer
  using (exactKNAFactorRouteConditionalBound)
open import DASHI.Physics.Closure.NSTriadKNGate2FactorRouteArithmetic
  using ( canonicalDirectionalFactorTransportModel
        ; canonicalExactKNAFactorRouteModel
        )

----------------------------------------------------------------------
-- Concrete arithmetic inhabitant of the exact K_N(A) factor-route
-- hypothesis package.
--
-- This is still seam-local arithmetic, not the true NS carrier, but it
-- now inhabits the factor-route theorem surface directly rather than only
-- the raw kernel.

canonicalDirectionalTransportIdentity :
  FactorTransport.directionalTransportIdentity
    canonicalDirectionalFactorTransportModel
canonicalDirectionalTransportIdentity = refl

canonicalCoarseTransportIdentity :
  FactorTransport.coarseTransportIdentity
    canonicalDirectionalFactorTransportModel
canonicalCoarseTransportIdentity = refl

canonicalDirectionalFactorLeqCoarse :
  FactorTransport.directionalFactor≤CoarseFactor
    canonicalDirectionalFactorTransportModel
canonicalDirectionalFactorLeqCoarse =
  FactorTransport.directionalFactor≤CoarseFactor
    canonicalDirectionalFactorTransportModel

canonicalExactRestrictionIdentity :
  FactorRoute.exactRestrictionIdentity
    canonicalExactKNAFactorRouteModel
canonicalExactRestrictionIdentity = refl

canonicalCoarseTransportQuarter :
  FactorRoute.coarseTransport≤quarter
    canonicalExactKNAFactorRouteModel
canonicalCoarseTransportQuarter =
  FactorRoute.coarseTransport≤quarter
    canonicalExactKNAFactorRouteModel

canonicalExactKNAFactorRouteBound :
  FactorRoute._≤_
    canonicalExactKNAFactorRouteModel
    (FactorRoute.exact-kna-ratio canonicalExactKNAFactorRouteModel)
    (FactorRoute.quarter-threshold canonicalExactKNAFactorRouteModel)
canonicalExactKNAFactorRouteBound =
  exactKNAFactorRouteConditionalBound
    canonicalExactKNAFactorRouteModel

canonicalExactFactorRouteHypotheses :
  NSTriadKNGate2ExactFactorRouteHypotheses
canonicalExactFactorRouteHypotheses =
  mkNSTriadKNGate2ExactFactorRouteHypotheses
    canonicalExactKNAFactorRouteModel
    "Exact Gate 2 factor-route hypothesis package: once the true carrier identifies exact K_N(A) with the directional transported ratio, reconstructs both directional and coarse products from the same seam Rayleigh ratio, proves the directional factor is no larger than the coarse factor, and closes the coarse quarter budget, the exact K_N(A) quarter bound follows immediately."
    refl
    canonicalDirectionalFactorTransportModel
    refl
    canonicalDirectionalTransportIdentity
    canonicalCoarseTransportIdentity
    canonicalDirectionalFactorLeqCoarse
    canonicalExactRestrictionIdentity
    canonicalCoarseTransportQuarter
    canonicalExactKNAFactorRouteBound
    true
    refl
    true
    refl
    false
    refl
