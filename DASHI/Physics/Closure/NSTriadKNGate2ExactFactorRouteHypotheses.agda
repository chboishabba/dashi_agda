module DASHI.Physics.Closure.NSTriadKNGate2ExactFactorRouteHypotheses where

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import DASHI.Physics.Closure.DirectionalFactorTransportBase
  using (DirectionalFactorTransportModel)
open import DASHI.Physics.Closure.ExactKNAFactorRouteBase
  using (ExactKNAFactorRouteModel)

----------------------------------------------------------------------
-- Exact K_N(A) factor-route hypothesis package.
--
-- This isolates the sharpest currently surviving Gate 2 transfer lane:
--
--   transported-ratio = directional-factor * seam-rayleigh-ratio
--   coarse-transport  = coarse-factor      * seam-rayleigh-ratio
--   directional-factor ≤ coarse-factor
--   coarse-transport ≤ quarter-threshold
--   exact-kna-ratio = transported-ratio
--
-- Once those hypotheses are witnessed on the true carrier, the exact
-- K_N(A) quarter bound follows by the factor route alone.  This is the
-- cleanest abstraction of the "directional beats coarse" strategy.

canonicalBoundaryText : String
canonicalBoundaryText =
  "Exact Gate 2 factor-route hypothesis package: once the true carrier identifies exact K_N(A) with the directional transported ratio, reconstructs both directional and coarse products from the same seam Rayleigh ratio, proves the directional factor is no larger than the coarse factor, and closes the coarse quarter budget, the exact K_N(A) quarter bound follows immediately."

record NSTriadKNGate2ExactFactorRouteHypotheses : Setω where
  constructor mkNSTriadKNGate2ExactFactorRouteHypotheses
  field
    factorRouteModel : ExactKNAFactorRouteModel

    boundaryText : String
    boundaryTextIsCanonical :
      boundaryText ≡ canonicalBoundaryText

    factorTransportModel :
      DirectionalFactorTransportModel
    factorTransportModelIsUnderlying :
      factorTransportModel
        ≡ ExactKNAFactorRouteModel.factorTransportModel factorRouteModel

    directionalTransportIdentityWitness :
      DirectionalFactorTransportModel.transported-ratio
        factorTransportModel
      ≡
      (DirectionalFactorTransportModel._*_
        factorTransportModel
        (DirectionalFactorTransportModel.directional-factor
          factorTransportModel)
        (DirectionalFactorTransportModel.seam-rayleigh-ratio
          factorTransportModel))

    coarseTransportIdentityWitness :
      DirectionalFactorTransportModel.coarse-transport
        factorTransportModel
      ≡
      (DirectionalFactorTransportModel._*_
        factorTransportModel
        (DirectionalFactorTransportModel.coarse-factor
          factorTransportModel)
        (DirectionalFactorTransportModel.seam-rayleigh-ratio
          factorTransportModel))

    directionalFactor≤CoarseFactorWitness :
      DirectionalFactorTransportModel._≤_
        factorTransportModel
        (DirectionalFactorTransportModel.directional-factor
          factorTransportModel)
        (DirectionalFactorTransportModel.coarse-factor
          factorTransportModel)

    exactRestrictionIdentityWitness :
      ExactKNAFactorRouteModel.exact-kna-ratio factorRouteModel
      ≡
      ExactKNAFactorRouteModel.transported-ratio factorRouteModel

    coarseTransportQuarterWitness :
      ExactKNAFactorRouteModel._≤_ factorRouteModel
        (ExactKNAFactorRouteModel.coarse-transport factorRouteModel)
        (ExactKNAFactorRouteModel.quarter-threshold factorRouteModel)

    exactKNAFactorRouteBound :
      ExactKNAFactorRouteModel._≤_ factorRouteModel
        (ExactKNAFactorRouteModel.exact-kna-ratio factorRouteModel)
        (ExactKNAFactorRouteModel.quarter-threshold factorRouteModel)

    packageInstalled : Bool
    packageInstalledIsTrue :
      packageInstalled ≡ true

    hypothesesAreAnalyticNotYetGeneralNS : Bool
    hypothesesAreAnalyticNotYetGeneralNSIsTrue :
      hypothesesAreAnalyticNotYetGeneralNS ≡ true

    exactKNAFactorRouteProved : Bool
    exactKNAFactorRouteProvedIsFalse :
      exactKNAFactorRouteProved ≡ false

open NSTriadKNGate2ExactFactorRouteHypotheses public

mkExactKNAFactorRouteHypothesisConsequences :
  (m : ExactKNAFactorRouteModel) →
  ExactKNAFactorRouteModel._≤_ m
    (ExactKNAFactorRouteModel.exact-kna-ratio m)
    (ExactKNAFactorRouteModel.quarter-threshold m)
mkExactKNAFactorRouteHypothesisConsequences =
  ExactKNAFactorRouteModel.exactKNA≤quarter
