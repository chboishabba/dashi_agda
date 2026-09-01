module DASHI.Physics.Closure.NSTriadKNSignedGramBypassesCoherentMajorantRound373Exact where

------------------------------------------------------------------------
-- ROUND373 / BIDI DEPENDENCY CORRECTION: R222 IS NOT REQUIRED BY R353/R354
--
-- Historical Round222 froze the then-authoritative Package-A frontier as a
-- NONNEGATIVE coherent Gram majorant R_coh(N,t) satisfying
--
--   gramDebt(N,t) <= R_coh(N,t)
--
-- together with a cutoff-uniform bound on integral R_coh.
--
-- The newer R303/R353 lane closes a different, weaker sufficient interface:
-- it retains the Gram channel SIGNED through time and asks only for a cutoff-
-- uniform upper bound on the integrated signed debt.  R293 consumes exactly
-- that signed integrated theorem, and R354 reaches the literal R240 Package-A
-- object without constructing `PhysicalCoherentGramResidualBudget`.
--
-- Therefore R222 remains a valid sufficient route, but it is no longer an
-- authoritative prerequisite for Package A.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Rational.Base using (ℚ)

import DASHI.Physics.Closure.NSTriadKNComplex3ExactCarrier as C3
import DASHI.Physics.Closure.NSTriadKNRationalOrderedFiniteL2 as Rational
import DASHI.Physics.Closure.NSTriadKNPhysicalNSGalerkinTrajectoryRound240Exact as R240
import DASHI.Physics.Closure.NSTriadKNR293ToPhysicalPackageARound354Exact as R354
import DASHI.Physics.Closure.NSTriadKNPhysicalCoherentGramResidualTargetRound222Exact as R222

F : C3.RealField _
F = Rational.rationalRealField

module SignedGramBypassesCoherentMajorant
    (Time : Set)
    (initialTime : Time)
    (integrateTo : (Time → ℚ) → Time → ℚ)
    (DerivativeOf :
      (Time → C3.Complex3 F) →
      (Time → C3.Complex3 F) → Set) where

  module Dyn = R240.PhysicalNSDynamics Time initialTime integrateTo DerivativeOf
  module Weld = R354.PhysicalPackageAWeld Time initialTime integrateTo DerivativeOf

  signedIntegratedRouteBuildsPackageA :
    (T : Dyn.PhysicalNSGalerkinTrajectory) →
    Weld.R293PhysicalPackageAInputs T →
    Dyn.PhysicalNSMixedHelicitySpacetimeBudget T
  signedIntegratedRouteBuildsPackageA = Weld.r293BuildsPhysicalPackageA

  -- Deliberately no R222.PhysicalCoherentGramResidualBudget argument appears
  -- in this theorem type.
  packageAWithoutCoherentMajorantBudget :
    (T : Dyn.PhysicalNSGalerkinTrajectory) →
    Weld.R293PhysicalPackageAInputs T →
    Dyn.PhysicalNSMixedHelicitySpacetimeBudget T
  packageAWithoutCoherentMajorantBudget = signedIntegratedRouteBuildsPackageA

round373HistoricalR222TargetRemainsValidSufficientRoute : Bool
round373HistoricalR222TargetRemainsValidSufficientRoute = true

round373R222NonnegativeCoherentMajorantRequiredBySignedRoute : Bool
round373R222NonnegativeCoherentMajorantRequiredBySignedRoute = false

round373SignedIntegratedGramDebtSufficesForR293Route : Bool
round373SignedIntegratedGramDebtSufficesForR293Route = true

round373LiteralR240PackageAReachableWithoutR222Budget : Bool
round373LiteralR240PackageAReachableWithoutR222Budget = true

round373HistoricalFrontierMutated : Bool
round373HistoricalFrontierMutated = false

round373R222NonnegativeCoherentMajorantRequiredBySignedRouteIsFalse :
  round373R222NonnegativeCoherentMajorantRequiredBySignedRoute ≡ false
round373R222NonnegativeCoherentMajorantRequiredBySignedRouteIsFalse = refl

round373LiteralR240PackageAReachableWithoutR222BudgetIsTrue :
  round373LiteralR240PackageAReachableWithoutR222Budget ≡ true
round373LiteralR240PackageAReachableWithoutR222BudgetIsTrue = refl
