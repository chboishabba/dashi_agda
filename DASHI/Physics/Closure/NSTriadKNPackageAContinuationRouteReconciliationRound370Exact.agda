module DASHI.Physics.Closure.NSTriadKNPackageAContinuationRouteReconciliationRound370Exact where

------------------------------------------------------------------------
-- ROUND370 / BIDI: TWO DISTINCT CONTINUATION CONSUMERS OF THE SAME PACKAGE A
--
-- R365 and R369 are alternative downstream consumers of the literal R240
-- Package-A budget:
--
--   R365: Package A -> scalar critical threshold -> restart contradiction.
--   R369: Package A -> same-solution Round103 limit data -> Serrin continuation.
--
-- They share the same upstream Package-A object but do not have definitionally
-- equal physical premises or conclusions.  This owner records the fork so proof
-- search may choose the shorter consumer for the available physical producer.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Core.ProofSearchLeastPrivilegeAdmissionExact as Admission
import DASHI.Physics.Closure.NSTriadKNPackageAToRestartFrontierRound365Exact as R365
import DASHI.Physics.Closure.NSTriadKNPackageAToSameSolutionSerrinRound369Exact as R369

data PackageAContinuationRoute : Set where
  scalarRestartRoute : PackageAContinuationRoute
  sameSolutionSerrinRoute : PackageAContinuationRoute

routeDisposition : PackageAContinuationRoute → Admission.RouteDisposition
routeDisposition scalarRestartRoute = Admission.redirectedReuse
routeDisposition sameSolutionSerrinRoute = Admission.redirectedReuse

round370BothRoutesConsumeLiteralR240PackageA : Bool
round370BothRoutesConsumeLiteralR240PackageA = true

round370ScalarRestartRouteCompilerAvailable : Bool
round370ScalarRestartRouteCompilerAvailable =
  R365.round365FiniteMaximalTimeContradictionCompilerClosedConditionally

round370SameSolutionSerrinRouteCompilerAvailable : Bool
round370SameSolutionSerrinRouteCompilerAvailable =
  R369.round369SameSolutionContinuationCompilerClosedConditionally

round370SameSolutionRouteRequiresDetachedScalarThreshold : Bool
round370SameSolutionRouteRequiresDetachedScalarThreshold = false

round370RoutesHaveDefinitionallyEqualPhysicalPremises : Bool
round370RoutesHaveDefinitionallyEqualPhysicalPremises = false

round370OneRouteFailureRefutesOtherRoute : Bool
round370OneRouteFailureRefutesOtherRoute = false

round370SameSolutionRoutePreferredWhenPhysicalLimitDataAlreadyAvailable : Bool
round370SameSolutionRoutePreferredWhenPhysicalLimitDataAlreadyAvailable = true

round370SameSolutionSerrinRouteCompilerAvailableIsTrue :
  round370SameSolutionSerrinRouteCompilerAvailable ≡ true
round370SameSolutionSerrinRouteCompilerAvailableIsTrue = refl

round370SameSolutionRouteRequiresDetachedScalarThresholdIsFalse :
  round370SameSolutionRouteRequiresDetachedScalarThreshold ≡ false
round370SameSolutionRouteRequiresDetachedScalarThresholdIsFalse = refl

round370RoutesHaveDefinitionallyEqualPhysicalPremisesIsFalse :
  round370RoutesHaveDefinitionallyEqualPhysicalPremises ≡ false
round370RoutesHaveDefinitionallyEqualPhysicalPremisesIsFalse = refl
