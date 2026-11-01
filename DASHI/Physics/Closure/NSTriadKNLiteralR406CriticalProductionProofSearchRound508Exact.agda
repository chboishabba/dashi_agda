module DASHI.Physics.Closure.NSTriadKNLiteralR406CriticalProductionProofSearchRound508Exact where

------------------------------------------------------------------------
-- ROUND508 / SHARPEN THE SECOND R504 TERMINAL LEAF
--
-- R507 proves that R414's literal-R406 critical slice is not a new analytic
-- seven-tuple: an existing Round104 signed-critical slice plus ONE equality of
-- its remainder with the literal R406 remainder integral compiles directly.
--
-- The physical Round104 constructors (R105 and the later R108 audit) still
-- leave the genuine signed physical forcing payment open.  R108 sharpens that
-- analytic object further by extracting the exact self Waleffe term and leaving
-- only the external cross-triad signed forcing remainder payment.
--
-- Hence the second R504 leaf should be searched in this order:
--
--   1. physical signed critical / external cross-triad forcing payment;
--   2. Round104 slice construction (compiler work, already available);
--   3. exact Round104 remainder = literal R406 integral weld;
--   4. R507 -> R414 literal-R406 critical slice.
--
-- The Inage residence-time comparator is not permitted to skip step 1 merely
-- from a low-drift-band statement; R506 records that variation authority is a
-- distinct capability.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Core.ProofSearchLeastPrivilegeAdmissionExact as Least
import DASHI.Physics.Closure.NSTriadKNLiteralR406ClayTerminalCutsetRound504Exact as R504
import DASHI.Physics.Closure.NSTriadKNResidenceBandVariationNoGoRound506Exact as R506
import DASHI.Physics.Closure.NSTriadKNRound104ToLiteralR406CriticalSliceRound507Exact as R507
import DASHI.Physics.Closure.NSTriadKNUniformGalerkinSignedCriticalProductionRound104Exact as R104
import DASHI.Physics.Closure.NSTriadKNGlobalSignedDangerToCriticalRound105Exact as R105
import DASHI.Physics.Closure.NSTriadKNWaleffeForcingRouteAuditRound108Exact as R108

data CriticalProductionResidual : Set where
  missingPhysicalSignedCriticalPayment : CriticalProductionResidual
  missingLiteralR406RemainderWeld : CriticalProductionResidual
  criticalProductionLeafClosed : CriticalProductionResidual

record CriticalProductionStatus : Set where
  constructor critical-production-status
  field
    physicalSignedCriticalPaymentPresent : Bool
    literalR406RemainderWeldPresent : Bool

open CriticalProductionStatus public

firstCriticalProductionResidual :
  CriticalProductionStatus → CriticalProductionResidual
firstCriticalProductionResidual (critical-production-status false weld) =
  missingPhysicalSignedCriticalPayment
firstCriticalProductionResidual (critical-production-status true false) =
  missingLiteralR406RemainderWeld
firstCriticalProductionResidual (critical-production-status true true) =
  criticalProductionLeafClosed

currentCriticalProductionStatus : CriticalProductionStatus
currentCriticalProductionStatus = critical-production-status false false

currentCriticalProductionResidual :
  firstCriticalProductionResidual currentCriticalProductionStatus
  ≡ missingPhysicalSignedCriticalPayment
currentCriticalProductionResidual = refl

externalCrossTriadForcingRoute : Least.RouteDisposition
externalCrossTriadForcingRoute = Least.admitted

lowDriftBandAloneAsPaymentRoute : Least.RouteDisposition
lowDriftBandAloneAsPaymentRoute = Least.rejected Least.hypothesisInflation

round104CompilerRoute : Least.RouteDisposition
round104CompilerRoute = Least.redirectedReuse

r406RemainderWeldRoute : Least.RouteDisposition
r406RemainderWeldRoute = Least.admitted

round508R504SecondLeafStillOpen : Bool
round508R504SecondLeafStillOpen =
  R504.round504CriticalProductionSliceClosed

round508Round104PhysicalSignedCriticalProductionClosed : Bool
round508Round104PhysicalSignedCriticalProductionClosed =
  R104.round104PhysicalUniformSignedCriticalProductionClosed

round508R105PhysicalGlobalCriticalDangerBoundClosed : Bool
round508R105PhysicalGlobalCriticalDangerBoundClosed =
  R105.round105PhysicalGlobalCriticalDangerBoundClosed

round508R108ExternalCrossTriadForcingPaymentClosed : Bool
round508R108ExternalCrossTriadForcingPaymentClosed =
  R108.round108PhysicalExternalCrossTriadForcingRemainderPaymentClosed

round508R507RemainderWeldClosed : Bool
round508R507RemainderWeldClosed =
  R507.round507LiteralR406RemainderSameObjectWeldClosed

round508LowDriftBandCreatesVariationAuthority : Bool
round508LowDriftBandCreatesVariationAuthority =
  R506.round506LowDriftBandAloneCreatesVariationAuthority

round508ClayPromotion : Bool
round508ClayPromotion = false

round508R504SecondLeafStillOpenIsFalse :
  round508R504SecondLeafStillOpen ≡ false
round508R504SecondLeafStillOpenIsFalse = refl

round508Round104PhysicalSignedCriticalProductionClosedIsFalse :
  round508Round104PhysicalSignedCriticalProductionClosed ≡ false
round508Round104PhysicalSignedCriticalProductionClosedIsFalse =
  R104.round104PhysicalUniformSignedCriticalProductionClosedIsFalse

round508R105PhysicalGlobalCriticalDangerBoundClosedIsFalse :
  round508R105PhysicalGlobalCriticalDangerBoundClosed ≡ false
round508R105PhysicalGlobalCriticalDangerBoundClosedIsFalse =
  R105.round105PhysicalGlobalCriticalDangerBoundClosedIsFalse

round508R108ExternalCrossTriadForcingPaymentClosedIsFalse :
  round508R108ExternalCrossTriadForcingPaymentClosed ≡ false
round508R108ExternalCrossTriadForcingPaymentClosedIsFalse =
  R108.round108PhysicalExternalCrossTriadForcingRemainderPaymentClosedIsFalse

round508R507RemainderWeldClosedIsFalse :
  round508R507RemainderWeldClosed ≡ false
round508R507RemainderWeldClosedIsFalse =
  R507.round507LiteralR406RemainderSameObjectWeldClosedIsFalse

round508LowDriftBandCreatesVariationAuthorityIsFalse :
  round508LowDriftBandCreatesVariationAuthority ≡ false
round508LowDriftBandCreatesVariationAuthorityIsFalse =
  R506.round506LowDriftBandAloneCreatesVariationAuthorityIsFalse

round508ClayPromotionIsFalse : round508ClayPromotion ≡ false
round508ClayPromotionIsFalse = refl
