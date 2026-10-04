module DASHI.Physics.Closure.NSTriadKNPhysicalCriticalRegionR406HomogeneityBoundaryMaxCutExact where

------------------------------------------------------------------------
-- POSITIVE B7 / HOMOGENEITY BOUNDARY FOR THE R406 SAME-OBJECT ROUTE
--
-- The conditional B7 decomposition record asks for an equality between the
-- literal R406 weighted nonlinear remainder and four times a sum of live
-- coherent covariances.  R496--R498 identify the former with a direct
-- resolvent companion built from the nonlinear mixed-forcing bracket.
--
-- The repository's existing R289/R611 homogeneity audit separates these
-- carriers:
--
--   nonlinear mixed-forcing / direct-companion side : velocity degree 5,
--   coherent Gram / centered covariance side        : velocity degree 4.
--
-- Pair rates and rational resolvent weights are amplitude independent, so the
-- resolvent normalization does not repair the degree mismatch.
--
-- Therefore a UNIVERSAL amplitude-scale-free equality
--
--   directFibreCompanion = coherentCovarianceNumerator
--
-- is not an admissible positive-B producer.  This does not assert that the two
-- scalars can never coincide at a particular state or along a specially
-- constrained trajectory.  The valid B7 frontier is instead a trajectory-
-- specific dynamic transport or a quantitative inequality from the literal
-- R406 quintic remainder into the currency controlled by B1--B4.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)

import DASHI.Physics.Closure.NSTriadKNMixedHelicityQuarticFluxHomogeneityRound289Exact as R289
import DASHI.Physics.Closure.NSTriadKNR604AmplitudeHomogeneityNoGoRound611Exact as R611
import DASHI.Physics.Closure.NSTriadKNPhysicalCriticalRegionR406DirectCompanionMaxCutExact as Direct

b7CovarianceAmplitudeDegree : Nat
b7CovarianceAmplitudeDegree = R289.gramDebtDegree

b7DirectCompanionAmplitudeDegree : Nat
b7DirectCompanionAmplitudeDegree =
  R289.mixedForcingWorkDegree R289.nonlinearModalForcingDegree

b7CovarianceAmplitudeDegreeIsFour : b7CovarianceAmplitudeDegree ≡ 4
b7CovarianceAmplitudeDegreeIsFour = R289.gramDebtIsQuartic

b7DirectCompanionAmplitudeDegreeIsFive :
  b7DirectCompanionAmplitudeDegree ≡ 5
b7DirectCompanionAmplitudeDegreeIsFive =
  R289.nonlinearMixedForcingWorkIsQuintic

b7SidesHaveSameAmplitudeDegree : Bool
b7SidesHaveSameAmplitudeDegree = false

b7UniversalDirectCompanionCovarianceEqualityAdmissible : Bool
b7UniversalDirectCompanionCovarianceEqualityAdmissible = false

b7TrajectorySpecificEqualityMayStillHold : Bool
b7TrajectorySpecificEqualityMayStillHold = true

b7QuantitativeR406TransportMayReplaceEquality : Bool
b7QuantitativeR406TransportMayReplaceEquality = true

b7RequiresDynamicOrQuantitativeTransport : Bool
b7RequiresDynamicOrQuantitativeTransport = true

b7GlobalFiniteAggregationAlreadyClosed : Bool
b7GlobalFiniteAggregationAlreadyClosed = Direct.b7R406GlobalAggregationClosed

b7NoGoClaimsPointwiseMismatchAlwaysNonzero : Bool
b7NoGoClaimsPointwiseMismatchAlwaysNonzero = false

b7HomogeneityBoundaryAgreesWithR611 : Bool
b7HomogeneityBoundaryAgreesWithR611 =
  not R611.r604SidesHaveSameAmplitudeDegree
  where
  not : Bool → Bool
  not true = false
  not false = true

clayPromotion : Bool
clayPromotion = false

b7SidesHaveSameAmplitudeDegreeIsFalse :
  b7SidesHaveSameAmplitudeDegree ≡ false
b7SidesHaveSameAmplitudeDegreeIsFalse = refl

b7UniversalDirectCompanionCovarianceEqualityAdmissibleIsFalse :
  b7UniversalDirectCompanionCovarianceEqualityAdmissible ≡ false
b7UniversalDirectCompanionCovarianceEqualityAdmissibleIsFalse = refl

b7RequiresDynamicOrQuantitativeTransportIsTrue :
  b7RequiresDynamicOrQuantitativeTransport ≡ true
b7RequiresDynamicOrQuantitativeTransportIsTrue = refl

b7NoGoClaimsPointwiseMismatchAlwaysNonzeroIsFalse :
  b7NoGoClaimsPointwiseMismatchAlwaysNonzero ≡ false
b7NoGoClaimsPointwiseMismatchAlwaysNonzeroIsFalse = refl
