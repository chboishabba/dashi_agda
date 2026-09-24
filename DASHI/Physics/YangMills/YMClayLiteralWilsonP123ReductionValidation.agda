{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.YMClayLiteralWilsonP123ReductionValidation where

open import Agda.Builtin.Bool using (false; true)
open import Agda.Builtin.Equality using (_≡_)

import DASHI.Physics.YangMills.YMClayLiteralWilsonP1FiniteClusteringExact as P1
import DASHI.Physics.YangMills.YMClayLiteralWilsonP2ExpectationConvergenceExact as P2
import DASHI.Physics.YangMills.YMClayLiteralWilsonP3SameOSCorrelationExact as P3
import DASHI.Physics.YangMills.YMClayLiteralWilsonRouteSThreeInputBoundaryExact as RouteS

p1NoNewClusteringInequality :
  P1.newFiniteClusteringInequalityRequiredAfterR320 ≡ false
p1NoNewClusteringInequality =
  P1.newFiniteClusteringInequalityRequiredAfterR320IsFalse

p1SelectedLocalizationRemains :
  P1.selectedR320LocalizationStillPhysical ≡ true
p1SelectedLocalizationRemains =
  P1.selectedR320LocalizationStillPhysicalIsTrue

p2ThreeLimitsAreDerived :
  P2.threeExpectationLimitsIndependentPhysicalLeaves ≡ false
p2ThreeLimitsAreDerived =
  P2.threeExpectationLimitsIndependentPhysicalLeavesIsFalse

p2WilsonPresentationRemains :
  P2.sameCarrierWilsonPresentationStillPhysical ≡ true
p2WilsonPresentationRemains =
  P2.sameCarrierWilsonPresentationStillPhysicalIsTrue

p3CorrelationIdentityIsDefinitional :
  P3.postHocCorrelationIdentityStillPhysical ≡ false
p3CorrelationIdentityIsDefinitional =
  P3.postHocCorrelationIdentityStillPhysicalIsFalse

p3SameHOSSpectrumRemains :
  P3.sameReconstructedHamiltonianSpectrumStillPhysical ≡ true
p3SameHOSSpectrumRemains =
  P3.sameReconstructedHamiltonianSpectrumStillPhysicalIsTrue

threeLeanHypothesesAreNotThreeIndependentAgdaPayments :
  RouteS.threeLeanHypothesisClassesAreThreeIndependentPhysicalTheorems ≡ false
threeLeanHypothesesAreNotThreeIndependentAgdaPayments =
  RouteS.threeLeanHypothesisClassesAreThreeIndependentPhysicalTheoremsIsFalse
