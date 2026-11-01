{-# OPTIONS --safe #-}
module DASHI.Physics.Closure.NSTriadKNPeriodicStandardCompletionSourcesRound649Exact where

------------------------------------------------------------------------
-- ROUND649 / STANDARD PERIODIC COMPLETION SOURCE BOUNDARY
--
-- The Clay-facing periodic max-cut should not mix source-level standard
-- analysis with the two new Navier--Stokes inequalities.
--
-- Existing downstream compilers already know how to consume:
--
--   C4: a canonical cutoff-uniform dyadic initial ceiling;
--   C6: scalar FTC + integration congruence/additivity/constant scaling;
--   C7: the three Simon/Rellich/weak-* critical facts.
--
-- This owner packages those source instances explicitly.  It proves no new
-- Fourier-series, FTC, Rellich, Simon, Banach--Alaoglu, or Navier--Stokes
-- theorem; it merely removes bookkeeping ambiguity about their consumer shape.
------------------------------------------------------------------------

open import Agda.Primitive using (lzero)
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Rational.Base using (ℚ)

import DASHI.Physics.Closure.NSIntegerFourierLattice as Z3
import DASHI.Physics.Closure.NSTriadKNComplex3ExactCarrier as C3
import DASHI.Physics.Closure.NSTriadKNRationalOrderedFiniteL2 as Rational
import DASHI.Physics.Closure.NSTriadKNCanonicalInitialCriticalCeilingRound644Exact as R644
import DASHI.Physics.Closure.NSTriadKNSelfFluxScalarFTCBoundaryRound564Exact as R564
import DASHI.Physics.Closure.NSTriadKNLiteralCriticalEnergyCalculusExact as Energy
import DASHI.Physics.Closure.NSTriadKNPhysicalCriticalGalerkinSimonWeldRound104Exact as R104
import DASHI.Physics.Closure.NSTriadKNCriticalSimonUpgradeFollowsBarrierRound148Exact as R148
import DASHI.Physics.Closure.NSTriadKNCriticalCompactnessSerrinRound29Exact as Critical
import DASHI.Physics.Closure.NSConcreteAubinLionsNonlinearLimitWitnesses as Concrete

F : C3.RealField _
F = Rational.rationalRealField

------------------------------------------------------------------------
-- C4 source boundary.
------------------------------------------------------------------------

record StandardInitialCriticalSource
    (initial : Z3.FourierMode → C3.Complex3 F) : Set where
  field
    canonicalDyadicInitialCeiling :
      R644.CanonicalDyadicInitialCeiling initial

open StandardInitialCriticalSource public

------------------------------------------------------------------------
-- C6 source boundary.
------------------------------------------------------------------------

record StandardScalarCalculusSource
    (Time : Set)
    (initialTime : Time)
    (integrateTo : (Time → ℚ) → Time → ℚ)
    (ScalarDerivativeOf : (Time → ℚ) → (Time → ℚ) → Set) : Set₁ where
  field
    scalarFTC :
      R564.ScalarFundamentalTheorem564
        Time initialTime integrateTo ScalarDerivativeOf

    scalarIntegrationLinearity :
      Energy.ScalarIntegrationLinearity Time integrateTo

open StandardScalarCalculusSource public

------------------------------------------------------------------------
-- C7 source boundary.
------------------------------------------------------------------------

ConcreteSetting : Set₁
ConcreteSetting = Concrete.ConcreteGalerkinSetting lzero lzero

record StandardCriticalCompactnessSource
    (S : ConcreteSetting)
    (X : Concrete.ConcreteAubinLionsNonlinearLimitCertificate S)
    (barrier : R104.CriticalBarrierTopology S X) : Set₁ where
  field
    criticalSimonFacts :
      R148.StandardCriticalSimonFacts S X barrier

open StandardCriticalCompactnessSource public

standardCompactnessSourceBuildsCriticalTarget :
  {S : ConcreteSetting}
  (X : Concrete.ConcreteAubinLionsNonlinearLimitCertificate S)
  (barrier : R104.CriticalBarrierTopology S X) →
  StandardCriticalCompactnessSource S X barrier →
  Critical.CriticalAubinLionsTarget
standardCompactnessSourceBuildsCriticalTarget X barrier source =
  R148.standardFactsGivePhysicalCriticalLimit
    X barrier (criticalSimonFacts source)

------------------------------------------------------------------------
-- Status / max-cut classification.
------------------------------------------------------------------------

round649C4StandardSourceInterfaceComplete : Bool
round649C4StandardSourceInterfaceComplete = true

round649C6StandardSourceInterfaceComplete : Bool
round649C6StandardSourceInterfaceComplete = true

round649C7StandardSourceInterfaceComplete : Bool
round649C7StandardSourceInterfaceComplete = true

round649AllStandardConsumersHaveTypedSourceBoundary : Bool
round649AllStandardConsumersHaveTypedSourceBoundary = true

round649StandardTheoremsProvedInternally : Bool
round649StandardTheoremsProvedInternally = false

round649IntroducesNewNSEstimate : Bool
round649IntroducesNewNSEstimate = false

round649ClayPromotion : Bool
round649ClayPromotion = false

round649C4StandardSourceInterfaceCompleteIsTrue :
  round649C4StandardSourceInterfaceComplete ≡ true
round649C4StandardSourceInterfaceCompleteIsTrue = refl

round649C6StandardSourceInterfaceCompleteIsTrue :
  round649C6StandardSourceInterfaceComplete ≡ true
round649C6StandardSourceInterfaceCompleteIsTrue = refl

round649C7StandardSourceInterfaceCompleteIsTrue :
  round649C7StandardSourceInterfaceComplete ≡ true
round649C7StandardSourceInterfaceCompleteIsTrue = refl

round649AllStandardConsumersHaveTypedSourceBoundaryIsTrue :
  round649AllStandardConsumersHaveTypedSourceBoundary ≡ true
round649AllStandardConsumersHaveTypedSourceBoundaryIsTrue = refl

round649StandardTheoremsProvedInternallyIsFalse :
  round649StandardTheoremsProvedInternally ≡ false
round649StandardTheoremsProvedInternallyIsFalse = refl

round649IntroducesNewNSEstimateIsFalse :
  round649IntroducesNewNSEstimate ≡ false
round649IntroducesNewNSEstimateIsFalse = refl

round649ClayPromotionIsFalse :
  round649ClayPromotion ≡ false
round649ClayPromotionIsFalse = refl
