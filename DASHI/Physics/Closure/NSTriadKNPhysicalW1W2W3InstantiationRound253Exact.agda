module DASHI.Physics.Closure.NSTriadKNPhysicalW1W2W3InstantiationRound253Exact where

------------------------------------------------------------------------
-- ROUND253 / PHYSICAL ANALYTIC INSTANTIATION SURFACE FOR W1 + W2 + W3
--
-- BIDI PURPOSE
-- Backward: Round252 needs exactly one periodic Sobolev/Hölder object, one
-- canonical-G2 same-physical dissipation object, one spacetime passage, and
-- one finite-dimensional first-hit law.
-- Forward: those four objects come from the same periodic Galerkin trajectory.
--
-- This file does not duplicate any theorem.  It packages the exact analytic
-- instances required by R249--R252 and makes same-family provenance explicit.
------------------------------------------------------------------------

open import Agda.Primitive using (Level; _⊔_)
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Data.Rational.Base using (ℚ)

import DASHI.Physics.Closure.NSConcreteAubinLionsNonlinearLimitWitnesses as Concrete
import DASHI.Physics.Closure.NSTriadKNCanonicalG2Round240W2Round250Exact as R250
import DASHI.Physics.Closure.NSTriadKNStandardPeriodicSobolevW1Round249Exact as R249
import DASHI.Physics.Closure.NSTriadKNStandardSpacetimeW1AndFirstHitW3Round251Exact as R251

record PhysicalW1W2W3Instances
    {ℓState ℓProp : Level}
    (S : Concrete.ConcreteGalerkinSetting ℓState ℓProp)
    (G2 : Concrete.G2ExactGalerkinEnergy S)
    (Time : Set)
    (integrateTo : (Time → ℚ) → Time → ℚ)
    (mixedMass criticalSize dissipationDensity : Nat → Time → ℚ)
    (Before : Time → Time → Set)
    (threshold : ℚ)
    : Set (ℓState ⊔ ℓProp) where
  field
    w1Pointwise :
      R249.StandardPeriodicW1Authority
        Time mixedMass criticalSize dissipationDensity

    w1Spacetime :
      R251.StandardSpacetimeW1Authority
        Time integrateTo mixedMass criticalSize dissipationDensity w1Pointwise

    w2Canonical :
      R250.CanonicalG2SamePhysicalW2
        S G2 Time (R251.integratedDissipation w1Spacetime)

    w3FirstHit :
      R251.FiniteDimensionalFirstHitAuthority
        Time Before criticalSize threshold

open PhysicalW1W2W3Instances public

round253W1W2W3SameAnalyticFamilyUnified : Bool
round253W1W2W3SameAnalyticFamilyUnified = true

round253NoParallelEnergyOrTrajectoryIntroduced : Bool
round253NoParallelEnergyOrTrajectoryIntroduced = true

round253ExternalPeriodicAnalysisKernelDerivedHere : Bool
round253ExternalPeriodicAnalysisKernelDerivedHere = false

round253PackageAClosed : Bool
round253PackageAClosed = false

round253W1W2W3SameAnalyticFamilyUnifiedIsTrue :
  round253W1W2W3SameAnalyticFamilyUnified ≡ true
round253W1W2W3SameAnalyticFamilyUnifiedIsTrue = refl

round253ExternalPeriodicAnalysisKernelDerivedHereIsFalse :
  round253ExternalPeriodicAnalysisKernelDerivedHere ≡ false
round253ExternalPeriodicAnalysisKernelDerivedHereIsFalse = refl
