module DASHI.Physics.Closure.NSTriadKNPhysicalCriticalGalerkinSimonWeldRound104Exact where

------------------------------------------------------------------------
-- PRIMARY SOURCES / CONTEXT
--
-- Author: Jacques Simon.
-- Title: "Compact Sets in the Space L^p(0,T;B)".
-- Annali di Matematica Pura ed Applicata 146 (1987), 65--96.
-- DOI: 10.1007/BF01762360.
--
-- Author: Roger Temam.
-- Title: "Navier-Stokes Equations: Theory and Numerical Analysis".
-- DOI: 10.1090/chel/343.
--
-- Authors: Hajer Bahouri; Jean-Yves Chemin; Raphael Danchin.
-- Title: "Fourier Analysis and Nonlinear Partial Differential Equations".
-- DOI: 10.1007/978-3-642-16830-7.
--
-- ROUND104 / PHYSICAL CRITICAL GALERKIN--SIMON WELD
--
-- The repository already has a substantially more concrete Galerkin limit
-- development than the abstract Round29 target: `NSConcreteAubinLionsNonlinear-
-- LimitWitnesses` splits the standard passage into G1--G19 and constructs the
-- canonical compactness/nonlinear-limit certificate from actual witnesses.
--
-- Re-proving those layers inside the critical Clay branch would be receipt
-- shuffling.  This module therefore reuses the existing G5/G8/G9/G10/G11/G12
-- witnesses directly and isolates ONLY the genuinely stronger critical-space
-- upgrade that the old energy-level route does not provide:
--
--   L^infinity_t H^(1/2) uniformly in N,
--   L^2_t H^(3/2) uniformly in N,
--   partial_t u_N uniformly in L^(4/3)_t H^(-1/2),
--   Simon compactness strong enough in L^2_t H^(1/2),
--   weak-* lower semicontinuity of the H^(1/2) critical supremum.
--
-- Product convergence, nonlinear distributional convergence, initial trace,
-- Leray--Hopf limit identification and dissipation liminf are not requested a
-- second time: they are inherited from the concrete G-chain.
--
-- This file is a theorem-bearing reuse adapter, not a claim that the critical
-- Sobolev/Simon upgrade itself is already proved.  That upgrade remains the
-- one standard-analysis leaf after the uniform critical Galerkin barrier.
------------------------------------------------------------------------

open import Agda.Primitive using (Level; Set; lsuc; _⊔_)
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Product.Base using (_×_; _,_)

import DASHI.Physics.Closure.NSTriadKNCriticalCompactnessSerrinRound29Exact as Critical
import DASHI.Physics.Closure.NSTriadKNCriticalAubinLionsExponentWeldRound102Exact as Exponents
import DASHI.Physics.Closure.NSGalerkinCompactnessLimit as Canonical
import DASHI.Physics.Closure.NSConcreteAubinLionsNonlinearLimitWitnesses as Concrete

------------------------------------------------------------------------
-- Only the critical-topology upgrade that is absent from the existing
-- energy-level G1--G19 chain.
------------------------------------------------------------------------

record CriticalSobolevSimonUpgrade
    {ℓState ℓProp : Level}
    (S : Concrete.ConcreteGalerkinSetting ℓState ℓProp)
    (X : Concrete.ConcreteAubinLionsNonlinearLimitCertificate S)
    : Set (ℓState ⊔ ℓProp) where
  field
    UniformLInfinityHOneHalf : Set ℓProp
    uniformLInfinityHOneHalf : UniformLInfinityHOneHalf

    UniformL2HThreeHalf : Set ℓProp
    uniformL2HThreeHalf : UniformL2HThreeHalf

    UniformLFourThirdTimeDerivativeHMinusHalf : Set ℓProp
    uniformLFourThirdTimeDerivativeHMinusHalf :
      UniformLFourThirdTimeDerivativeHMinusHalf

    StrongL2HOneHalfSimonCompactness : Set ℓProp
    strongL2HOneHalfSimonCompactness : StrongL2HOneHalfSimonCompactness

    WeakStarCriticalLowerSemicontinuity : Set ℓProp
    weakStarCriticalLowerSemicontinuity : WeakStarCriticalLowerSemicontinuity

open CriticalSobolevSimonUpgrade public

------------------------------------------------------------------------
-- The old concrete chain already owns the remaining standard passage pieces.
------------------------------------------------------------------------

ExistingQuadraticLimit :
  ∀ {ℓState ℓProp}
    {S : Concrete.ConcreteGalerkinSetting ℓState ℓProp} →
  Concrete.ConcreteAubinLionsNonlinearLimitCertificate S → Set (ℓState ⊔ ℓProp)
ExistingQuadraticLimit {S = S} X =
  Concrete.G8ProductConvergence S (Concrete.g5 X)

ExistingLimitingEquation :
  ∀ {ℓState ℓProp}
    {S : Concrete.ConcreteGalerkinSetting ℓState ℓProp} →
  Concrete.ConcreteAubinLionsNonlinearLimitCertificate S → Set (ℓState ⊔ ℓProp)
ExistingLimitingEquation {S = S} X =
  Concrete.G9NonlinearTermConvergence S (Concrete.g5 X)
  × Concrete.G12LerayHopfLimit S

ExistingInitialTrace :
  ∀ {ℓState ℓProp}
    {S : Concrete.ConcreteGalerkinSetting ℓState ℓProp} →
  Concrete.ConcreteAubinLionsNonlinearLimitCertificate S → Set (ℓState ⊔ ℓProp)
ExistingInitialTrace {S = S} X = Concrete.G10InitialTraceIdentification S

ExistingDissipationLiminf :
  ∀ {ℓState ℓProp}
    {S : Concrete.ConcreteGalerkinSetting ℓState ℓProp} →
  Concrete.ConcreteAubinLionsNonlinearLimitCertificate S → Set (ℓState ⊔ ℓProp)
ExistingDissipationLiminf {S = S} X =
  Concrete.G11DissipationLowerSemicontinuity S (Concrete.g5 X)

existingQuadraticLimitWitness :
  ∀ {ℓState ℓProp}
    {S : Concrete.ConcreteGalerkinSetting ℓState ℓProp}
    (X : Concrete.ConcreteAubinLionsNonlinearLimitCertificate S) →
  ExistingQuadraticLimit X
existingQuadraticLimitWitness X = Concrete.g8 X

existingLimitingEquationWitness :
  ∀ {ℓState ℓProp}
    {S : Concrete.ConcreteGalerkinSetting ℓState ℓProp}
    (X : Concrete.ConcreteAubinLionsNonlinearLimitCertificate S) →
  ExistingLimitingEquation X
existingLimitingEquationWitness X = Concrete.g9 X , Concrete.g12 X

existingInitialTraceWitness :
  ∀ {ℓState ℓProp}
    {S : Concrete.ConcreteGalerkinSetting ℓState ℓProp}
    (X : Concrete.ConcreteAubinLionsNonlinearLimitCertificate S) →
  ExistingInitialTrace X
existingInitialTraceWitness X = Concrete.g10 X

existingDissipationLiminfWitness :
  ∀ {ℓState ℓProp}
    {S : Concrete.ConcreteGalerkinSetting ℓState ℓProp}
    (X : Concrete.ConcreteAubinLionsNonlinearLimitCertificate S) →
  ExistingDissipationLiminf X
existingDissipationLiminfWitness X = Concrete.g11 X

------------------------------------------------------------------------
-- Build the Round29 target with no duplicated product/trace/limit receipts.
--
-- The target's carrier fields are intentionally the actual cutoff index Nat
-- and the existing analytic state carrier.  The later same-solution compiler
-- must still identify that limit carrier with its continuation solution type.
------------------------------------------------------------------------

physicalCriticalGalerkinSimonWeld :
  ∀ {ℓState ℓProp : Level}
    {S : Concrete.ConcreteGalerkinSetting ℓState ℓProp} →
  (X : Concrete.ConcreteAubinLionsNonlinearLimitCertificate S) →
  CriticalSobolevSimonUpgrade S X →
  Critical.CriticalAubinLionsTarget
physicalCriticalGalerkinSimonWeld {S = S} X U = record
  { Critical.GalerkinSequence = Canonical.State (Concrete.analytic S)
  ; Critical.LimitState = Canonical.SolutionClass (Concrete.analytic S)
  ; Critical.uniformLInfinityHOneHalf = UniformLInfinityHOneHalf U
  ; Critical.uniformLInfinityHOneHalfWitness = uniformLInfinityHOneHalf U
  ; Critical.uniformL2HThreeHalf = UniformL2HThreeHalf U
  ; Critical.uniformL2HThreeHalfWitness = uniformL2HThreeHalf U
  ; Critical.uniformTimeDerivativeNegativeHalf =
      UniformLFourThirdTimeDerivativeHMinusHalf U
  ; Critical.uniformTimeDerivativeNegativeHalfWitness =
      uniformLFourThirdTimeDerivativeHMinusHalf U
  ; Critical.strongL2HOneHalfCompactness = StrongL2HOneHalfSimonCompactness U
  ; Critical.strongL2HOneHalfCompactnessWitness =
      strongL2HOneHalfSimonCompactness U
  ; Critical.quadraticTermConvergence = ExistingQuadraticLimit X
  ; Critical.quadraticTermConvergenceWitness = existingQuadraticLimitWitness X
  ; Critical.initialTraceRecovered = ExistingInitialTrace X
  ; Critical.initialTraceRecoveredWitness = existingInitialTraceWitness X
  ; Critical.limitingEquationRecovered = ExistingLimitingEquation X
  ; Critical.limitingEquationRecoveredWitness = existingLimitingEquationWitness X
  ; Critical.weakStarLowerSemicontinuity = WeakStarCriticalLowerSemicontinuity U
  ; Critical.weakStarLowerSemicontinuityWitness =
      weakStarCriticalLowerSemicontinuity U
  ; Critical.weakDissipationLowerSemicontinuity = ExistingDissipationLiminf X
  ; Critical.weakDissipationLowerSemicontinuityWitness =
      existingDissipationLiminfWitness X
  }

------------------------------------------------------------------------
-- Existing G-chain projections are genuine theorem witnesses, not booleans.
------------------------------------------------------------------------

physicalSimonWeldReusesExistingStrongL2 :
  ∀ {ℓState ℓProp : Level}
    {S : Concrete.ConcreteGalerkinSetting ℓState ℓProp}
    (X : Concrete.ConcreteAubinLionsNonlinearLimitCertificate S) →
  Canonical.StrongL2TimeSpaceConvergence
    (Concrete.analytic S)
    (Concrete.subsequence (Concrete.g5 X))
    (Canonical.LimitState (Concrete.analytic S))
physicalSimonWeldReusesExistingStrongL2 X =
  Concrete.repositoryStrongL2 (Concrete.g5 X)

physicalSimonWeldReusesExistingNonlinearLimit :
  ∀ {ℓState ℓProp : Level}
    {S : Concrete.ConcreteGalerkinSetting ℓState ℓProp}
    (X : Concrete.ConcreteAubinLionsNonlinearLimitCertificate S) →
  Canonical.NonlinearDistributionalConvergence
    (Concrete.analytic S)
    (Concrete.subsequence (Concrete.g5 X))
    (Canonical.LimitNonlinearity (Concrete.analytic S))
physicalSimonWeldReusesExistingNonlinearLimit X =
  Concrete.convectionDistribution (Concrete.g9 X)

round104ExistingG5G8G9G10G11G12LimitMachineryReused : Bool
round104ExistingG5G8G9G10G11G12LimitMachineryReused = true

round104CriticalExponentArithmeticReused : Bool
round104CriticalExponentArithmeticReused =
  Exponents.round102CriticalAubinLionsExponentArithmeticClosed

-- Remaining standard-analysis leaf: instantiate the five critical-space
-- witnesses above on the literal periodic Galerkin family.  No new nonlinear
-- dynamics should be introduced here after the uniform critical barrier exists.
round104PhysicalCriticalSobolevSimonUpgradeClosed : Bool
round104PhysicalCriticalSobolevSimonUpgradeClosed = false

round104ExistingG5G8G9G10G11G12LimitMachineryReusedIsTrue :
  round104ExistingG5G8G9G10G11G12LimitMachineryReused ≡ true
round104ExistingG5G8G9G10G11G12LimitMachineryReusedIsTrue = refl

round104PhysicalCriticalSobolevSimonUpgradeClosedIsFalse :
  round104PhysicalCriticalSobolevSimonUpgradeClosed ≡ false
round104PhysicalCriticalSobolevSimonUpgradeClosedIsFalse = refl