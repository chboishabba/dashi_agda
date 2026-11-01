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
-- The repository already has a concrete G1--G19 Galerkin limit chain.  This
-- module reuses G5/G8/G9/G10/G11/G12 rather than requesting duplicate
-- compactness/product/trace/limit receipts.
--
-- One further dependency correction matters.  The uniform
--
--   L^infinity_t H^(1/2),   L^2_t H^(3/2)
--
-- estimates are not additional Simon lemmas: they are exactly the topology
-- realization of the uniform critical Galerkin barrier produced by obligation
-- A.  They are therefore carried separately as `CriticalBarrierTopology`.
--
-- Once that barrier topology exists, the genuinely additional standard-
-- analysis upgrade has only THREE components:
--
--   1. partial_t u_N uniformly in L^(4/3)_t H^(-1/2);
--   2. Simon compactness strong enough in L^2_t H^(1/2);
--   3. weak-* lower semicontinuity of the H^(1/2) critical supremum.
--
-- Product convergence, nonlinear distributional convergence, initial trace,
-- Leray--Hopf limit identification and dissipation liminf are inherited from
-- the existing concrete G-chain.  The actual Round29 limiting element is the
-- G12 Leray--Hopf solution itself.
------------------------------------------------------------------------

open import Agda.Primitive using (lzero)
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Data.Product.Base using (_×_; _,_)

import DASHI.Physics.Closure.NSTriadKNCriticalCompactnessSerrinRound29Exact as Critical
import DASHI.Physics.Closure.NSTriadKNCriticalAubinLionsExponentWeldRound102Exact as Exponents
import DASHI.Physics.Closure.NSGalerkinCompactnessLimit as Canonical
import DASHI.Physics.Closure.NSConcreteAubinLionsNonlinearLimitWitnesses as Concrete

ConcreteSetting : Set₁
ConcreteSetting = Concrete.ConcreteGalerkinSetting lzero lzero

------------------------------------------------------------------------
-- Output topology of obligation A: not counted again as Simon work.
------------------------------------------------------------------------

record CriticalBarrierTopology
    (S : ConcreteSetting)
    (X : Concrete.ConcreteAubinLionsNonlinearLimitCertificate S) : Set where
  field
    UniformLInfinityHOneHalf : Set
    uniformLInfinityHOneHalf : UniformLInfinityHOneHalf

    UniformL2HThreeHalf : Set
    uniformL2HThreeHalf : UniformL2HThreeHalf

open CriticalBarrierTopology public

------------------------------------------------------------------------
-- Only the genuinely additional standard-analysis upgrade.
------------------------------------------------------------------------

record CriticalSobolevSimonUpgrade
    (S : ConcreteSetting)
    (X : Concrete.ConcreteAubinLionsNonlinearLimitCertificate S)
    (barrier : CriticalBarrierTopology S X) : Set where
  field
    UniformLFourThirdTimeDerivativeHMinusHalf : Set
    uniformLFourThirdTimeDerivativeHMinusHalf :
      UniformLFourThirdTimeDerivativeHMinusHalf

    StrongL2HOneHalfSimonCompactness : Set
    strongL2HOneHalfSimonCompactness : StrongL2HOneHalfSimonCompactness

    WeakStarCriticalLowerSemicontinuity : Set
    weakStarCriticalLowerSemicontinuity : WeakStarCriticalLowerSemicontinuity

open CriticalSobolevSimonUpgrade public

ExistingQuadraticLimit :
  {S : ConcreteSetting} →
  Concrete.ConcreteAubinLionsNonlinearLimitCertificate S → Set
ExistingQuadraticLimit {S = S} X =
  Concrete.G8ProductConvergence S (Concrete.g5 X)

ExistingLimitingEquation :
  {S : ConcreteSetting} →
  Concrete.ConcreteAubinLionsNonlinearLimitCertificate S → Set
ExistingLimitingEquation {S = S} X =
  Concrete.G9NonlinearTermConvergence S (Concrete.g5 X)
  × Concrete.G12LerayHopfLimit S

ExistingInitialTrace :
  {S : ConcreteSetting} →
  Concrete.ConcreteAubinLionsNonlinearLimitCertificate S → Set
ExistingInitialTrace {S = S} X = Concrete.G10InitialTraceIdentification S

ExistingDissipationLiminf :
  {S : ConcreteSetting} →
  Concrete.ConcreteAubinLionsNonlinearLimitCertificate S → Set
ExistingDissipationLiminf {S = S} X =
  Concrete.G11DissipationLowerSemicontinuity S (Concrete.g5 X)

existingQuadraticLimitWitness :
  {S : ConcreteSetting}
  (X : Concrete.ConcreteAubinLionsNonlinearLimitCertificate S) →
  ExistingQuadraticLimit X
existingQuadraticLimitWitness X = Concrete.g8 X

existingLimitingEquationWitness :
  {S : ConcreteSetting}
  (X : Concrete.ConcreteAubinLionsNonlinearLimitCertificate S) →
  ExistingLimitingEquation X
existingLimitingEquationWitness X = Concrete.g9 X , Concrete.g12 X

existingInitialTraceWitness :
  {S : ConcreteSetting}
  (X : Concrete.ConcreteAubinLionsNonlinearLimitCertificate S) →
  ExistingInitialTrace X
existingInitialTraceWitness X = Concrete.g10 X

existingDissipationLiminfWitness :
  {S : ConcreteSetting}
  (X : Concrete.ConcreteAubinLionsNonlinearLimitCertificate S) →
  ExistingDissipationLiminf X
existingDissipationLiminfWitness X = Concrete.g11 X

physicalCriticalGalerkinSimonWeld :
  {S : ConcreteSetting} →
  (X : Concrete.ConcreteAubinLionsNonlinearLimitCertificate S) →
  (barrier : CriticalBarrierTopology S X) →
  CriticalSobolevSimonUpgrade S X barrier →
  Critical.CriticalAubinLionsTarget
physicalCriticalGalerkinSimonWeld {S = S} X barrier U = record
  { Critical.GalerkinSequence = Nat
  ; Critical.LimitState = Canonical.SolutionClass (Concrete.analytic S)
  ; Critical.limitingState = Concrete.solution (Concrete.g12 X)
  ; Critical.uniformLInfinityHOneHalf = UniformLInfinityHOneHalf barrier
  ; Critical.uniformLInfinityHOneHalfWitness = uniformLInfinityHOneHalf barrier
  ; Critical.uniformL2HThreeHalf = UniformL2HThreeHalf barrier
  ; Critical.uniformL2HThreeHalfWitness = uniformL2HThreeHalf barrier
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

physicalSimonWeldReusesExistingStrongL2 :
  {S : ConcreteSetting}
  (X : Concrete.ConcreteAubinLionsNonlinearLimitCertificate S) →
  Canonical.StrongL2TimeSpaceConvergence
    (Concrete.analytic S)
    (Concrete.subsequence (Concrete.g5 X))
    (Canonical.LimitState (Concrete.analytic S))
physicalSimonWeldReusesExistingStrongL2 X =
  Concrete.repositoryStrongL2 (Concrete.g5 X)

physicalSimonWeldReusesExistingNonlinearLimit :
  {S : ConcreteSetting}
  (X : Concrete.ConcreteAubinLionsNonlinearLimitCertificate S) →
  Canonical.NonlinearDistributionalConvergence
    (Concrete.analytic S)
    (Concrete.subsequence (Concrete.g5 X))
    (Canonical.LimitNonlinearity (Concrete.analytic S))
physicalSimonWeldReusesExistingNonlinearLimit X =
  Concrete.convectionDistribution (Concrete.g9 X)

physicalSimonWeldReusesExistingDissipationLiminf :
  {S : ConcreteSetting}
  (X : Concrete.ConcreteAubinLionsNonlinearLimitCertificate S) →
  Canonical.DissipationLowerSemicontinuity
    (Concrete.analytic S)
    (Concrete.subsequence (Concrete.g5 X))
physicalSimonWeldReusesExistingDissipationLiminf X =
  Concrete.repositoryLiminf (Concrete.g11 X)

round104BarrierTopologyBelongsToUniformCriticalBarrier : Bool
round104BarrierTopologyBelongsToUniformCriticalBarrier = true

round104ExistingG5G8G9G10G11G12LimitMachineryReused : Bool
round104ExistingG5G8G9G10G11G12LimitMachineryReused = true

round104CriticalExponentArithmeticReused : Bool
round104CriticalExponentArithmeticReused =
  Exponents.round102CriticalAubinLionsExponentArithmeticClosed

round104PhysicalCriticalSobolevSimonUpgradeClosed : Bool
round104PhysicalCriticalSobolevSimonUpgradeClosed = false

round104BarrierTopologyBelongsToUniformCriticalBarrierIsTrue :
  round104BarrierTopologyBelongsToUniformCriticalBarrier ≡ true
round104BarrierTopologyBelongsToUniformCriticalBarrierIsTrue = refl

round104ExistingG5G8G9G10G11G12LimitMachineryReusedIsTrue :
  round104ExistingG5G8G9G10G11G12LimitMachineryReused ≡ true
round104ExistingG5G8G9G10G11G12LimitMachineryReusedIsTrue = refl

round104PhysicalCriticalSobolevSimonUpgradeClosedIsFalse :
  round104PhysicalCriticalSobolevSimonUpgradeClosed ≡ false
round104PhysicalCriticalSobolevSimonUpgradeClosedIsFalse = refl