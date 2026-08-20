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
-- Leray--Hopf limit identification and dissipation liminf are inherited from
-- the concrete G-chain.
--
-- Round29's legacy target stores ordinary `Set` fields, so this adapter is
-- deliberately specialized to the repository's concrete lzero/lzero physical
-- setting.  That is a type-correct API boundary, not a mathematical loss.
------------------------------------------------------------------------

open import Agda.Primitive using (lzero; Set; Set₁)
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
-- Only the critical-topology upgrade absent from the energy-level G1--G19
-- chain.  Every named proposition is accompanied by an inhabitant.
------------------------------------------------------------------------

record CriticalSobolevSimonUpgrade
    (S : ConcreteSetting)
    (X : Concrete.ConcreteAubinLionsNonlinearLimitCertificate S) : Set where
  field
    UniformLInfinityHOneHalf : Set
    uniformLInfinityHOneHalf : UniformLInfinityHOneHalf

    UniformL2HThreeHalf : Set
    uniformL2HThreeHalf : UniformL2HThreeHalf

    UniformLFourThirdTimeDerivativeHMinusHalf : Set
    uniformLFourThirdTimeDerivativeHMinusHalf :
      UniformLFourThirdTimeDerivativeHMinusHalf

    StrongL2HOneHalfSimonCompactness : Set
    strongL2HOneHalfSimonCompactness : StrongL2HOneHalfSimonCompactness

    WeakStarCriticalLowerSemicontinuity : Set
    weakStarCriticalLowerSemicontinuity : WeakStarCriticalLowerSemicontinuity

open CriticalSobolevSimonUpgrade public

------------------------------------------------------------------------
-- Existing concrete G-chain witnesses reused directly.
------------------------------------------------------------------------

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

------------------------------------------------------------------------
-- Build Round29's witness-bearing target.  Nat is the literal Galerkin cutoff
-- index carrier; the limit carrier is the existing analytic SolutionClass.
------------------------------------------------------------------------

physicalCriticalGalerkinSimonWeld :
  {S : ConcreteSetting} →
  (X : Concrete.ConcreteAubinLionsNonlinearLimitCertificate S) →
  CriticalSobolevSimonUpgrade S X →
  Critical.CriticalAubinLionsTarget
physicalCriticalGalerkinSimonWeld {S = S} X U = record
  { Critical.GalerkinSequence = Nat
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
-- Actual theorem witnesses exported from the old G-chain.
------------------------------------------------------------------------

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

round104ExistingG5G8G9G10G11G12LimitMachineryReused : Bool
round104ExistingG5G8G9G10G11G12LimitMachineryReused = true

round104CriticalExponentArithmeticReused : Bool
round104CriticalExponentArithmeticReused =
  Exponents.round102CriticalAubinLionsExponentArithmeticClosed

-- Remaining standard-analysis leaf: instantiate these five critical-space
-- witnesses on the literal periodic Galerkin family.  No new nonlinear
-- dynamics should be introduced here after the uniform critical barrier.
round104PhysicalCriticalSobolevSimonUpgradeClosed : Bool
round104PhysicalCriticalSobolevSimonUpgradeClosed = false

round104ExistingG5G8G9G10G11G12LimitMachineryReusedIsTrue :
  round104ExistingG5G8G9G10G11G12LimitMachineryReused ≡ true
round104ExistingG5G8G9G10G11G12LimitMachineryReusedIsTrue = refl

round104PhysicalCriticalSobolevSimonUpgradeClosedIsFalse :
  round104PhysicalCriticalSobolevSimonUpgradeClosed ≡ false
round104PhysicalCriticalSobolevSimonUpgradeClosedIsFalse = refl