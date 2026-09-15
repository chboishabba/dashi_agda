module DASHI.Physics.Closure.NSTriadKNLiteralFiniteCriticalObservableFoldExact where

------------------------------------------------------------------------
-- STRICT B-PHASE S0 / LITERAL FINITE CRITICAL-OBSERVABLE FOLD
--
-- Purpose
-- -------
-- R515 correctly observed that an R414 slice indexed by a physical trajectory
-- still contains free rational coordinates. R516/R517 subsequently closed the
-- finite-carrier critical radial / dyadic-equivalence seam, but did not install
-- those coordinates on the live R240 trajectory.
--
-- This owner does the first concrete part of that job. From the SAME finite
-- Galerkin system at (N,t) it computes, without caller-supplied scalar aliases:
--
--   X_N(t)   -- dyadic critical endpoint mass;
--   D_N(T)   -- integrated dyadic 3/2 dissipation mass;
--   N_N(T)   -- integrated dyadic critical real-Hermitian pairing of u_N with
--               the literal Audit.projectedNonlinearity.
--
-- The nonlinear production is NOT defined by rearranging an energy identity.
-- Hence the later critical-energy identity remains a genuine theorem rather
-- than becoming true by definition.
--
-- Scalar / physical-norm boundary
-- -------------------------------
-- R414 is a rational finite algebra surface. The selected dyadic weights below
-- therefore stay in Q so that R240's existing integrateTo : (Time -> Q) -> ...
-- can be reused literally. R517 owns the theorem-backed finite-carrier bridge
-- between the dyadic critical multiplier route and physical H^(1/2)/H^(3/2)
-- multipliers. This file reuses that route as the critical-norm authority; it
-- does NOT claim that its rational dyadic weight is definitionally the Bishop
-- real physical multiplier.
--
-- Geometry is deliberately generic in the exact integer embedding E and
-- inverse-square witness I carried by the finite system. The live R240 state
-- therefore supplies its own same-object Fourier geometry; no invented
-- "rationalIntegerEmbedding" alias is introduced here.
--
-- Remaining strict leaves after this owner:
--   S1  critical energy identity / exact production normalisation;
--   S2  signed-production estimate by the literal R406 remainder;
--   S3  cutoff-uniform initial-critical ceiling;
--   S4  positive retained viscosity.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Agda.Builtin.List using (List; []; _∷_)
open import Data.Rational.Base using (ℚ; 0ℚ; 1ℚ; _+_; _*_)

import DASHI.Physics.Closure.NSIntegerFourierLattice as Z3
import DASHI.Physics.Closure.NSTriadKNComplex3ExactCarrier as C3
import DASHI.Physics.Closure.NSTriadKNOrderedEuclideanL2Carrier as L2
import DASHI.Physics.Closure.NSTriadKNRationalOrderedFiniteL2 as Rational
import DASHI.Physics.Closure.NSTriadKNComplex3GalerkinEquationAudit as Audit
import DASHI.Physics.Closure.NSTriadKNPhysicalNSGalerkinTrajectoryRound240Exact as R240
import DASHI.Physics.Closure.NSTriadKNLiteralDyadicShellConstants as Shell
import DASHI.Physics.Closure.NSTriadKNDyadicCriticalNormEquivalenceBoundaryRound517Exact as R517

F : C3.RealField _
F = Rational.rationalRealField

------------------------------------------------------------------------
-- Exact rational dyadic weights.
------------------------------------------------------------------------

natAsRational : Nat → ℚ
natAsRational zero = 0ℚ
natAsRational (suc n) = 1ℚ + natAsRational n

dyadicCriticalWeight : Z3.FourierMode → ℚ
dyadicCriticalWeight mode =
  natAsRational (Shell.pow2 (Shell.shellIndex mode))

cube : ℚ → ℚ
cube value = value * value * value

dyadicCriticalThreeHalfWeight : Z3.FourierMode → ℚ
dyadicCriticalThreeHalfWeight mode = cube (dyadicCriticalWeight mode)

------------------------------------------------------------------------
-- Literal finite state folds, generic in the SAME E/I geometry carried by the
-- finite system.
------------------------------------------------------------------------

weightedVelocityMass :
  ∀ {E : C3.IntegerEmbedding F}
    {I : C3.ModeInverseSquare F E} →
  (Z3.FourierMode → ℚ) →
  Audit.FiniteComplex3GalerkinSystem F E I →
  List Z3.FourierMode →
  ℚ
weightedVelocityMass weight system [] = 0ℚ
weightedVelocityMass weight system (mode ∷ rest) =
  weight mode * L2.complex3NormSquared (Audit.velocity system mode)
    + weightedVelocityMass weight system rest

criticalEndpointMass :
  ∀ {E : C3.IntegerEmbedding F}
    {I : C3.ModeInverseSquare F E} →
  Audit.FiniteComplex3GalerkinSystem F E I →
  ℚ
criticalEndpointMass system =
  weightedVelocityMass dyadicCriticalWeight system (Audit.modes system)

criticalDissipationRate :
  ∀ {E : C3.IntegerEmbedding F}
    {I : C3.ModeInverseSquare F E} →
  Audit.FiniteComplex3GalerkinSystem F E I →
  ℚ
criticalDissipationRate system =
  weightedVelocityMass
    dyadicCriticalThreeHalfWeight system (Audit.modes system)

realHermitianPairing :
  C3.Complex3 F → C3.Complex3 F → ℚ
realHermitianPairing left right =
  C3.real (C3.hermitianPairing3 left right)

weightedProjectedNonlinearProduction :
  ∀ {E : C3.IntegerEmbedding F}
    {I : C3.ModeInverseSquare F E} →
  Audit.FiniteComplex3GalerkinSystem F E I →
  List Z3.FourierMode →
  ℚ
weightedProjectedNonlinearProduction system [] = 0ℚ
weightedProjectedNonlinearProduction system (mode ∷ rest) =
  dyadicCriticalWeight mode
    * realHermitianPairing
        (Audit.velocity system mode)
        (Audit.projectedNonlinearity system mode)
    + weightedProjectedNonlinearProduction system rest

criticalProductionRate :
  ∀ {E : C3.IntegerEmbedding F}
    {I : C3.ModeInverseSquare F E} →
  Audit.FiniteComplex3GalerkinSystem F E I →
  ℚ
criticalProductionRate system =
  weightedProjectedNonlinearProduction system (Audit.modes system)

------------------------------------------------------------------------
-- Same-trajectory spacetime specialization.
------------------------------------------------------------------------

module LiteralCriticalObservables
    (Time : Set)
    (initialTime : Time)
    (integrateTo : (Time → ℚ) → Time → ℚ)
    (DerivativeOf :
      (Time → C3.Complex3 F) →
      (Time → C3.Complex3 F) → Set) where

  module Dyn = R240.PhysicalNSDynamics Time initialTime integrateTo DerivativeOf

  criticalEnergyAt :
    Dyn.PhysicalNSGalerkinTrajectory → Nat → Time → ℚ
  criticalEnergyAt trajectory cutoff time =
    criticalEndpointMass
      (Dyn.Base.systemAt (Dyn.forgetDynamics trajectory) cutoff time)

  dissipationRateAt :
    Dyn.PhysicalNSGalerkinTrajectory → Nat → Time → ℚ
  dissipationRateAt trajectory cutoff time =
    criticalDissipationRate
      (Dyn.Base.systemAt (Dyn.forgetDynamics trajectory) cutoff time)

  productionRateAt :
    Dyn.PhysicalNSGalerkinTrajectory → Nat → Time → ℚ
  productionRateAt trajectory cutoff time =
    criticalProductionRate
      (Dyn.Base.systemAt (Dyn.forgetDynamics trajectory) cutoff time)

  integratedCriticalDissipation :
    Dyn.PhysicalNSGalerkinTrajectory → Nat → Time → ℚ
  integratedCriticalDissipation trajectory cutoff terminal =
    integrateTo (dissipationRateAt trajectory cutoff) terminal

  integratedCriticalProduction :
    Dyn.PhysicalNSGalerkinTrajectory → Nat → Time → ℚ
  integratedCriticalProduction trajectory cutoff terminal =
    integrateTo (productionRateAt trajectory cutoff) terminal

  record LiteralFiniteCriticalObservables
      (trajectory : Dyn.PhysicalNSGalerkinTrajectory)
      (cutoff : Nat)
      (terminal : Time) : Set where
    constructor literal-finite-critical-observables
    field
      initialCritical : ℚ
      terminalCritical : ℚ
      criticalDissipation : ℚ
      integratedSignedProduction : ℚ

      initialCriticalMeaning :
        initialCritical ≡ criticalEnergyAt trajectory cutoff initialTime
      terminalCriticalMeaning :
        terminalCritical ≡ criticalEnergyAt trajectory cutoff terminal
      criticalDissipationMeaning :
        criticalDissipation
        ≡ integratedCriticalDissipation trajectory cutoff terminal
      integratedSignedProductionMeaning :
        integratedSignedProduction
        ≡ integratedCriticalProduction trajectory cutoff terminal

  open LiteralFiniteCriticalObservables public

  canonicalLiteralFiniteCriticalObservables :
    (trajectory : Dyn.PhysicalNSGalerkinTrajectory) →
    (cutoff : Nat) →
    (terminal : Time) →
    LiteralFiniteCriticalObservables trajectory cutoff terminal
  canonicalLiteralFiniteCriticalObservables trajectory cutoff terminal = record
    { initialCritical = criticalEnergyAt trajectory cutoff initialTime
    ; terminalCritical = criticalEnergyAt trajectory cutoff terminal
    ; criticalDissipation =
        integratedCriticalDissipation trajectory cutoff terminal
    ; integratedSignedProduction =
        integratedCriticalProduction trajectory cutoff terminal
    ; initialCriticalMeaning = refl
    ; terminalCriticalMeaning = refl
    ; criticalDissipationMeaning = refl
    ; integratedSignedProductionMeaning = refl
    }

------------------------------------------------------------------------
-- Status / firewalls.
------------------------------------------------------------------------

literalCriticalEndpointFoldConstructed : Bool
literalCriticalEndpointFoldConstructed = true

literalCriticalDissipationFoldConstructed : Bool
literalCriticalDissipationFoldConstructed = true

literalProjectedNonlinearProductionFoldConstructed : Bool
literalProjectedNonlinearProductionFoldConstructed = true

r517CriticalMultiplierComparisonReused : Bool
r517CriticalMultiplierComparisonReused =
  R517.round517FiniteCarrierCriticalNormRealizationClosed

-- The production scalar above is computed from the projected nonlinearity.
-- It is deliberately not defined as X(T)-X(0)+nu*D or any equivalent residual.
productionDefinedByEnergyResidual : Bool
productionDefinedByEnergyResidual = false

-- The exact coefficient/factor identifying this fold with R414's chosen
-- integratedSignedProduction is the next same-object theorem. Keeping this
-- false prevents an unnoticed factor-two or convention mismatch from becoming
-- definitional.
r414ProductionNormalisationRecovered : Bool
r414ProductionNormalisationRecovered = false

-- S0 constructs literal finite observables, but R414's complete slice still
-- needs S1--S4. In particular this owner does not invent critical-energy,
-- signed-remainder, initial-ceiling, or retained-viscosity receipts.
r414FullPhysicalSliceConstructed : Bool
r414FullPhysicalSliceConstructed = false

literalCriticalEndpointFoldConstructedIsTrue :
  literalCriticalEndpointFoldConstructed ≡ true
literalCriticalEndpointFoldConstructedIsTrue = refl

literalCriticalDissipationFoldConstructedIsTrue :
  literalCriticalDissipationFoldConstructed ≡ true
literalCriticalDissipationFoldConstructedIsTrue = refl

literalProjectedNonlinearProductionFoldConstructedIsTrue :
  literalProjectedNonlinearProductionFoldConstructed ≡ true
literalProjectedNonlinearProductionFoldConstructedIsTrue = refl

r517CriticalMultiplierComparisonReusedIsTrue :
  r517CriticalMultiplierComparisonReused ≡ true
r517CriticalMultiplierComparisonReusedIsTrue =
  R517.round517FiniteCarrierCriticalNormRealizationClosedIsTrue

productionDefinedByEnergyResidualIsFalse :
  productionDefinedByEnergyResidual ≡ false
productionDefinedByEnergyResidualIsFalse = refl

r414ProductionNormalisationRecoveredIsFalse :
  r414ProductionNormalisationRecovered ≡ false
r414ProductionNormalisationRecoveredIsFalse = refl

r414FullPhysicalSliceConstructedIsFalse :
  r414FullPhysicalSliceConstructed ≡ false
r414FullPhysicalSliceConstructedIsFalse = refl
