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
--   D_N(T)   -- integrated ODE-compatible critical viscous mass;
--   N_N(T)   -- integrated dyadic critical real-Hermitian pairing of u_N with
--               the literal Audit.projectedNonlinearity.
--
-- The nonlinear production is NOT defined by rearranging an energy identity.
-- Hence the later critical-energy identity remains a genuine theorem rather
-- than becoming true by definition.
--
-- Exact dissipation normalization
-- -------------------------------
-- If the endpoint critical weight is w(k), differentiating that quadratic
-- energy against the literal viscous term produces the exact weight
--
--     w(k) * |k|^2 * |u_k|^2,
--
-- not w(k)^3 * |u_k|^2.  The latter is an equivalent dyadic H^(3/2) norm, but
-- replacing the exact ODE weight by it at definition time would silently turn
-- the energy identity into an inequality.  Therefore this S0 owner keeps the
-- exact mixed viscous weight. R517 remains the theorem-backed finite-carrier
-- comparison authority used later to transport this dyadic route to the
-- physical H^(1/2)/H^(3/2) interpretation.
--
-- Scalar / physical-norm boundary
-- -------------------------------
-- R414 is a rational finite algebra surface. The selected dyadic endpoint
-- weight therefore stays in Q so that R240's existing
-- integrateTo : (Time -> Q) -> ... can be reused literally. This file does NOT
-- claim that its rational dyadic weight is definitionally the Bishop-real
-- physical multiplier.
--
-- Geometry is deliberately generic in the exact integer embedding E and
-- inverse-square witness I carried by the finite system. The live R240 state
-- therefore supplies its own same-object Fourier geometry; no invented
-- rational-geometry alias is introduced here.
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
-- Exact rational dyadic endpoint weight.
------------------------------------------------------------------------

natAsRational : Nat → ℚ
natAsRational zero = 0ℚ
natAsRational (suc n) = 1ℚ + natAsRational n

dyadicCriticalWeight : Z3.FourierMode → ℚ
dyadicCriticalWeight mode =
  natAsRational (Shell.pow2 (Shell.shellIndex mode))

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

-- Exact viscous quadratic form paired with the selected endpoint multiplier.
criticalViscousMass :
  ∀ {E : C3.IntegerEmbedding F}
    {I : C3.ModeInverseSquare F E} →
  Audit.FiniteComplex3GalerkinSystem F E I →
  List Z3.FourierMode →
  ℚ
criticalViscousMass system [] = 0ℚ
criticalViscousMass system (mode ∷ rest) =
  (dyadicCriticalWeight mode * C3.normSquared (Audit.inverseSquare system) mode)
    * L2.complex3NormSquared (Audit.velocity system mode)
    + criticalViscousMass system rest

criticalDissipationRate :
  ∀ {E : C3.IntegerEmbedding F}
    {I : C3.ModeInverseSquare F E} →
  Audit.FiniteComplex3GalerkinSystem F E I →
  ℚ
criticalDissipationRate system =
  criticalViscousMass system (Audit.modes system)

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

productionDefinedByEnergyResidual : Bool
productionDefinedByEnergyResidual = false

r414ProductionNormalisationRecovered : Bool
r414ProductionNormalisationRecovered = false

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
