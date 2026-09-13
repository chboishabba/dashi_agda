module DASHI.Physics.Closure.IncompressibleEulerGalerkinCoreExact where

open import Agda.Primitive using (Level; lsuc)
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Physics.Closure.NSIntegerFourierLattice as Z3
import DASHI.Physics.Closure.NSTriadKNComplex3ExactCarrier as C3
import DASHI.Physics.Closure.NSTriadKNComplex3GalerkinEquationAudit as Galerkin

------------------------------------------------------------------------
-- ZERO-ORIGIN EULER ADAPTER OVER THE HISTORICAL DASHI GALERKIN CARRIER.
--
-- Attribution correction:
--
--   This module does NOT originate the Euler Galerkin carrier.
--
-- The historical owner `NSTriadKNComplex3GalerkinEquationAudit` already owns
-- the literal viscosity-independent projected nonlinear operator
--
--     N_k(u) = projectedNonlinearity system k
--
-- on the exact physical output fibre, and its `ExactProjectedGalerkinEquation`
-- already permits the inviscid specialization by identifying the viscous term
-- with zero.  Historical executable audits also differentiate observables
-- along this Galerkin Euler flow.
--
-- This file is therefore only a thin naming/specialization adapter plus a
-- forced-Euler extension.  It receives ZERO origin/priority credit for the
-- underlying Euler/Galerkin mathematics.
------------------------------------------------------------------------

record ExactEulerSpecialization
    {r : Level}
    {F : C3.RealField r}
    {E : C3.IntegerEmbedding F}
    {I : C3.ModeInverseSquare F E}
    (system : Galerkin.FiniteComplex3GalerkinSystem F E I) : Set (lsuc r) where
  field
    equation : Galerkin.ExactProjectedGalerkinEquation system
    zeroVector : C3.Complex3 F
    viscousTermIsZero :
      (k : Z3.FourierMode) → Galerkin.viscousTerm equation k ≡ zeroVector

open ExactEulerSpecialization public

-- Forced Euler is an orthogonal extension because the historical NS equation
-- record did not make external forcing a first-class field of the projected
-- ODE.  The nonlinear term is still the historical `projectedNonlinearity`.
record ExactProjectedForcedEulerExtension
    {r : Level}
    {F : C3.RealField r}
    {E : C3.IntegerEmbedding F}
    {I : C3.ModeInverseSquare F E}
    (system : Galerkin.FiniteComplex3GalerkinSystem F E I) : Set (lsuc r) where
  field
    timeDerivative forcing : Z3.FourierMode → C3.Complex3 F

    projectedForcedEulerODE :
      (k : Z3.FourierMode) → Galerkin.modeListed system k →
      timeDerivative k
      ≡ C3.complex3Add
          (Galerkin.projectedNonlinearity system k)
          (forcing k)

    divergenceFreePreserved : Set
    realityConditionPreserved : Set
    forcingTransverse : Set

open ExactProjectedForcedEulerExtension public

record SmoothForcedEulerBlowupWitness
    {r : Level}
    {F : C3.RealField r}
    {E : C3.IntegerEmbedding F}
    {I : C3.ModeInverseSquare F E}
    (Time : Set)
    (system : Galerkin.FiniteComplex3GalerkinSystem F E I) : Set (lsuc r) where
  field
    equation : ExactProjectedForcedEulerExtension system
    terminalTime : Time

    smoothInitialVelocity : Set
    smoothForcingThroughTerminalTime : Set
    finiteEnergyBeforeTerminalTime : Set
    classicalSolutionBeforeTerminalTime : Set
    uniquenessInClaimedClassBeforeTerminalTime : Set
    vorticityBecomesUnboundedAtTerminalTime : Set

open SmoothForcedEulerBlowupWitness public

------------------------------------------------------------------------
-- Attribution / provenance firewall.
------------------------------------------------------------------------

historicalDashiEulerGalerkinCarrierPredatesThisAdapter : Bool
historicalDashiEulerGalerkinCarrierPredatesThisAdapter = true

thisAdapterOriginatesEulerGalerkinCarrier : Bool
thisAdapterOriginatesEulerGalerkinCarrier = false

thisAdapterGetsEulerOriginPriorityCredit : Bool
thisAdapterGetsEulerOriginPriorityCredit = false

historicalProjectedNonlinearityReusedWithoutReplacement : Bool
historicalProjectedNonlinearityReusedWithoutReplacement = true

forcedEulerExtensionIsNewCoordinateNotNewNonlinearOntology : Bool
forcedEulerExtensionIsNewCoordinateNotNewNonlinearOntology = true

specificExternalBlowupConstructionInhabitedHere : Bool
specificExternalBlowupConstructionInhabitedHere = false

thisAdapterGetsEulerOriginPriorityCreditIsFalse :
  thisAdapterGetsEulerOriginPriorityCredit ≡ false
thisAdapterGetsEulerOriginPriorityCreditIsFalse = refl

specificExternalBlowupConstructionInhabitedHereIsFalse :
  specificExternalBlowupConstructionInhabitedHere ≡ false
specificExternalBlowupConstructionInhabitedHereIsFalse = refl
