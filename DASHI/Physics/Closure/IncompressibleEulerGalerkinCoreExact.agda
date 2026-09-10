module DASHI.Physics.Closure.IncompressibleEulerGalerkinCoreExact where

open import Agda.Primitive using (Level; lsuc)
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Physics.Closure.NSIntegerFourierLattice as Z3
import DASHI.Physics.Closure.NSTriadKNComplex3ExactCarrier as C3
import DASHI.Physics.Closure.NSTriadKNComplex3GalerkinEquationAudit as Galerkin

------------------------------------------------------------------------
-- GENERAL INCOMPRESSIBLE EULER / FORCED EULER ON THE EXISTING EXACT
-- FOURIER-GALERKIN NONLINEARITY.
--
-- The exact projected nonlinear operator already present in the NS lane is
-- viscosity-independent.  Euler therefore reuses that SAME finite Fourier
-- carrier and omits the viscous term rather than creating a second nonlinear
-- ontology.
--
-- Projected unforced Euler:
--
--     d_t u_k = N_k(u)
--
-- Projected forced Euler:
--
--     d_t u_k = N_k(u) + f_k.
--
-- Pressure is already removed by the Leray projection in N_k.  These records
-- are theorem interfaces on the exact carrier; they do not claim a continuum
-- existence, uniqueness, regularity, or blowup theorem by themselves.
------------------------------------------------------------------------

record ExactProjectedEulerEquation
    {r : Level}
    {F : C3.RealField r}
    {E : C3.IntegerEmbedding F}
    {I : C3.ModeInverseSquare F E}
    (system : Galerkin.FiniteComplex3GalerkinSystem F E I) : Set (lsuc r) where
  field
    timeDerivative : Z3.FourierMode → C3.Complex3 F

    projectedEulerODE :
      (k : Z3.FourierMode) → Galerkin.modeListed system k →
      timeDerivative k ≡ Galerkin.projectedNonlinearity system k

    divergenceFreePreserved : Set
    realityConditionPreserved : Set

open ExactProjectedEulerEquation public

record ExactProjectedForcedEulerEquation
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

open ExactProjectedForcedEulerEquation public

------------------------------------------------------------------------
-- Continuum/blowup theorem interface.
--
-- Kept deliberately generic so a paper-specific construction can inhabit it
-- without changing the Euler equation ontology.
------------------------------------------------------------------------

record SmoothForcedEulerBlowupWitness
    {r : Level}
    {F : C3.RealField r}
    {E : C3.IntegerEmbedding F}
    {I : C3.ModeInverseSquare F E}
    (Time : Set)
    (system : Galerkin.FiniteComplex3GalerkinSystem F E I) : Set (lsuc r) where
  field
    equation : ExactProjectedForcedEulerEquation system
    terminalTime : Time

    smoothInitialVelocity : Set
    smoothForcingThroughTerminalTime : Set
    finiteEnergyBeforeTerminalTime : Set
    classicalSolutionBeforeTerminalTime : Set
    uniquenessInClaimedClassBeforeTerminalTime : Set

    vorticityBecomesUnboundedAtTerminalTime : Set

open SmoothForcedEulerBlowupWitness public

------------------------------------------------------------------------
-- Boundary / status.
------------------------------------------------------------------------

generalEulerProjectedCarrierImplemented : Bool
generalEulerProjectedCarrierImplemented = true

forcedEulerProjectedCarrierImplemented : Bool
forcedEulerProjectedCarrierImplemented = true

sameExactOrderedNonlinearityAsNSReused : Bool
sameExactOrderedNonlinearityAsNSReused = true

positiveViscosityRequiredByEulerEquationInterface : Bool
positiveViscosityRequiredByEulerEquationInterface = false

smoothForcedEulerBlowupTheoremInterfaceImplemented : Bool
smoothForcedEulerBlowupTheoremInterfaceImplemented = true

specificExternalBlowupConstructionInhabitedHere : Bool
specificExternalBlowupConstructionInhabitedHere = false

continuumEulerTheoryCompletedHere : Bool
continuumEulerTheoryCompletedHere = false

specificExternalBlowupConstructionInhabitedHereIsFalse :
  specificExternalBlowupConstructionInhabitedHere ≡ false
specificExternalBlowupConstructionInhabitedHereIsFalse = refl

continuumEulerTheoryCompletedHereIsFalse :
  continuumEulerTheoryCompletedHere ≡ false
continuumEulerTheoryCompletedHereIsFalse = refl
