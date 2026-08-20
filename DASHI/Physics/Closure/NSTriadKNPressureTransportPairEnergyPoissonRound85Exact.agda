module DASHI.Physics.Closure.NSTriadKNPressureTransportPairEnergyPoissonRound85Exact where

------------------------------------------------------------------------
-- PRIMARY SOURCES / CONTEXT
--
-- Author: Roger Temam.
-- Title: "Navier-Stokes Equations: Theory and Numerical Analysis".
-- DOI: 10.1090/chel/343.
--
-- Authors: Jinhee Jeong; Fazle Hussain.
-- Title: "On the identification of a vortex".
-- DOI: 10.1017/S0022112095000462.
--
-- ROUND85 / PRESSURE TRANSPORT REVERSE PAIR ENERGY = POISSON DEFECT ENERGY
--
-- Combine the exact pressure transport adjoint defect
--
--   conjugate(T_qk) + T_kq = -h_m
--
-- with the generic pairwise quadratic-form theorem.  For any vector amplitudes
-- u_k,u_q on a resonant reverse pair m+q=k,
--
--   Re( <u_k,T_kq u_q> + <u_q,T_qk u_k> )
--     = Re <u_k,(-h_m) u_q>.
--
-- Here h_m is the literal complex Poisson source coefficient
--
--   h_m = (-Delta p)_m = -2 Q_m.
--
-- This is the exact finite-Fourier integration-by-parts identity pair by pair.
-- The remaining principal-packet step is purely finite combinatorics: partition
-- the selected transport matrix into reverse pairs and account for the doubled
-- Fourier representation of the real quadratic source term.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true)
open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Physics.Closure.NSIntegerFourierLattice as Z3
import DASHI.Physics.Closure.NSTriadKNComplex3ExactCarrier as C3
import DASHI.Physics.Closure.NSTriadKNComplex3RealityPhaseAudit as Reality
import DASHI.Physics.Closure.NSTriadKNComplex3GalerkinEquationAudit as Galerkin
import DASHI.Physics.Closure.NSTriadKNLiteralAdvectivePressureRHSSplitRound84Exact as AP
import DASHI.Physics.Closure.NSTriadKNPressureTransportPoissonSplitRound85Exact as Poisson
import DASHI.Physics.Closure.NSTriadKNPressureTransportAdjointDivergenceDefectRound85Exact as Defect
import DASHI.Physics.Closure.NSTriadKNTransportPairEnergyDefectRound85Exact as Pair

pressureTransportPairEnergyPoissonExact :
  ∀ {r} {F : C3.RealField r}
    {E : C3.IntegerEmbedding F}
    {I : C3.ModeInverseSquare F E}
    (system : Galerkin.FiniteComplex3GalerkinSystem F E I)
    (advector input output : Z3.FourierMode)
    (resonance : Z3.addMode advector input ≡ output)
    (pressureReality : Reality.RealityCondition (AP.pressureNonlinearity system))
    (outputValue inputValue : C3.Complex3 F) →
  C3.real
    (C3.complexAdd
      (Pair.forwardEnergy
        (Defect.forwardCoefficient
          (Defect.pressureAdvectorWitness
            system advector input output resonance pressureReality))
        outputValue inputValue)
      (Pair.reverseEnergy
        (Defect.reverseCoefficient
          (Defect.pressureAdvectorWitness
            system advector input output resonance pressureReality))
        outputValue inputValue))
  ≡
  C3.real
    (Pair.defectEnergy
      (C3.complexNegate
        (Poisson.pressurePoissonSourceCoefficient system advector))
      outputValue inputValue)
pressureTransportPairEnergyPoissonExact
    system advector input output resonance pressureReality outputValue inputValue =
  Pair.pairEnergyDefectExact
    (Defect.forwardCoefficient witness)
    (Defect.reverseCoefficient witness)
    (C3.complexNegate
      (Poisson.pressurePoissonSourceCoefficient system advector))
    outputValue inputValue
    (Defect.pressureTransportAdjointDefectIsMinusPoissonSource
      system advector input output resonance pressureReality)
  where
  witness =
    Defect.pressureAdvectorWitness
      system advector input output resonance pressureReality

round85PressureTransportPairEnergyPoissonExact : Bool
round85PressureTransportPairEnergyPoissonExact = true

round85PressureTransportPairEnergyPoissonExactIsTrue :
  round85PressureTransportPairEnergyPoissonExact ≡ true
round85PressureTransportPairEnergyPoissonExactIsTrue = refl
