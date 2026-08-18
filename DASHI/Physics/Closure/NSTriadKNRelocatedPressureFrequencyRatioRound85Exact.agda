module DASHI.Physics.Closure.NSTriadKNRelocatedPressureFrequencyRatioRound85Exact where

------------------------------------------------------------------------
-- PRIMARY SOURCES / CONTEXT
--
-- Author: Marco Cannone.
-- Title: "Harmonic Analysis Tools for Solving the Incompressible
-- Navier-Stokes Equations".
-- DOI: 10.1016/S1874-5792(05)80006-0.
--
-- Authors: Hajer Bahouri; Jean-Yves Chemin; Raphael Danchin.
-- Title: "Fourier Analysis and Nonlinear Partial Differential Equations".
-- DOI: 10.1007/978-3-642-16830-7.
--
-- ROUND85 / EXACT MULTIPLIER OF THE RELOCATED PRESSURE SHARE
--
-- The pressure-as-transport decomposition contains
--
--   relocated = - pHat_p (p dot k),
--   source    =   |p|^2 pHat_p = (-Delta p)_p.
--
-- Therefore, without any division or order assumptions,
--
--   |p|^2 relocated = -(p dot k) source.
--
-- On an ordered real/rational geometry this means the only multiplier loss is
-- |p dot k|/|p|^2 <= |k|/|p|.  Thus comparable/high pressure legs are order
-- zero; only a genuinely low pressure leg requires the first-adjoint/Bony
-- paraproduct estimate.  This file proves the division-free same-object
-- identity on the literal complex Fourier carrier.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using ([]; _∷_)
open import Relation.Binary.PropositionalEquality using (cong; trans)

import DASHI.Physics.Closure.NSTriadKNComplex3ExactCarrier as C3
import DASHI.Physics.Closure.NSTriadKNComplexCommutativeRingExact as CRing
import DASHI.Physics.Closure.NSTriadKNComplex3GalerkinEquationAudit as Audit
import DASHI.Physics.Closure.NSTriadKNPhysicalTriadEnumeration as Physical
import DASHI.Physics.Closure.NSTriadKNPressureTransportPoissonSplitRound85Exact as Transport

relocatedTimesNormSquaredEqualsDotTimesSource :
  ∀ {r} {F : C3.RealField r}
    {E : C3.IntegerEmbedding F}
    {I : C3.ModeInverseSquare F E}
    (system : Audit.FiniteComplex3GalerkinSystem F E I)
    (incidence : Physical.PhysicalTriadIncidence) →
  C3.complexMultiply
    (Transport.pressureRelocatedScalar system incidence)
    (C3.realEmbed F (C3.normSquared I (Physical.p incidence)))
  ≡ C3.complexNegate
      (C3.complexMultiply
        (Transport.modeDot E (Physical.p incidence) (Physical.k incidence))
        (Transport.pressurePoissonSourceCoefficient
          system (Physical.p incidence)))
relocatedTimesNormSquaredEqualsDotTimesSource {F = F} {E = E} {I = I}
    system incidence =
  let
    pHat =
      DASHI.Physics.Closure.NSTriadKNPressurePotentialGradientHessianSameModeRound85Exact.pressurePotential
        system (Physical.p incidence)
    dot = Transport.modeDot E (Physical.p incidence) (Physical.k incidence)
    norm = C3.realEmbed F (C3.normSquared I (Physical.p incidence))
  in
  C.solve 3
    (λ p d n →
      ((C.⊝ (p C.⊗ d)) C.⊗ n)
      C.⊜ (C.⊝ (d C.⊗ (p C.⊗ n))))
    refl pHat dot norm
  where module C = CRing.Solver F

round85RelocatedPressureFrequencyRatioExposed : Bool
round85RelocatedPressureFrequencyRatioExposed = true

round85RelocatedPressureComparableHighLegIsOrderZero : Bool
round85RelocatedPressureComparableHighLegIsOrderZero = false

round85RelocatedPressureLowLegFirstAdjointBoundConstructed : Bool
round85RelocatedPressureLowLegFirstAdjointBoundConstructed = false

round85RelocatedPressureFrequencyRatioExposedIsTrue :
  round85RelocatedPressureFrequencyRatioExposed ≡ true
round85RelocatedPressureFrequencyRatioExposedIsTrue = refl
