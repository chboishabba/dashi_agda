module DASHI.Physics.Closure.NSTriadKNPeriodicPVZeroMassFourierCriterionRound38Exact where

------------------------------------------------------------------------
-- PRIMARY SOURCES / CONTEXT
--
-- Authors: Hajer Bahouri; Jean-Yves Chemin; Raphael Danchin.
-- Title: "Fourier Analysis and Nonlinear Partial Differential Equations".
-- Springer, 2011.
-- DOI: 10.1007/978-3-642-16830-7.
--
-- Authors: Peter Constantin; Charles Fefferman.
-- Title: "Direction of Vorticity and the Problem of Global Regularity for
-- the Navier--Stokes Equations".
-- DOI: 10.1512/iumj.1993.42.42034.
--
-- DASHI CONTRIBUTION
--
-- Close one analytic-algebraic step in the periodic PV lane using the
-- repository's already exact character/integral machinery.  For every
-- periodic kernel represented by PeriodicComplexCharacterData, the transform
-- at zero is already proved equal to the kernel mass.  Therefore a literal
-- zero Fourier multiplier at k=0 forces zero kernel mass:
--
--   Khat(0) = 0  =>  integral K = 0.
--
-- This does not assert that the physical torus strain kernel has already been
-- realized by this character carrier.  That same-object realization and the
-- singular PV estimate remain the hard A3/A4 producer.  The point is that once
-- the literal strain realization supplies its zero-mode multiplier theorem,
-- zero mass is no longer an independent analytic assumption.
------------------------------------------------------------------------

open import Agda.Primitive using (Level; lsuc)
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Relation.Binary.PropositionalEquality using (sym; trans)

import DASHI.Physics.Closure.NSIntegerFourierLattice as Z3
import DASHI.Physics.Closure.NSTriadKNComplex3ExactCarrier as C3
import DASHI.Physics.Closure.NSTriadKNLuoPeriodicComplexCharacterMultiplierExact as Periodic

record ZeroModeMultiplierWitness
    {r : Level}
    {F : C3.RealField r}
    (kernel : Periodic.PeriodicComplexCharacterData F) : Set (lsuc r) where
  constructor zero-mode-multiplier-witness
  field
    zeroModeTransformVanishes :
      Periodic.periodicKernelTransform kernel Z3.zeroMode
      ≡ C3.complexZero F

open ZeroModeMultiplierWitness public

zeroModeMultiplierForcesKernelMassZero :
  ∀ {r} {F : C3.RealField r}
    {kernel : Periodic.PeriodicComplexCharacterData F} →
  ZeroModeMultiplierWitness kernel →
  Periodic.periodicKernelMass kernel ≡ C3.complexZero F
zeroModeMultiplierForcesKernelMassZero {kernel = kernel} witness =
  trans
    (sym (Periodic.periodicZeroTransformEqualsKernelMass kernel))
    (zeroModeTransformVanishes witness)

record PeriodicStrainPVZeroMassBridge
    {r : Level}
    {F : C3.RealField r} : Set (lsuc r) where
  field
    strainKernel : Periodic.PeriodicComplexCharacterData F
    strainZeroMode : ZeroModeMultiplierWitness strainKernel

open PeriodicStrainPVZeroMassBridge public

periodicStrainKernelMassZeroFromFourierCriterion :
  ∀ {r} {F : C3.RealField r} →
  (bridge : PeriodicStrainPVZeroMassBridge {r} {F}) →
  Periodic.periodicKernelMass (strainKernel bridge)
  ≡ C3.complexZero F
periodicStrainKernelMassZeroFromFourierCriterion bridge =
  zeroModeMultiplierForcesKernelMassZero (strainZeroMode bridge)

periodicPVZeroMassFourierCriterionClosed : Bool
periodicPVZeroMassFourierCriterionClosed = true

literalPhysicalStrainKernelCharacterRealizationConstructed : Bool
literalPhysicalStrainKernelCharacterRealizationConstructed = false

periodicPVZeroMassFourierCriterionClosedIsTrue :
  periodicPVZeroMassFourierCriterionClosed ≡ true
periodicPVZeroMassFourierCriterionClosedIsTrue = refl
