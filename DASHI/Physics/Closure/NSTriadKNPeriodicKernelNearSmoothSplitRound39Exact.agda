module DASHI.Physics.Closure.NSTriadKNPeriodicKernelNearSmoothSplitRound39Exact where

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
-- Indiana University Mathematics Journal 42 (1993), 775--789.
-- DOI: 10.1512/iumj.1993.42.42034.
--
-- DASHI CONTRIBUTION
--
-- Round 38 reduced the HH-good problem to the literal periodic strain/PV
-- operator.  The efficient analytic route is not to estimate the torus kernel
-- monolithically: split its physical weight into a near singular piece and a
-- smooth periodic correction while keeping the *same* torus, Haar integral
-- and characters.
--
-- This module proves the exact algebra that such a split must satisfy.  If
--
--   K = K_near + K_smooth
--
-- pointwise, then for every Fourier mode and every weighted increment,
--
--   Khat = Khat_near + Khat_smooth,
--   mass K = mass K_near + mass K_smooth,
--   Delta_K = Delta_near + Delta_smooth.
--
-- Thus a future physical theorem
--
--   K_T3 = chi K_R3^hom + R_T3
--
-- can feed the singular HH-good owner estimate and the harmless smooth
-- remainder estimate separately without changing conventions or introducing
-- an independent Fourier carrier.  Existence/smoothness of that literal
-- physical decomposition remains a genuine A3 analytic producer.
------------------------------------------------------------------------

open import Agda.Primitive using (Level; lsuc)
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Relation.Binary.PropositionalEquality using (cong; trans)

import DASHI.Physics.Closure.NSTriadKNComplex3ExactCarrier as C3
import DASHI.Physics.Closure.NSTriadKNComplex3FieldAlgebra as Algebra
import DASHI.Physics.Closure.NSTriadKNComplexCommutativeRingExact as Ring
import DASHI.Physics.Closure.NSTriadKNLuoComplexLinearIntegralWeightedIncrementExact as Integral
import DASHI.Physics.Closure.NSTriadKNLuoPeriodicComplexCharacterMultiplierExact as Periodic
import DASHI.Physics.Closure.NSIntegerFourierLattice as Z3

record PeriodicKernelNearSmoothSplit
    {r : Level}
    {F : C3.RealField r}
    (full : Periodic.PeriodicComplexCharacterData F) : Set (lsuc r) where
  field
    nearWeight smoothWeight :
      Periodic.TorusPoint full → C3.Complex F

    weightSplit :
      (point : Periodic.TorusPoint full) →
      Periodic.kernelWeight full point
      ≡ C3.complexAdd (nearWeight point) (smoothWeight point)

open PeriodicKernelNearSmoothSplit public

nearKernel :
  ∀ {r} {F : C3.RealField r}
    {full : Periodic.PeriodicComplexCharacterData F} →
  PeriodicKernelNearSmoothSplit full →
  Periodic.PeriodicComplexCharacterData F
nearKernel {full = full} split = record
  { TorusPoint = Periodic.TorusPoint full
  ; integral = Periodic.integral full
  ; kernelWeight = nearWeight split
  ; character = Periodic.character full
  ; characterAdd = Periodic.characterAdd full
  ; characterZero = Periodic.characterZero full
  }

smoothKernel :
  ∀ {r} {F : C3.RealField r}
    {full : Periodic.PeriodicComplexCharacterData F} →
  PeriodicKernelNearSmoothSplit full →
  Periodic.PeriodicComplexCharacterData F
smoothKernel {full = full} split = record
  { TorusPoint = Periodic.TorusPoint full
  ; integral = Periodic.integral full
  ; kernelWeight = smoothWeight split
  ; character = Periodic.character full
  ; characterAdd = Periodic.characterAdd full
  ; characterZero = Periodic.characterZero full
  }

transformIntegrandSplit :
  ∀ {r} {F : C3.RealField r}
    {full : Periodic.PeriodicComplexCharacterData F}
    (split : PeriodicKernelNearSmoothSplit full)
    (mode : Z3.FourierMode)
    (point : Periodic.TorusPoint full) →
  C3.complexMultiply
    (Periodic.kernelWeight full point)
    (Periodic.character full mode point)
  ≡
  C3.complexAdd
    (C3.complexMultiply
      (nearWeight split point)
      (Periodic.character full mode point))
    (C3.complexMultiply
      (smoothWeight split point)
      (Periodic.character full mode point))
transformIntegrandSplit split mode point =
  trans
    (cong
      (λ weight →
        C3.complexMultiply weight
          (Periodic.character _ mode point))
      (weightSplit split point))
    (Ring.complexDistributeRight
      (nearWeight split point)
      (smoothWeight split point)
      (Periodic.character _ mode point))

periodicKernelTransformSplits :
  ∀ {r} {F : C3.RealField r}
    {full : Periodic.PeriodicComplexCharacterData F}
    (split : PeriodicKernelNearSmoothSplit full)
    (mode : Z3.FourierMode) →
  Periodic.periodicKernelTransform full mode
  ≡
  C3.complexAdd
    (Periodic.periodicKernelTransform (nearKernel split) mode)
    (Periodic.periodicKernelTransform (smoothKernel split) mode)
periodicKernelTransformSplits {full = full} split mode =
  let I = Periodic.integral full in
  trans
    (Integral.integralExtensional I
      (λ point →
        C3.complexMultiply
          (Periodic.kernelWeight full point)
          (Periodic.character full mode point))
      (λ point →
        C3.complexAdd
          (C3.complexMultiply
            (nearWeight split point)
            (Periodic.character full mode point))
          (C3.complexMultiply
            (smoothWeight split point)
            (Periodic.character full mode point)))
      (transformIntegrandSplit split mode))
    (Integral.integralAdd I
      (λ point →
        C3.complexMultiply
          (nearWeight split point)
          (Periodic.character full mode point))
      (λ point →
        C3.complexMultiply
          (smoothWeight split point)
          (Periodic.character full mode point)))

periodicKernelMassSplits :
  ∀ {r} {F : C3.RealField r}
    {full : Periodic.PeriodicComplexCharacterData F}
    (split : PeriodicKernelNearSmoothSplit full) →
  Periodic.periodicKernelMass full
  ≡
  C3.complexAdd
    (Periodic.periodicKernelMass (nearKernel split))
    (Periodic.periodicKernelMass (smoothKernel split))
periodicKernelMassSplits {full = full} split =
  let I = Periodic.integral full in
  trans
    (Integral.integralExtensional I
      (Periodic.kernelWeight full)
      (λ point →
        C3.complexAdd
          (nearWeight split point)
          (smoothWeight split point))
      (weightSplit split))
    (Integral.integralAdd I
      (nearWeight split)
      (smoothWeight split))

incrementFactor :
  ∀ {r} {F : C3.RealField r}
    (full : Periodic.PeriodicComplexCharacterData F) →
  Z3.FourierMode → Z3.FourierMode →
  Periodic.TorusPoint full → C3.Complex F
incrementFactor {F = F} full left right point =
  C3.complexMultiply
    (C3.complexSubtract
      (Periodic.character full left point)
      (C3.complexOne F))
    (C3.complexSubtract
      (Periodic.character full right point)
      (C3.complexOne F))

weightedIncrementIntegrandSplit :
  ∀ {r} {F : C3.RealField r}
    {full : Periodic.PeriodicComplexCharacterData F}
    (split : PeriodicKernelNearSmoothSplit full)
    (left right : Z3.FourierMode)
    (point : Periodic.TorusPoint full) →
  C3.complexMultiply
    (Periodic.kernelWeight full point)
    (incrementFactor full left right point)
  ≡
  C3.complexAdd
    (C3.complexMultiply
      (nearWeight split point)
      (incrementFactor full left right point))
    (C3.complexMultiply
      (smoothWeight split point)
      (incrementFactor full left right point))
weightedIncrementIntegrandSplit {full = full} split left right point =
  trans
    (cong
      (λ weight →
        C3.complexMultiply weight
          (incrementFactor full left right point))
      (weightSplit split point))
    (Ring.complexDistributeRight
      (nearWeight split point)
      (smoothWeight split point)
      (incrementFactor full left right point))

periodicWeightedIncrementSplits :
  ∀ {r} {F : C3.RealField r}
    {full : Periodic.PeriodicComplexCharacterData F}
    (split : PeriodicKernelNearSmoothSplit full)
    (left right : Z3.FourierMode) →
  Periodic.periodicWeightedIncrement full left right
  ≡
  C3.complexAdd
    (Periodic.periodicWeightedIncrement (nearKernel split) left right)
    (Periodic.periodicWeightedIncrement (smoothKernel split) left right)
periodicWeightedIncrementSplits {full = full} split left right =
  let I = Periodic.integral full in
  trans
    (Integral.integralExtensional I
      (λ point →
        C3.complexMultiply
          (Periodic.kernelWeight full point)
          (incrementFactor full left right point))
      (λ point →
        C3.complexAdd
          (C3.complexMultiply
            (nearWeight split point)
            (incrementFactor full left right point))
          (C3.complexMultiply
            (smoothWeight split point)
            (incrementFactor full left right point)))
      (weightedIncrementIntegrandSplit split left right))
    (Integral.integralAdd I
      (λ point →
        C3.complexMultiply
          (nearWeight split point)
          (incrementFactor full left right point))
      (λ point →
        C3.complexMultiply
          (smoothWeight split point)
          (incrementFactor full left right point)))

nearSmoothPeriodicKernelAlgebraClosed : Bool
nearSmoothPeriodicKernelAlgebraClosed = true

literalTorusStrainNearSmoothSplitConstructed : Bool
literalTorusStrainNearSmoothSplitConstructed = false

smoothPeriodicCorrectionOwnerBoundConstructed : Bool
smoothPeriodicCorrectionOwnerBoundConstructed = false

nearSmoothPeriodicKernelAlgebraClosedIsTrue :
  nearSmoothPeriodicKernelAlgebraClosed ≡ true
nearSmoothPeriodicKernelAlgebraClosedIsTrue = refl
