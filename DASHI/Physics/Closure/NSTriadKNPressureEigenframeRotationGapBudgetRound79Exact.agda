module DASHI.Physics.Closure.NSTriadKNPressureEigenframeRotationGapBudgetRound79Exact where

------------------------------------------------------------------------
-- PRIMARY SOURCES / CONTEXT
--
-- Author: Tosio Kato.
-- Title: "Perturbation Theory for Linear Operators".
-- DOI: 10.1007/978-3-642-66282-9.
--
-- Authors: Dhawal Buaria; Alain Pumir.
-- Title: "Role of pressure in the dynamics of intense velocity gradients in
-- turbulent flows".
-- DOI: 10.1017/jfm.2023.786.
--
-- Author: Andrea Cavazzini.
-- Title: "Self-Frustration of Vortex Stretching and the Architecture of the
-- Navier-Stokes Blow-Up Barrier".
-- DOI: 10.5281/zenodo.19158797.
--
-- ROUND79 / DIVISION-FREE EIGENFRAME ROTATION BUDGET
--
-- Rellich--Kato eigenvector differentiation produces schematic terms
--
--   injection / spectralGap.
--
-- Round79 keeps this estimate division-free. A claimed rotation budget R is
-- certified by
--
--   |injection| <= R * spectralGap,
--
-- together with a strictly positive physical spectral gap. This makes a
-- collapsing denominator visible instead of replacing it by an unjustified
-- lower bound comparable to ||omega||_infinity.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Rational.Base using (ℚ; 0ℚ; _*_; _≤_; _<_)

record PressureEigenframeRotationGapBudget : Set where
  constructor pressure-eigenframe-rotation-gap-budget
  field
    injectionMagnitude : ℚ
    spectralGap : ℚ
    rotationBudget : ℚ
    injectionNonnegative : 0ℚ ≤ injectionMagnitude
    gapPositive : 0ℚ < spectralGap
    rotationBudgetNonnegative : 0ℚ ≤ rotationBudget
    divisionFreeRotationBound :
      injectionMagnitude ≤ rotationBudget * spectralGap

open PressureEigenframeRotationGapBudget public

record GapIndependentInjectionBound : Set where
  constructor gap-independent-injection-bound
  field
    numeratorCeiling : ℚ
    injectionValue : ℚ
    gapValue : ℚ
    numeratorBound : injectionValue ≤ numeratorCeiling

-- A numerator ceiling deliberately does not contain a rotation budget theorem:
-- without a positive lower control on the actual gap, division is unauthorized.
record PressureRotationClosureInputs : Set where
  constructor pressure-rotation-closure-inputs
  field
    numerator : GapIndependentInjectionBound
    gapBudget : PressureEigenframeRotationGapBudget
    sameInjection :
      injectionValue numerator ≡ injectionMagnitude gapBudget
    sameGap :
      gapValue numerator ≡ spectralGap gapBudget

open PressureRotationClosureInputs public

round79NumeratorBoundAloneClosesEigenframeRotation : Bool
round79NumeratorBoundAloneClosesEigenframeRotation = false

round79DivisionFreeGapBudgetIsRequired : Bool
round79DivisionFreeGapBudgetIsRequired = true

round79NumeratorBoundAloneClosesEigenframeRotationIsFalse :
  round79NumeratorBoundAloneClosesEigenframeRotation ≡ false
round79NumeratorBoundAloneClosesEigenframeRotationIsFalse = refl
