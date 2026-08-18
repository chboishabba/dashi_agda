module DASHI.Physics.Closure.NSTriadKNFiniteRationalSlotAssignmentBridgeRound74Exact where

------------------------------------------------------------------------
-- PRIMARY SOURCES / CONTEXT
--
-- Author: Roger Temam.
-- Title: "Navier-Stokes Equations: Theory and Numerical Analysis".
-- DOI: 10.1090/chel/343.
--
-- Author: Philip Hartman.
-- Title: "Ordinary Differential Equations".
-- DOI: 10.1137/1.9780898719222.
--
-- ROUND74 / CORRECT FINITE INPUT CHART FOR THE EXISTING LIPSCHITZ THEOREM
--
-- Round28 already proved the quantitative local-Lipschitz estimate for the
-- literal degree-two Galerkin coordinate polynomial, but its semantic state was
-- the unrestricted function
--
--   CoordinateVariable -> Q.
--
-- Round71 repaired the physical ODE carrier to a finite ordered list containing
-- exactly six real slots per canonical reality-orbit mode.  This file builds an
-- executable lookup from that corrected finite rational state into the old
-- assignment semantics.  Off-chart variables are zero; variables occurring in
-- the finite slot list are read from the actual finite state.
--
-- This does NOT re-authorize the old unrestricted assignment as the physical
-- phase space.  It is only an evaluation chart used to reuse the already-proved
-- polynomial difference/Lipschitz theorem on the corrected finite carrier.
--
-- Remaining A1 work after this file:
--   1. prove the fixed canonical physical RHS agrees with the coordinate
--      polynomial evaluated through this finite chart;
--   2. transport the finite quantitative estimate to a complete real normed
--      carrier and invoke Picard--Lindelof.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Data.Rational.Base using (ℚ; 0ℚ; _-_; _*_; _≤_; ∣_∣)

import DASHI.Physics.Closure.NSTriadKNPhysicalOutputFiber as Output
import DASHI.Physics.Closure.NSTriadKNLuoFiniteGalerkinPolynomialRound26Exact as Polynomial
import DASHI.Physics.Closure.NSTriadKNRationalOrderedFiniteL2 as L2
import DASHI.Physics.Closure.NSTriadKNFiniteRealCanonicalCoordinateCarrierRound71Exact as Finite
import DASHI.Physics.Closure.NSTriadKNFiniteGalerkinLocalLipschitzRound28Exact as Lipschitz

axisEqual : Polynomial.CoordinateAxis → Polynomial.CoordinateAxis → Bool
axisEqual Polynomial.xAxis Polynomial.xAxis = true
axisEqual Polynomial.yAxis Polynomial.yAxis = true
axisEqual Polynomial.zAxis Polynomial.zAxis = true
axisEqual _ _ = false

axisEqualSound : ∀ {left right} → axisEqual left right ≡ true → left ≡ right
axisEqualSound {Polynomial.xAxis} {Polynomial.xAxis} proof = refl
axisEqualSound {Polynomial.xAxis} {Polynomial.yAxis} ()
axisEqualSound {Polynomial.xAxis} {Polynomial.zAxis} ()
axisEqualSound {Polynomial.yAxis} {Polynomial.xAxis} ()
axisEqualSound {Polynomial.yAxis} {Polynomial.yAxis} proof = refl
axisEqualSound {Polynomial.yAxis} {Polynomial.zAxis} ()
axisEqualSound {Polynomial.zAxis} {Polynomial.xAxis} ()
axisEqualSound {Polynomial.zAxis} {Polynomial.yAxis} ()
axisEqualSound {Polynomial.zAxis} {Polynomial.zAxis} proof = refl

axisEqualRefl : ∀ axis → axisEqual axis axis ≡ true
axisEqualRefl Polynomial.xAxis = refl
axisEqualRefl Polynomial.yAxis = refl
axisEqualRefl Polynomial.zAxis = refl

partEqual : Polynomial.CoordinatePart → Polynomial.CoordinatePart → Bool
partEqual Polynomial.realPart Polynomial.realPart = true
partEqual Polynomial.imaginaryPart Polynomial.imaginaryPart = true
partEqual _ _ = false

partEqualSound : ∀ {left right} → partEqual left right ≡ true → left ≡ right
partEqualSound {Polynomial.realPart} {Polynomial.realPart} proof = refl
partEqualSound {Polynomial.realPart} {Polynomial.imaginaryPart} ()
partEqualSound {Polynomial.imaginaryPart} {Polynomial.realPart} ()
partEqualSound {Polynomial.imaginaryPart} {Polynomial.imaginaryPart} proof = refl

partEqualRefl : ∀ part → partEqual part part ≡ true
partEqualRefl Polynomial.realPart = refl
partEqualRefl Polynomial.imaginaryPart = refl

coordinateEqual :
  Polynomial.CoordinateVariable → Polynomial.CoordinateVariable → Bool
coordinateEqual left right =
  Output._and_
    (Output.modeEqual
      (Polynomial.variableMode left)
      (Polynomial.variableMode right))
    (Output._and_
      (axisEqual
        (Polynomial.variableAxis left)
        (Polynomial.variableAxis right))
      (partEqual
        (Polynomial.variablePart left)
        (Polynomial.variablePart right)))

coordinateExt :
  ∀ {left right : Polynomial.CoordinateVariable} →
  Polynomial.variableMode left ≡ Polynomial.variableMode right →
  Polynomial.variableAxis left ≡ Polynomial.variableAxis right →
  Polynomial.variablePart left ≡ Polynomial.variablePart right →
  left ≡ right
coordinateExt
  {Polynomial.coordinate-variable lm la lp}
  {Polynomial.coordinate-variable .lm .la .lp}
  refl refl refl = refl

coordinateEqualSound : ∀ {left right} →
  coordinateEqual left right ≡ true → left ≡ right
coordinateEqualSound {left} {right} proof =
  coordinateExt
    (Output.modeEqualSound
      (Output.andTrueLeft
        {a = Output.modeEqual
          (Polynomial.variableMode left)
          (Polynomial.variableMode right)}
        {b = Output._and_
          (axisEqual
            (Polynomial.variableAxis left)
            (Polynomial.variableAxis right))
          (partEqual
            (Polynomial.variablePart left)
            (Polynomial.variablePart right))}
        proof))
    (axisEqualSound
      (Output.andTrueLeft
        {a = axisEqual
          (Polynomial.variableAxis left)
          (Polynomial.variableAxis right)}
        {b = partEqual
          (Polynomial.variablePart left)
          (Polynomial.variablePart right)}
        (Output.andTrueRight
          {a = Output.modeEqual
            (Polynomial.variableMode left)
            (Polynomial.variableMode right)}
          {b = Output._and_
            (axisEqual
              (Polynomial.variableAxis left)
              (Polynomial.variableAxis right))
            (partEqual
              (Polynomial.variablePart left)
              (Polynomial.variablePart right))}
          proof)))
    (partEqualSound
      (Output.andTrueRight
        {a = axisEqual
          (Polynomial.variableAxis left)
          (Polynomial.variableAxis right)}
        {b = partEqual
          (Polynomial.variablePart left)
          (Polynomial.variablePart right)}
        (Output.andTrueRight
          {a = Output.modeEqual
            (Polynomial.variableMode left)
            (Polynomial.variableMode right)}
          {b = Output._and_
            (axisEqual
              (Polynomial.variableAxis left)
              (Polynomial.variableAxis right))
            (partEqual
              (Polynomial.variablePart left)
              (Polynomial.variablePart right))}
          proof)))

coordinateEqualRefl : ∀ variable → coordinateEqual variable variable ≡ true
coordinateEqualRefl
    (Polynomial.coordinate-variable mode axis part)
  rewrite Output.modeEqualRefl mode
        | axisEqualRefl axis
        | partEqualRefl part = refl

lookupFiniteRationalEntries :
  Polynomial.CoordinateVariable →
  List (Finite.RealSlotValue L2.rationalRealField) → ℚ
lookupFiniteRationalEntries variable [] = 0ℚ
lookupFiniteRationalEntries variable (entry ∷ rest)
  with coordinateEqual variable (Finite.slot entry)
... | true = Finite.value entry
... | false = lookupFiniteRationalEntries variable rest

lookupHeadExact :
  ∀ entry rest →
  lookupFiniteRationalEntries
    (Finite.slot entry)
    (entry ∷ rest)
  ≡ Finite.value entry
lookupHeadExact entry rest
  rewrite coordinateEqualRefl (Finite.slot entry) = refl

finiteRationalAssignment :
  ∀ {slots} →
  Finite.FiniteRealCoordinateState L2.rationalRealField slots →
  Polynomial.Assignment
finiteRationalAssignment state variable =
  lookupFiniteRationalEntries variable (Finite.entries state)

assignmentReadsHeadEntryExactly :
  ∀ {slots}
    (state : Finite.FiniteRealCoordinateState L2.rationalRealField slots)
    {entry rest} →
  Finite.entries state ≡ entry ∷ rest →
  finiteRationalAssignment state (Finite.slot entry) ≡ Finite.value entry
assignmentReadsHeadEntryExactly state refl = lookupHeadExact _ _

finiteChartCoordinateRightHandSideLocalLipschitz :
  (radius delta : ℚ) →
  0ℚ ≤ radius →
  0ℚ ≤ delta →
  (equation : Polynomial.LiteralGalerkinCoordinateEquation) →
  ∀ {leftSlots rightSlots}
    (left : Finite.FiniteRealCoordinateState L2.rationalRealField leftSlots)
    (right : Finite.FiniteRealCoordinateState L2.rationalRealField rightSlots) →
  Lipschitz.AssignmentBound radius (finiteRationalAssignment left) →
  Lipschitz.AssignmentBound radius (finiteRationalAssignment right) →
  Lipschitz.AssignmentDifferenceBound delta
    (finiteRationalAssignment left) (finiteRationalAssignment right) →
  ∣ Polynomial.coordinateRightHandSide equation (finiteRationalAssignment left)
    - Polynomial.coordinateRightHandSide equation (finiteRationalAssignment right) ∣
  ≤
  Lipschitz.atomsLipschitzWeight radius
    (Polynomial.rightHandSideAtoms equation)
  * delta
finiteChartCoordinateRightHandSideLocalLipschitz
  radius delta radiusNN deltaNN equation left right
  leftBound rightBound differenceBound =
  Lipschitz.coordinateRightHandSideLocalLipschitz
    radius delta radiusNN deltaNN equation
    (finiteRationalAssignment left)
    (finiteRationalAssignment right)
    leftBound rightBound differenceBound

round74CorrectedFiniteRationalStateHasExecutableAssignmentChart : Bool
round74CorrectedFiniteRationalStateHasExecutableAssignmentChart = true

round74Round28LipschitzMajorantAppliesThroughFiniteChart : Bool
round74Round28LipschitzMajorantAppliesThroughFiniteChart = true

round74PhysicalRHSAgreesWithFiniteChartPolynomial : Bool
round74PhysicalRHSAgreesWithFiniteChartPolynomial = false

round74RealPicardLindelofAppliedToFiniteChart : Bool
round74RealPicardLindelofAppliedToFiniteChart = false

round74Round28LipschitzMajorantAppliesThroughFiniteChartIsTrue :
  round74Round28LipschitzMajorantAppliesThroughFiniteChart ≡ true
round74Round28LipschitzMajorantAppliesThroughFiniteChartIsTrue = refl
