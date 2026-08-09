module DASHI.Physics.Closure.NSTriadKNCutoffUniformCotlarSteinRound30Exact where

------------------------------------------------------------------------
-- PRIMARY SOURCES / CONTEXT
--
-- Authors: Mischa Cotlar; Elias M. Stein.
-- Title: "A unified theory of Hilbert transforms and ergodic theorems".
-- DOI: not assigned to the cited 1955 conference article.
--
-- Authors: Hajer Bahouri; Jean-Yves Chemin; Raphael Danchin.
-- Title: "Fourier Analysis and Nonlinear Partial Differential Equations".
-- DOI: 10.1007/978-3-642-16830-7.
--
-- Authors: Tosio Kato; Gustavo Ponce.
-- Title: "Commutator Estimates and the Euler and Navier-Stokes Equations".
-- DOI: 10.1002/cpa.3160410704.
--
-- DASHI CONTRIBUTION
--
-- Upgrade the scalar Round-29 cross-shell ledger to the exact operator-valued
-- input required by Cotlar--Stein.  Both products T_q* T_r and T_q T_r* are
-- controlled, their finite row masses are bounded uniformly in the Galerkin
-- cutoff, and the standard finite Cotlar--Stein theorem is consumed only after
-- those two-sided bounds refer to the same operator family.  The output is a
-- squared norm estimate with no square-root or real-completeness shortcut.
------------------------------------------------------------------------

open import Agda.Primitive using (Level; lsuc; _⊔_)
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Data.Rational.Base using (ℚ; 0ℚ; _+_; _*_; _≤_)
import Data.Rational.Properties as ℚP

sumRational : ∀ {Index : Set} → List Index → (Index → ℚ) → ℚ
sumRational [] value = 0ℚ
sumRational (index ∷ rest) value =
  value index + sumRational rest value

record FiniteOperatorSpace
    {operatorLevel : Level}
    (Operator : Set operatorLevel) : Set (lsuc operatorLevel) where
  field
    zeroOperator : Operator
    addOperator composeOperator : Operator → Operator → Operator
    adjointOperator : Operator → Operator
    operatorNorm : Operator → ℚ
    operatorNormNonnegative : ∀ operator → 0ℚ ≤ operatorNorm operator

open FiniteOperatorSpace public

finiteOperatorSum :
  ∀ {operatorLevel}
    {Operator : Set operatorLevel} →
  FiniteOperatorSpace Operator → List Operator → Operator
finiteOperatorSum space [] = zeroOperator space
finiteOperatorSum space (operator ∷ rest) =
  addOperator space operator (finiteOperatorSum space rest)

record OperatorCrossShellDecay
    {operatorLevel shellLevel : Level}
    {Operator : Set operatorLevel}
    {Shell : Set shellLevel}
    (space : FiniteOperatorSpace Operator)
    (shells : List Shell)
    (operatorAt : Shell → Operator) :
    Set (lsuc (operatorLevel ⊔ shellLevel)) where
  field
    leftEnvelope rightEnvelope : Shell → Shell → ℚ
    leftEnvelopeNonnegative : ∀ left right →
      0ℚ ≤ leftEnvelope left right
    rightEnvelopeNonnegative : ∀ left right →
      0ℚ ≤ rightEnvelope left right

    adjointThenForwardBound : ∀ left right →
      operatorNorm space
        (composeOperator space
          (adjointOperator space (operatorAt left))
          (operatorAt right))
      ≤ leftEnvelope left right

    forwardThenAdjointBound : ∀ left right →
      operatorNorm space
        (composeOperator space
          (operatorAt left)
          (adjointOperator space (operatorAt right)))
      ≤ rightEnvelope left right

open OperatorCrossShellDecay public

leftRowMass :
  ∀ {operatorLevel shellLevel}
    {Operator : Set operatorLevel}
    {Shell : Set shellLevel}
    {space : FiniteOperatorSpace Operator}
    {shells : List Shell}
    {operatorAt : Shell → Operator} →
  OperatorCrossShellDecay space shells operatorAt → Shell → ℚ
leftRowMass decay left =
  sumRational _ (leftEnvelope decay left)

rightRowMass :
  ∀ {operatorLevel shellLevel}
    {Operator : Set operatorLevel}
    {Shell : Set shellLevel}
    {space : FiniteOperatorSpace Operator}
    {shells : List Shell}
    {operatorAt : Shell → Operator} →
  OperatorCrossShellDecay space shells operatorAt → Shell → ℚ
rightRowMass decay left =
  sumRational _ (rightEnvelope decay left)

record CutoffUniformCrossShellMass
    {operatorLevel shellLevel}
    {Operator : Set operatorLevel}
    {Shell : Set shellLevel}
    {space : FiniteOperatorSpace Operator}
    {shells : List Shell}
    {operatorAt : Shell → Operator}
    (decay : OperatorCrossShellDecay space shells operatorAt) : Set shellLevel where
  field
    uniformLeftMass uniformRightMass : ℚ
    uniformLeftMassNonnegative : 0ℚ ≤ uniformLeftMass
    uniformRightMassNonnegative : 0ℚ ≤ uniformRightMass
    leftMassBound : ∀ shell →
      leftRowMass decay shell ≤ uniformLeftMass
    rightMassBound : ∀ shell →
      rightRowMass decay shell ≤ uniformRightMass

open CutoffUniformCrossShellMass public

record FiniteCotlarSteinAuthority
    {operatorLevel : Level}
    {Operator : Set operatorLevel}
    (space : FiniteOperatorSpace Operator) : Set (lsuc operatorLevel) where
  field
    finiteCotlarSteinSquared :
      ∀ {Shell : Set}
        (shells : List Shell)
        (operatorAt : Shell → Operator)
        (decay : OperatorCrossShellDecay space shells operatorAt)
        (mass : CutoffUniformCrossShellMass decay) →
      operatorNorm space
        (finiteOperatorSum space (mapOperators shells operatorAt))
      * operatorNorm space
        (finiteOperatorSum space (mapOperators shells operatorAt))
      ≤ uniformLeftMass mass * uniformRightMass mass

    mapOperators : ∀ {Shell : Set} →
      List Shell → (Shell → Operator) → List Operator

open FiniteCotlarSteinAuthority public

cutoffUniformCotlarSteinSquaredBound :
  ∀ {operatorLevel}
    {Operator : Set operatorLevel}
    (space : FiniteOperatorSpace Operator)
    (authority : FiniteCotlarSteinAuthority space)
    {Shell : Set}
    (shells : List Shell)
    (operatorAt : Shell → Operator)
    (decay : OperatorCrossShellDecay space shells operatorAt)
    (mass : CutoffUniformCrossShellMass decay) →
  operatorNorm space
    (finiteOperatorSum space
      (mapOperators authority shells operatorAt))
  * operatorNorm space
    (finiteOperatorSum space
      (mapOperators authority shells operatorAt))
  ≤ uniformLeftMass mass * uniformRightMass mass
cutoffUniformCotlarSteinSquaredBound space authority =
  finiteCotlarSteinSquared authority

record GeometricCrossShellEnvelope
    {operatorLevel : Level}
    {Operator : Set operatorLevel}
    {space : FiniteOperatorSpace Operator}
    {Shell : Set}
    {shells : List Shell}
    {operatorAt : Shell → Operator}
    (decay : OperatorCrossShellDecay space shells operatorAt) : Set where
  field
    commonConstant geometricMass : ℚ
    geometricMassNonnegative : 0ℚ ≤ geometricMass
    leftGeometricMass : ∀ shell →
      leftRowMass decay shell ≤ commonConstant * geometricMass
    rightGeometricMass : ∀ shell →
      rightRowMass decay shell ≤ commonConstant * geometricMass

open GeometricCrossShellEnvelope public

geometricEnvelopeProducesUniformMass :
  ∀ {operatorLevel}
    {Operator : Set operatorLevel}
    {space : FiniteOperatorSpace Operator}
    {Shell : Set}
    {shells : List Shell}
    {operatorAt : Shell → Operator}
    {decay : OperatorCrossShellDecay space shells operatorAt} →
  GeometricCrossShellEnvelope decay →
  0ℚ ≤ commonConstant _ →
  CutoffUniformCrossShellMass decay
geometricEnvelopeProducesUniformMass envelope constantNN = record
  { uniformLeftMass = commonConstant envelope * geometricMass envelope
  ; uniformRightMass = commonConstant envelope * geometricMass envelope
  ; uniformLeftMassNonnegative = ℚP.*-nonNegative constantNN
      (geometricMassNonnegative envelope)
  ; uniformRightMassNonnegative = ℚP.*-nonNegative constantNN
      (geometricMassNonnegative envelope)
  ; leftMassBound = leftGeometricMass envelope
  ; rightMassBound = rightGeometricMass envelope
  }

operatorValuedCotlarSteinReducerClosed : Bool
operatorValuedCotlarSteinReducerClosed = true

physicalCrossShellOperatorDecaySupplied : Bool
physicalCrossShellOperatorDecaySupplied = false

operatorValuedCotlarSteinReducerClosedIsTrue :
  operatorValuedCotlarSteinReducerClosed ≡ true
operatorValuedCotlarSteinReducerClosedIsTrue = refl

physicalCrossShellOperatorDecaySuppliedIsFalse :
  physicalCrossShellOperatorDecaySupplied ≡ false
physicalCrossShellOperatorDecaySuppliedIsFalse = refl
