module DASHI.Physics.Closure.NSTriadKNSignedInteractionFibreRound28Exact where

------------------------------------------------------------------------
-- PRIMARY SOURCES / CONTEXT
--
-- Author: Audrey Terras.
-- Title: "Fourier Analysis on Finite Groups and Applications".
-- DOI: 10.1017/CBO9780511626265.
--
-- Authors: Hajer Bahouri; Jean-Yves Chemin; Raphael Danchin.
-- Title: "Fourier Analysis and Nonlinear Partial Differential Equations".
-- DOI: 10.1007/978-3-642-16830-7.
--
-- DASHI CONTRIBUTION
--
-- Lift Round 27's pointwise signed translation--multiplier commutator into a
-- structured finite interaction fibre.  Every cell retains its shell label,
-- output mode, low translation, state, multiplier and test symbol.  The
-- tested fibre sum is proved exactly equal to the sum using the signed symbol
-- difference m(k)-m(k-l); no absolute row sum is inserted.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat)
open import Data.Rational.Base using (ℚ; 0ℚ; _+_; _*_)
open import Relation.Binary.PropositionalEquality using (cong; trans)

import DASHI.Physics.Closure.NSIntegerFourierLattice as Z3
import DASHI.Physics.Closure.NSTriadKNFiniteTranslationMultiplierCommutatorRound27Exact as Commutator

record SignedInteractionCell : Set where
  constructor signed-interaction-cell
  field
    shell : Nat
    output : Z3.FourierMode
    lowShift : Z3.FourierMode
    testSymbol : Commutator.MultiplierDualCarrier
    multiplier : Commutator.MultiplierDualCarrier
    state : Commutator.FourierStateCarrier

open SignedInteractionCell public

cellCommutatorValue : SignedInteractionCell → ℚ
cellCommutatorValue cell =
  Commutator.multiplierSymbol (testSymbol cell) (output cell)
  *
  Commutator.stateCoefficient
    (Commutator.translationMultiplierCommutator
      (multiplier cell) (lowShift cell) (state cell))
    (output cell)

cellSignedDifferenceValue : SignedInteractionCell → ℚ
cellSignedDifferenceValue cell =
  Commutator.multiplierSymbol (testSymbol cell) (output cell)
  *
  Commutator.stateCoefficient
    (Commutator.signedDifferenceCommutator
      (multiplier cell) (lowShift cell) (state cell))
    (output cell)

cellSignedCommutatorExact :
  (cell : SignedInteractionCell) →
  cellCommutatorValue cell ≡ cellSignedDifferenceValue cell
cellSignedCommutatorExact cell =
  cong
    (λ value →
      Commutator.multiplierSymbol
        (testSymbol cell) (output cell)
      * value)
    (Commutator.translationMultiplierCommutatorExact
      (multiplier cell) (lowShift cell) (state cell) (output cell))

interactionFibreCommutator : List SignedInteractionCell → ℚ
interactionFibreCommutator [] = 0ℚ
interactionFibreCommutator (cell ∷ rest) =
  cellCommutatorValue cell + interactionFibreCommutator rest

interactionFibreSignedDifference : List SignedInteractionCell → ℚ
interactionFibreSignedDifference [] = 0ℚ
interactionFibreSignedDifference (cell ∷ rest) =
  cellSignedDifferenceValue cell + interactionFibreSignedDifference rest

interactionFibreSignedIdentity :
  (fibre : List SignedInteractionCell) →
  interactionFibreCommutator fibre
  ≡ interactionFibreSignedDifference fibre
interactionFibreSignedIdentity [] = refl
interactionFibreSignedIdentity (cell ∷ rest) =
  trans
    (cong
      (λ value → value + interactionFibreCommutator rest)
      (cellSignedCommutatorExact cell))
    (cong
      (cellSignedDifferenceValue cell +_)
      (interactionFibreSignedIdentity rest))

signedInteractionFibreClosed : Bool
signedInteractionFibreClosed = true

finiteFibreIdentityClosed : Bool
finiteFibreIdentityClosed = true

cutoffUniformTStarTBoundClosed : Bool
cutoffUniformTStarTBoundClosed = false

signedInteractionFibreClosedIsTrue : signedInteractionFibreClosed ≡ true
signedInteractionFibreClosedIsTrue = refl

cutoffUniformTStarTBoundClosedIsFalse :
  cutoffUniformTStarTBoundClosed ≡ false
cutoffUniformTStarTBoundClosedIsFalse = refl
