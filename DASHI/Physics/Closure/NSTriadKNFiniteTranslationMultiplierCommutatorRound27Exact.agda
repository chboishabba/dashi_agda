module DASHI.Physics.Closure.NSTriadKNFiniteTranslationMultiplierCommutatorRound27Exact where

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
-- Separate the Fourier state carrier from its multiplier/test dual and prove
-- the exact finite translation--multiplier commutator:
--
--   M_m T_l u - T_l M_m u
--     = M_(m - tau_l m) T_l u.
--
-- Pointwise this is the signed multiplier difference
--
--   (m(k)-m(k-l)) u(k-l),
--
-- which is the algebraic source of the low-advection commutator.  No absolute
-- value is inserted, so later TT* or square-function cancellation remains
-- available.  This theorem does not claim the cutoff-uniform operator bound.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
import Data.Integer.Base as Int
open import Data.Rational.Base using (ℚ; _/_; _+_; _-_; _*_)
open import Data.Rational.Tactic.RingSolver using (solve)

import DASHI.Physics.Closure.NSIntegerFourierLattice as Z3

record FourierStateCarrier : Set where
  constructor fourier-state-carrier
  field
    stateCoefficient : Z3.FourierMode → ℚ

open FourierStateCarrier public

record MultiplierDualCarrier : Set where
  constructor multiplier-dual-carrier
  field
    multiplierSymbol : Z3.FourierMode → ℚ

open MultiplierDualCarrier public

shiftedMode : Z3.FourierMode → Z3.FourierMode → Z3.FourierMode
shiftedMode shift output =
  Z3.addMode output (Z3.negateMode shift)

translateState : Z3.FourierMode → FourierStateCarrier → FourierStateCarrier
translateState shift state =
  fourier-state-carrier
    (λ output → stateCoefficient state (shiftedMode shift output))

applyMultiplier :
  MultiplierDualCarrier → FourierStateCarrier → FourierStateCarrier
applyMultiplier multiplier state =
  fourier-state-carrier
    (λ output →
      multiplierSymbol multiplier output * stateCoefficient state output)

translateMultiplierSymbol :
  Z3.FourierMode → MultiplierDualCarrier → MultiplierDualCarrier
translateMultiplierSymbol shift multiplier =
  multiplier-dual-carrier
    (λ output →
      multiplierSymbol multiplier (shiftedMode shift output))

multiplierDifference :
  MultiplierDualCarrier → MultiplierDualCarrier → MultiplierDualCarrier
multiplierDifference left right =
  multiplier-dual-carrier
    (λ output →
      multiplierSymbol left output - multiplierSymbol right output)

translationMultiplierCommutator :
  MultiplierDualCarrier → Z3.FourierMode →
  FourierStateCarrier → FourierStateCarrier
translationMultiplierCommutator multiplier shift state =
  fourier-state-carrier
    (λ output →
      stateCoefficient
        (applyMultiplier multiplier (translateState shift state)) output
      -
      stateCoefficient
        (translateState shift (applyMultiplier multiplier state)) output)

signedDifferenceCommutator :
  MultiplierDualCarrier → Z3.FourierMode →
  FourierStateCarrier → FourierStateCarrier
signedDifferenceCommutator multiplier shift state =
  applyMultiplier
    (multiplierDifference multiplier
      (translateMultiplierSymbol shift multiplier))
    (translateState shift state)

translationMultiplierCommutatorExact :
  ∀ multiplier shift state output →
  stateCoefficient
    (translationMultiplierCommutator multiplier shift state) output
  ≡
  stateCoefficient
    (signedDifferenceCommutator multiplier shift state) output
translationMultiplierCommutatorExact multiplier shift state output =
  solve
    ( multiplierSymbol multiplier output
    ∷ multiplierSymbol multiplier (shiftedMode shift output)
    ∷ stateCoefficient state (shiftedMode shift output)
    ∷ [])

------------------------------------------------------------------------
-- Finite state/dual pairing.  The pairing is intentionally typed separately
-- from the state itself; shell selectors and derivative symbols live in the
-- multiplier carrier rather than masquerading as additional velocity modes.
------------------------------------------------------------------------

zeroQ : ℚ
zeroQ = Int.+ 0 / 1

finitePairing :
  List Z3.FourierMode →
  MultiplierDualCarrier → FourierStateCarrier → ℚ
finitePairing [] multiplier state = zeroQ
finitePairing (mode ∷ rest) multiplier state =
  multiplierSymbol multiplier mode * stateCoefficient state mode
  + finitePairing rest multiplier state

finitePairingAppend :
  (left right : List Z3.FourierMode) →
  (multiplier : MultiplierDualCarrier) →
  (state : FourierStateCarrier) →
  finitePairing (append left right) multiplier state
  ≡ finitePairing left multiplier state
    + finitePairing right multiplier state
  where
  append : List Z3.FourierMode → List Z3.FourierMode → List Z3.FourierMode
  append [] right = right
  append (mode ∷ rest) right = mode ∷ append rest right
finitePairingAppend [] right multiplier state = solve []
finitePairingAppend (mode ∷ rest) right multiplier state
  rewrite finitePairingAppend rest right multiplier state =
  solve
    ( multiplierSymbol multiplier mode
    ∷ stateCoefficient state mode
    ∷ finitePairing rest multiplier state
    ∷ finitePairing right multiplier state
    ∷ [])

stateDualSeparationClosed : Bool
stateDualSeparationClosed = true

translationMultiplierCommutatorIdentityClosed : Bool
translationMultiplierCommutatorIdentityClosed = true

cutoffUniformSignedOperatorTaxClosed : Bool
cutoffUniformSignedOperatorTaxClosed = false
