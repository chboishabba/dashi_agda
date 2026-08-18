module DASHI.Physics.Closure.NSTriadKNPeriodicQMeanZeroLocalityBoundaryRound85Exact where

------------------------------------------------------------------------
-- PRIMARY SOURCES / CONTEXT
--
-- Authors: Jinhee Jeong; Fazle Hussain.
-- Title: "On the identification of a vortex".
-- Journal of Fluid Mechanics 285 (1995), 69--94.
-- DOI: 10.1017/S0022112095000462.
--
-- Authors: Karthik Menon; Rajat Mittal.
-- Title: "Significance of the strain-dominated region around a vortex on
-- induced aerodynamic loads".
-- Journal of Fluid Mechanics 918 (2021), R3.
-- DOI: 10.1017/jfm.2021.359.
--
-- ROUND85 / PERIODIC Q MEAN-ZERO: EXACT USE AND EXACT LIMITATION
--
-- On a periodic domain the spatial integral of Delta p vanishes.  Combined
-- with the exact Q normalization
--
--   Delta p = 2 Q,
--
-- this gives
--
--   integral Q = 0.
--
-- The first half of this module proves the arithmetic reducer exactly: once a
-- selected periodic pressure/Q realization supplies the two source equalities,
-- the Q mean is forced to zero.
--
-- The second half records the crucial authority boundary for C5.  A zero-sum
-- scalar law has NO spectral-locality content by itself.  For every proposed
-- finite shell radius r, the exact two-shell charge
--
--   +1 at the selected shell,
--   -1 at shell suc r
--
-- has total zero while its compensator lies outside r.  Thus periodic
-- integral-Q zero cannot, without an additional localization theorem, fund a
-- bounded-neighbour-shell replenishment claim.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using ([]; _∷_)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Data.Empty using (⊥)
import Data.Integer.Base as Int
open import Data.Rational.Base using (ℚ; 0ℚ; _/_; _+_; _*_; -_)
open import Data.Rational.Tactic.RingSolver using (solve)
open import Relation.Binary.PropositionalEquality using (cong; sym; trans)

------------------------------------------------------------------------
-- Exact periodic mean-Q arithmetic reducer.
------------------------------------------------------------------------

two : ℚ
two = Int.+ 2 / 1

half : ℚ
half = Int.+ 1 / 2

record PeriodicQMeanPoissonDatum : Set where
  field
    pressureLaplacianMean qMean : ℚ

    periodicLaplacianMeanZero : pressureLaplacianMean ≡ 0ℚ
    pressurePoissonMean : pressureLaplacianMean ≡ two * qMean

open PeriodicQMeanPoissonDatum public

periodicQMeanZero :
  (datum : PeriodicQMeanPoissonDatum) → qMean datum ≡ 0ℚ
periodicQMeanZero datum =
  let
    twoQZero : two * qMean datum ≡ 0ℚ
    twoQZero = trans (sym (pressurePoissonMean datum))
      (periodicLaplacianMeanZero datum)

    halfScaled : half * (two * qMean datum) ≡ half * 0ℚ
    halfScaled = cong (half *_) twoQZero

    leftIsQ : half * (two * qMean datum) ≡ qMean datum
    leftIsQ = solve (qMean datum ∷ [])

    rightIsZero : half * 0ℚ ≡ 0ℚ
    rightIsZero = solve []
  in
  trans (sym leftIsQ) (trans halfScaled rightIsZero)

------------------------------------------------------------------------
-- Zero total does not imply bounded shell locality.
------------------------------------------------------------------------

data _≤ᴺ_ : Nat → Nat → Set where
  zero≤ : ∀ {n} → zero ≤ᴺ n
  suc≤ : ∀ {m n} → m ≤ᴺ n → suc m ≤ᴺ suc n

notSuccessorWithinSelf : ∀ radius → suc radius ≤ᴺ radius → ⊥
notSuccessorWithinSelf zero ()
notSuccessorWithinSelf (suc radius) (suc≤ proof) =
  notSuccessorWithinSelf radius proof

record GlobalZeroForcesCompensationWithin (radius : Nat) : Set where
  field
    forceWithin :
      (compensationShell : Nat)
      (positiveCharge negativeCharge : ℚ) →
      positiveCharge + negativeCharge ≡ 0ℚ →
      compensationShell ≤ᴺ radius

open GlobalZeroForcesCompensationWithin public

selectedCharge : ℚ
selectedCharge = Int.+ 1 / 1

compensatingCharge : ℚ
compensatingCharge = - selectedCharge

twoShellChargeSumsToZero : selectedCharge + compensatingCharge ≡ 0ℚ
twoShellChargeSumsToZero = solve []

globalZeroCannotForceAnyFiniteCompensationRadius :
  ∀ radius → GlobalZeroForcesCompensationWithin radius → ⊥
globalZeroCannotForceAnyFiniteCompensationRadius radius candidate =
  notSuccessorWithinSelf radius
    (forceWithin candidate
      (suc radius)
      selectedCharge compensatingCharge
      twoShellChargeSumsToZero)

round85PeriodicQMeanZeroReducerConstructed : Bool
round85PeriodicQMeanZeroReducerConstructed = true

round85GlobalQMeanZeroImpliesBoundedShellCompensation : Bool
round85GlobalQMeanZeroImpliesBoundedShellCompensation = false

round85PeriodicQMeanZeroReducerConstructedIsTrue :
  round85PeriodicQMeanZeroReducerConstructed ≡ true
round85PeriodicQMeanZeroReducerConstructedIsTrue = refl

round85GlobalQMeanZeroImpliesBoundedShellCompensationIsFalse :
  round85GlobalQMeanZeroImpliesBoundedShellCompensation ≡ false
round85GlobalQMeanZeroImpliesBoundedShellCompensationIsFalse = refl
