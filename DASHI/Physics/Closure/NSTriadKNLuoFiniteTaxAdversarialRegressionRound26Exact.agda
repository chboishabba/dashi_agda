module DASHI.Physics.Closure.NSTriadKNLuoFiniteTaxAdversarialRegressionRound26Exact where

------------------------------------------------------------------------
-- PRIMARY SOURCES / CONTEXT
--
-- Author: Terence Tao.
-- Title: "Why global regularity for Navier-Stokes is hard".
-- Publication: expository article, 2007; no DOI assigned.
--
-- Authors: Hajer Bahouri; Jean-Yves Chemin; Raphael Danchin.
-- Title: "Fourier Analysis and Nonlinear Partial Differential Equations".
-- DOI: 10.1007/978-3-642-16830-7.
--
-- DASHI CONTRIBUTION
--
-- Exact finite regressions accompany every proposed tax.  These examples show
-- why the signed ledger must be preserved until cancellation is exhausted and
-- why duplicate ownership is forbidden:
--
--   (+1) + (-1) = 0,
--   taxing both magnitudes gives 2,
--   counting one unit atom under two owners also gives 2.
--
-- They do not refute a correctly grouped estimate.  They reject two common
-- proof transformations before continuum analysis begins.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.List using ([]; _∷_)
import Data.Integer.Base as Int
open import Data.Rational.Base using (ℚ; _/_; _+_; _-_; _*_)
open import Data.Rational.Tactic.RingSolver using (solve)

zero one two : ℚ
zero = Int.+ 0 / 1
one = Int.+ 1 / 1
two = Int.+ 2 / 1

negativeOne : ℚ
negativeOne = zero - one

signedCancellationExample : one + negativeOne ≡ zero
signedCancellationExample = solve []

magnitudeTaxAfterEarlyAbsoluteValue : one + one ≡ two
magnitudeTaxAfterEarlyAbsoluteValue = solve []

record DuplicateOwnershipExample : Set where
  constructor duplicate-ownership-example
  field
    originalAtom : ℚ
    firstOwnerCharge : ℚ
    secondOwnerCharge : ℚ
    firstOwnerCopiesAtom : firstOwnerCharge ≡ originalAtom
    secondOwnerCopiesAtom : secondOwnerCharge ≡ originalAtom

open DuplicateOwnershipExample public

duplicateOwnershipDoublesUnitAtom :
  (example : DuplicateOwnershipExample) →
  originalAtom example ≡ one →
  firstOwnerCharge example + secondOwnerCharge example ≡ two
duplicateOwnershipDoublesUnitAtom example originalIsOne
  rewrite firstOwnerCopiesAtom example
        | secondOwnerCopiesAtom example
        | originalIsOne =
  solve []

------------------------------------------------------------------------
-- One signed pair can be globally conservative while both local positive
-- projections are nonzero.  Hence classwise positive parts may be strictly
-- more expensive than the signed class sum.
------------------------------------------------------------------------

record SignedPair : Set where
  constructor signed-pair
  field
    left right : ℚ
    signedZero : left + right ≡ zero

open SignedPair public

canonicalOppositePair : SignedPair
canonicalOppositePair = signed-pair one negativeOne signedCancellationExample

canonicalOppositePairSignedSumZero :
  left canonicalOppositePair + right canonicalOppositePair ≡ zero
canonicalOppositePairSignedSumZero = signedZero canonicalOppositePair

canonicalOppositePairSeparateMagnitudeTwo : one + one ≡ two
canonicalOppositePairSeparateMagnitudeTwo = magnitudeTaxAfterEarlyAbsoluteValue

------------------------------------------------------------------------
-- A remainder-free zero-budget estimate cannot pay a positive atom.  The
-- exact arithmetic surface below is used by finite search scripts as a guard:
-- any candidate class tax with D=X=R=0 and production=1 has a zero right side.
------------------------------------------------------------------------

zeroBudget : ℚ → ℚ → ℚ → ℚ → ℚ
zeroBudget eta dissipation coefficient reservoir =
  eta * dissipation + coefficient * reservoir

zeroBudgetIsZero :
  (eta coefficient : ℚ) →
  zeroBudget eta zero coefficient zero ≡ zero
zeroBudgetIsZero eta coefficient = solve (eta ∷ coefficient ∷ [])
