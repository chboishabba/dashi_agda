module DASHI.Physics.Closure.NSTriadKNComGramOperatorMismatchRound53Exact where

------------------------------------------------------------------------
-- PRIMARY SOURCES / CONTEXT
--
-- Authors: Mischa Cotlar; Elias M. Stein.
-- Title: "A unified theory of Hilbert transforms and ergodic theorems".
-- Proceedings of the Symposium on Ergodic Theory, 1955.
-- DOI: no DOI assigned to the cited historical conference article.
--
-- Authors: Tosio Kato; Gustavo Ponce.
-- Title: "Commutator Estimates and the Euler and Navier-Stokes Equations".
-- DOI: 10.1002/cpa.3160410704.
--
-- Authors: Hajer Bahouri; Jean-Yves Chemin; Raphael Danchin.
-- Title: "Fourier Analysis and Nonlinear Partial Differential Equations".
-- DOI: 10.1007/978-3-642-16830-7.
--
-- DASHI CONTRIBUTION
--
-- Round 52 left one potentially catastrophic type/constant ambiguity: the
-- stored `pairProduct` belongs to a Gram/Cotlar lane, while 17/64 and 65/512
-- were tempting to read as direct shell-operator norms.
--
-- This file proves an exact rational counterexample showing why that promotion
-- is invalid in general.  From
--
--   blockNorm^2 <= gramBound
--
-- one cannot conclude
--
--   blockNorm <= gramBound.
--
-- The witness blockNorm=1/2, gramBound=1/4 satisfies the squared inequality
-- with equality but violates the unsquared inequality.  Therefore Round 53
-- freezes the correct physical fork:
--
--   (A) prove pairProduct majorizes the WHOLE unsquared shell-block norm; or
--   (B) keep pairProduct as a Gram quantity and let the Cotlar square-root
--       conversion occur at the operator layer.
--
-- No 17/64 or 65/512 constant is promoted across that fork without a typed
-- same-object theorem.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
import Data.Integer.Base as Int
open import Data.Rational.Base using (ℚ; _/_; _*_; _≤_; _<_)
import Data.Rational.Properties as ℚP
open ℚP using (_≤?_; _<?_)
open import Data.Rational.Tactic.RingSolver using (solve)
open import Relation.Nullary.Decidable.Core using (toWitness)

half quarter : ℚ
half = Int.+ 1 / 2
quarter = Int.+ 1 / 4

halfSquaredIsQuarter : half * half ≡ quarter
halfSquaredIsQuarter = solve []

halfSquaredBelowQuarter : half * half ≤ quarter
halfSquaredBelowQuarter rewrite halfSquaredIsQuarter = ℚP.≤-refl

quarterStrictlyBelowHalf : quarter < half
quarterStrictlyBelowHalf =
  toWitness {a? = quarter <? half} _

record SquaredGramMajorantWitness : Set where
  field
    blockNorm gramBound : ℚ
    squaredBlockNormBelowGram : blockNorm * blockNorm ≤ gramBound

open SquaredGramMajorantWitness public

counterexampleWitness : SquaredGramMajorantWitness
counterexampleWitness = record
  { blockNorm = half
  ; gramBound = quarter
  ; squaredBlockNormBelowGram = halfSquaredBelowQuarter
  }

counterexampleUnsquaredPromotionFails :
  gramBound counterexampleWitness < blockNorm counterexampleWitness
counterexampleUnsquaredPromotionFails = quarterStrictlyBelowHalf

data ComConstantMeaning : Set where
  wholeBlockNormMajorant : ComConstantMeaning
  gramProductMajorant : ComConstantMeaning

physicalComConstantMeaningResolved : Bool
physicalComConstantMeaningResolved = false

gramToOperatorPromotionWithoutSquareRootIsInvalid : Bool
gramToOperatorPromotionWithoutSquareRootIsInvalid = true

gramToOperatorPromotionWithoutSquareRootIsInvalidIsTrue :
  gramToOperatorPromotionWithoutSquareRootIsInvalid ≡ true
gramToOperatorPromotionWithoutSquareRootIsInvalidIsTrue = refl
