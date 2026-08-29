module DASHI.Physics.YangMills.BalabanNormalizedExpectationCrossNumeratorExact where

------------------------------------------------------------------------
-- ROUND82: DIVISION-FREE NORMALIZED-EXPECTATION CANCELLATION ALGEBRA
--
-- This is the finite algebra sitting underneath the CMP119 (3.44)--(3.47)
-- exponentiated-cluster cancellation.  If N/Z and N'/Z' are two normalized
-- expectations, their difference has cross numerator
--
--                 N' Z - N Z'.
--
-- A factor carried identically by the perturbed numerator and denominator pulls
-- out of this cross numerator.  Hence disconnected vacuum factors cannot create
-- a new connected response; only the factor touching the distinguished
-- insertion can survive after normalization.  CMP119 supplies the nontrivial
-- polymer exponentiation/localization theorem which realizes this algebra on
-- the actual gauge density.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_)
open import Data.Rational.Base as ℚ using (ℚ; _*_; _-_)
open import Data.Rational.Tactic.RingSolver as ℚRing

open import DASHI.Physics.YangMills.CompactLieProofLevel

normalizedCrossNumerator : ℚ → ℚ → ℚ → ℚ → ℚ
normalizedCrossNumerator baseNumerator baseDenominator
  newNumerator newDenominator =
  newNumerator * baseDenominator - baseNumerator * newDenominator

disconnectedCommonFactorPullsOut : ∀ factor baseNumerator baseDenominator
  newNumerator newDenominator →
  normalizedCrossNumerator baseNumerator baseDenominator
    (factor * newNumerator) (factor * newDenominator)
  ≡ factor * normalizedCrossNumerator baseNumerator baseDenominator
      newNumerator newDenominator
disconnectedCommonFactorPullsOut =
  ℚRing.solve-∀

nestedDisconnectedFactorsPullOut : ∀ first second baseNumerator baseDenominator
  newNumerator newDenominator →
  normalizedCrossNumerator baseNumerator baseDenominator
    (first * (second * newNumerator))
    (first * (second * newDenominator))
  ≡ (first * second)
      * normalizedCrossNumerator baseNumerator baseDenominator
          newNumerator newDenominator
nestedDisconnectedFactorsPullOut =
  ℚRing.solve-∀

normalizedExpectationCrossNumeratorLevel : ProofLevel
normalizedExpectationCrossNumeratorLevel = machineChecked
