module DASHI.Physics.Closure.NSTriadKNLuoCenteredPairedCommutatorIdentityExact where

------------------------------------------------------------------------
-- PROVENANCE
--
-- Authors: Peter Constantin; Weinan E; Edriss S. Titi.
-- Title: "Onsager's Conjecture on the Energy Conservation for Solutions of
-- Euler's Equation".
-- DOI: 10.1007/BF02099744.
--
-- Author: Piero D'Ancona.
-- Title: "A Short Proof of Commutator Estimates".
-- DOI: 10.1007/s00041-018-9612-8.
-- Correction DOI: 10.1007/s00041-019-09724-7.
--
-- PURPOSE
-- Prove the exact paired-difference identity used by the centered low--high
-- commutator.  Pairing the y and -y kernel samples gives
--
--   (a_- - a_0) g_- + (a_+ - a_0) g_+
--     = (a_- - 2 a_0 + a_+) g_-
--       + (a_+ - a_0) (g_+ - g_-).
--
-- The first term carries a second difference of the low field; the second
-- moves one difference onto the high field.  This is the algebraic source of
-- the two Taylor branches in the (6,3) exponent table.  The identity is proved
-- both pointwise and after arbitrary finite weighted summation.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.List using (List; []; _∷_)
open import Data.Rational.Base using (ℚ; 0ℚ; _+_; _*_; _-_)
open import Data.Rational.Tactic.RingSolver using (solve)

record PairedCommutatorSample : Set where
  constructor paired-commutator-sample
  field
    kernelWeight : ℚ
    aMinus aCenter aPlus : ℚ
    gMinus gPlus : ℚ

open PairedCommutatorSample public

rawPair : PairedCommutatorSample → ℚ
rawPair sample =
  (aMinus sample - aCenter sample) * gMinus sample
  + (aPlus sample - aCenter sample) * gPlus sample

centeredLowBranch : PairedCommutatorSample → ℚ
centeredLowBranch sample =
  (aMinus sample - (aCenter sample + aCenter sample) + aPlus sample)
  * gMinus sample

highDifferenceBranch : PairedCommutatorSample → ℚ
highDifferenceBranch sample =
  (aPlus sample - aCenter sample)
  * (gPlus sample - gMinus sample)

pairedCommutatorIdentity :
  (sample : PairedCommutatorSample) →
  rawPair sample
  ≡ centeredLowBranch sample + highDifferenceBranch sample
pairedCommutatorIdentity sample =
  solve
    ( aMinus sample
    ∷ aCenter sample
    ∷ aPlus sample
    ∷ gMinus sample
    ∷ gPlus sample
    ∷ [])

weightedRawPair : PairedCommutatorSample → ℚ
weightedRawPair sample = kernelWeight sample * rawPair sample

weightedCenteredBranch : PairedCommutatorSample → ℚ
weightedCenteredBranch sample =
  kernelWeight sample * centeredLowBranch sample

weightedHighDifferenceBranch : PairedCommutatorSample → ℚ
weightedHighDifferenceBranch sample =
  kernelWeight sample * highDifferenceBranch sample

weightedPairedCommutatorIdentity :
  (sample : PairedCommutatorSample) →
  weightedRawPair sample
  ≡ weightedCenteredBranch sample
    + weightedHighDifferenceBranch sample
weightedPairedCommutatorIdentity sample
  rewrite pairedCommutatorIdentity sample =
  solve
    ( kernelWeight sample
    ∷ centeredLowBranch sample
    ∷ highDifferenceBranch sample
    ∷ [])

sumBy :
  ∀ {A : Set} →
  List A →
  (A → ℚ) →
  ℚ
sumBy [] value = 0ℚ
sumBy (item ∷ items) value = value item + sumBy items value

finiteWeightedPairedCommutatorIdentity :
  (samples : List PairedCommutatorSample) →
  sumBy samples weightedRawPair
  ≡ sumBy samples weightedCenteredBranch
    + sumBy samples weightedHighDifferenceBranch
finiteWeightedPairedCommutatorIdentity [] = solve []
finiteWeightedPairedCommutatorIdentity (sample ∷ samples)
  rewrite weightedPairedCommutatorIdentity sample
        | finiteWeightedPairedCommutatorIdentity samples =
  solve
    ( weightedCenteredBranch sample
    ∷ weightedHighDifferenceBranch sample
    ∷ sumBy samples weightedCenteredBranch
    ∷ sumBy samples weightedHighDifferenceBranch
    ∷ [])
