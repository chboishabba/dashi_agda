module DASHI.Physics.Closure.NSTriadKNLuoFiniteEvenKernelCenteredTaylorExact where

------------------------------------------------------------------------
-- PROVENANCE
--
-- Authors: Peter Constantin; Weinan E; Edriss S. Titi.
-- Title: "Onsager's Conjecture on the Energy Conservation for Solutions of
-- Euler's Equation".
-- Communications in Mathematical Physics 165 (1994), 207--209.
-- DOI: 10.1007/BF02099744.
--
-- Authors: Hajer Bahouri; Jean-Yves Chemin; Raphael Danchin.
-- Title: "Fourier Analysis and Nonlinear Partial Differential Equations".
-- Springer, 2011.
-- DOI: 10.1007/978-3-642-16830-7.
--
-- PURPOSE
-- Prove the exact finite algebra behind the centered even-kernel gain.  A
-- symmetric pair at displacements y and -y has zero weighted first moment.
-- If the two Taylor samples have opposite linear parts, then the centered
-- pair increment contains only the two remainders.  The pointwise identity is
-- lifted to arbitrary finite paired folds; no cancellation after absolute
-- values is asserted.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Data.Rational.Base using
  (ℚ; 0ℚ; _+_; _*_; _-_; -_)
open import Data.Rational.Tactic.RingSolver using (solve)

firstMomentPair : ℚ → ℚ → ℚ
firstMomentPair weight displacement =
  weight * displacement + weight * (- displacement)

firstMomentPairCancels :
  (weight displacement : ℚ) →
  firstMomentPair weight displacement ≡ 0ℚ
firstMomentPairCancels weight displacement =
  solve (weight ∷ displacement ∷ [])

record PairedTaylorSample : Set where
  constructor paired-taylor-sample
  field
    weight center linearPart : ℚ
    plusRemainder minusRemainder : ℚ
    plusValue minusValue : ℚ

    plusMeaning :
      plusValue ≡ center + linearPart + plusRemainder
    minusMeaning :
      minusValue ≡ center - linearPart + minusRemainder

open PairedTaylorSample public

pairedCenteredIncrement : PairedTaylorSample → ℚ
pairedCenteredIncrement sample =
  weight sample
  * ( (plusValue sample - center sample)
    + (minusValue sample - center sample))

pairedRemainderContribution : PairedTaylorSample → ℚ
pairedRemainderContribution sample =
  weight sample * (plusRemainder sample + minusRemainder sample)

pairedTaylorLinearCancellation :
  (sample : PairedTaylorSample) →
  pairedCenteredIncrement sample
  ≡ pairedRemainderContribution sample
pairedTaylorLinearCancellation sample
  rewrite plusMeaning sample | minusMeaning sample =
  solve
    ( weight sample
    ∷ center sample
    ∷ linearPart sample
    ∷ plusRemainder sample
    ∷ minusRemainder sample
    ∷ []
    )

sumCenteredIncrements : List PairedTaylorSample → ℚ
sumCenteredIncrements [] = 0ℚ
sumCenteredIncrements (sample ∷ samples) =
  pairedCenteredIncrement sample + sumCenteredIncrements samples

sumRemainderContributions : List PairedTaylorSample → ℚ
sumRemainderContributions [] = 0ℚ
sumRemainderContributions (sample ∷ samples) =
  pairedRemainderContribution sample + sumRemainderContributions samples

finiteEvenKernelCenteredCancellation :
  (samples : List PairedTaylorSample) →
  sumCenteredIncrements samples ≡ sumRemainderContributions samples
finiteEvenKernelCenteredCancellation [] = refl
finiteEvenKernelCenteredCancellation (sample ∷ samples)
  rewrite pairedTaylorLinearCancellation sample
        | finiteEvenKernelCenteredCancellation samples = refl
