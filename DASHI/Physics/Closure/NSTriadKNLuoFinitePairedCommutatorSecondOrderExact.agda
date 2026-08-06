module DASHI.Physics.Closure.NSTriadKNLuoFinitePairedCommutatorSecondOrderExact where

------------------------------------------------------------------------
-- PROVENANCE
--
-- Authors: Tosio Kato; Gustavo Ponce.
-- Title: "Commutator Estimates and the Euler and Navier--Stokes Equations".
-- Communications on Pure and Applied Mathematics 41 (1988), 891--907.
-- DOI: 10.1002/cpa.3160410704.
--
-- Authors: Peter Constantin; Weinan E; Edriss S. Titi.
-- Title: "Onsager's Conjecture on the Energy Conservation for Solutions of
-- Euler's Equation".
-- Communications in Mathematical Physics 165 (1994), 207--209.
-- DOI: 10.1007/BF02099744.
--
-- PURPOSE
-- Audit the proposed second-order centered commutator gain without silently
-- treating the transported derivative as constant.  For a paired displacement
-- y and -y, write
--
--   a_+ - a_0 = L + R_+,
--   a_- - a_0 = -L + R_-.
--
-- Then the exact paired commutator is
--
--   L (g_+ - g_-) + R_+ g_+ + R_- g_-.
--
-- The first-order transport increments cancel only against an equal derivative
-- sample.  In general a derivative-variation term survives and must be paid by
-- a second spatial increment.  This is the exact algebra needed before any
-- absolute-value or moment estimate.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.List using ([]; _∷_)
import Data.Integer.Base as Int
open import Data.Rational.Base using (ℚ; 0ℚ; 1ℚ; _/_; _+_; _*_; _-_; -_)
open import Data.Rational.Tactic.RingSolver using (solve)

record PairedCommutatorSample : Set where
  constructor paired-commutator-sample
  field
    weight centerTransport linearIncrement : ℚ
    plusRemainder minusRemainder : ℚ
    plusDerivative minusDerivative : ℚ

open PairedCommutatorSample public

plusTransport : PairedCommutatorSample → ℚ
plusTransport sample =
  centerTransport sample
  + linearIncrement sample
  + plusRemainder sample

minusTransport : PairedCommutatorSample → ℚ
minusTransport sample =
  centerTransport sample
  - linearIncrement sample
  + minusRemainder sample

pairedCommutator : PairedCommutatorSample → ℚ
pairedCommutator sample =
  weight sample
  * ( (plusTransport sample - centerTransport sample)
      * plusDerivative sample
    + (minusTransport sample - centerTransport sample)
      * minusDerivative sample
    )

pairedSecondOrderDefect : PairedCommutatorSample → ℚ
pairedSecondOrderDefect sample =
  weight sample
  * ( linearIncrement sample
      * (plusDerivative sample - minusDerivative sample)
    + plusRemainder sample * plusDerivative sample
    + minusRemainder sample * minusDerivative sample
    )

pairedCommutatorSecondOrderIdentity :
  (sample : PairedCommutatorSample) →
  pairedCommutator sample ≡ pairedSecondOrderDefect sample
pairedCommutatorSecondOrderIdentity sample =
  solve
    ( weight sample
    ∷ centerTransport sample
    ∷ linearIncrement sample
    ∷ plusRemainder sample
    ∷ minusRemainder sample
    ∷ plusDerivative sample
    ∷ minusDerivative sample
    ∷ []
    )

pairedEqualDerivativePureRemainder :
  (sample : PairedCommutatorSample) →
  plusDerivative sample ≡ minusDerivative sample →
  pairedCommutator sample
  ≡ weight sample
      * ( plusRemainder sample * plusDerivative sample
        + minusRemainder sample * minusDerivative sample
        )
pairedEqualDerivativePureRemainder sample derivativeEquality
  rewrite pairedCommutatorSecondOrderIdentity sample
        | derivativeEquality =
  solve
    ( weight sample
    ∷ linearIncrement sample
    ∷ plusDerivative sample
    ∷ minusDerivative sample
    ∷ plusRemainder sample
    ∷ minusRemainder sample
    ∷ []
    )

unitWitness : PairedCommutatorSample
unitWitness =
  paired-commutator-sample
    1ℚ 0ℚ 1ℚ 0ℚ 0ℚ 1ℚ 0ℚ

firstMomentCancellationAloneDoesNotKillCommutator :
  pairedCommutator unitWitness ≡ 1ℚ
firstMomentCancellationAloneDoesNotKillCommutator = solve []

unitWitnessDerivativeVariation :
  pairedSecondOrderDefect unitWitness ≡ 1ℚ
unitWitnessDerivativeVariation = solve []

oneHalf : ℚ
oneHalf = Int.+ 1 / 2

symmetricDerivativeWitness : PairedCommutatorSample
symmetricDerivativeWitness =
  paired-commutator-sample
    1ℚ 0ℚ 1ℚ oneHalf oneHalf 1ℚ 1ℚ

symmetricDerivativeLeavesOnlyRemainders :
  pairedCommutator symmetricDerivativeWitness ≡ 1ℚ
symmetricDerivativeLeavesOnlyRemainders = solve []
