module DASHI.Crypto.ShorFiniteVectorBornNonnegativeRegression where

open import DASHI.Core.Prelude
open import Data.Fin.Base using (Fin)

import DASHI.Algebra.Quantum.ShorCyclicPhaseAmplitudeQFTExact as Phase
import DASHI.Algebra.Quantum.ShorFiniteVectorAmplitudeRegisterExact as Vector
import DASHI.Crypto.ShorFiniteVectorBornWeightsExact as Weights
import DASHI.Crypto.ShorFiniteVectorBornProbabilityExact as Born
import DASHI.Crypto.ShorFiniteVectorBornNonnegativeExact as Nonnegative

------------------------------------------------------------------------
-- RED regression.
--
-- A normalized finite weight family is not yet a probability law unless its
-- entries are known nonnegative.  The exact Shor row probability must inherit
-- nonnegativity constructively from coefficient norm-squares, finite addition,
-- and admissible division.
------------------------------------------------------------------------

bornOutcomeProbabilityIsNonnegative :
  ∀ {Q N : Nat}
    {Coefficient Weight : Set}
    {A : Phase.CyclicPhaseCoefficientAuthority Coefficient Q}
    {W : Weights.CoefficientBornWeightAuthority A Weight}
    (D : Born.FiniteBornDivisionAuthority W)
    (O : Nonnegative.FiniteBornNonnegativeAuthority D)
    (state : Vector.VectorAmplitudeState Q N A)
    (positiveTotal : Born.PositiveTotalWeight D state)
    (outcome : Fin Q) →
  Nonnegative.Nonnegative O
    (Born.exponentProbability D state positiveTotal outcome)
bornOutcomeProbabilityIsNonnegative D O state positiveTotal outcome =
  Nonnegative.exponentProbabilityNonnegative
    D O state positiveTotal outcome
