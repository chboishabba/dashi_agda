module DASHI.Crypto.ShorFiniteVectorBornProbabilityRegression where

open import DASHI.Core.Prelude
open import Data.Fin.Base using (Fin)

import DASHI.Algebra.Quantum.ShorCyclicPhaseAmplitudeQFTExact as Phase
import DASHI.Algebra.Quantum.ShorFiniteVectorAmplitudeRegisterExact as Vector
import DASHI.Crypto.ShorFiniteVectorBornWeightsExact as Weights
import DASHI.Crypto.ShorFiniteVectorBornProbabilityExact as Born

------------------------------------------------------------------------
-- RED regression.
--
-- Once weight division and admissibility of the total weight are supplied, the
-- probability assigned to exponent k is definitionally its exact row weight
-- divided by the exact total vector weight.
------------------------------------------------------------------------

probabilityIsNormalizedRowWeight :
  ∀ {Q N Coefficient Weight}
    {A : Phase.CyclicPhaseCoefficientAuthority Coefficient Q}
    (W : Weights.CoefficientBornWeightAuthority A Weight)
    (D : Born.FiniteBornDivisionAuthority W)
    (state : Vector.VectorAmplitudeState Q N A)
    (positiveTotal : Born.PositiveTotalWeight D state)
    (outcome : Fin Q) →
  Born.exponentProbability D state positiveTotal outcome
  ≡ Born.divideWeight D
      (Weights.exponentWeight W state outcome)
      (Weights.totalVectorWeight W state)
probabilityIsNormalizedRowWeight W D state positiveTotal outcome = refl
