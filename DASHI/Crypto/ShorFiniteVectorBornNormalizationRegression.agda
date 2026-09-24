module DASHI.Crypto.ShorFiniteVectorBornNormalizationRegression where

open import DASHI.Core.Prelude

import DASHI.Algebra.Quantum.ShorCyclicPhaseAmplitudeQFTExact as Phase
import DASHI.Algebra.Quantum.ShorFiniteVectorAmplitudeRegisterExact as Vector
import DASHI.Crypto.ShorFiniteVectorBornWeightsExact as Weights
import DASHI.Crypto.ShorFiniteVectorBornProbabilityExact as Born
import DASHI.Crypto.ShorFiniteVectorBornNormalizationExact as Normalize

------------------------------------------------------------------------
-- RED regression.
--
-- Normalization is not an axiom of the Shor probability owner.  Given only
-- the explicit finite quotient algebra needed to commute a common denominator
-- through the finite sum and reduce W/W to one, the exact same-carrier outcome
-- probabilities must sum to the supplied multiplicative unit.
------------------------------------------------------------------------

finiteBornProbabilitiesNormalize :
  ∀ {Q N Coefficient Weight}
    {A : Phase.CyclicPhaseCoefficientAuthority Coefficient Q}
    {W : Weights.CoefficientBornWeightAuthority A Weight}
    (D : Born.FiniteBornDivisionAuthority W)
    (L : Normalize.FiniteBornNormalizationAlgebra D)
    (state : Vector.VectorAmplitudeState Q N A)
    (positiveTotal : Born.PositiveTotalWeight D state) →
  Normalize.sumExponentProbabilities D state positiveTotal
  ≡ Normalize.oneWeight L
finiteBornProbabilitiesNormalize D L state positiveTotal =
  Normalize.sumExponentProbabilitiesIsOne D L state positiveTotal
