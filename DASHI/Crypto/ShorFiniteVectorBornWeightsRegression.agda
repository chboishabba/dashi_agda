module DASHI.Crypto.ShorFiniteVectorBornWeightsRegression where

open import DASHI.Core.Prelude
open import Data.Fin.Base using (Fin)

import DASHI.Algebra.Quantum.ShorCyclicPhaseAmplitudeQFTExact as Phase
import DASHI.Algebra.Quantum.ShorFiniteVectorAmplitudeRegisterExact as Vector
import DASHI.Crypto.ShorFiniteVectorBornWeightsExact as Born

------------------------------------------------------------------------
-- RED regression.
--
-- Q4 must be attached to the exact preferred finite-vector state.  Exponent
-- outcome weight is the finite sum of coefficient norm-squares across target
-- columns, and total weight is the finite sum of those exponent-row weights.
------------------------------------------------------------------------

rowWeightUsesExactRow :
  ∀ {Q N Coefficient Weight}
    {A : Phase.CyclicPhaseCoefficientAuthority Coefficient Q}
    (W : Born.CoefficientBornWeightAuthority A Weight)
    (state : Vector.VectorAmplitudeState Q N A)
    (outcome : Fin Q) →
  Born.exponentWeight W state outcome
  ≡ Born.sumTargetWeights W state outcome
rowWeightUsesExactRow W state outcome = refl

totalWeightUsesAllExponentRows :
  ∀ {Q N Coefficient Weight}
    {A : Phase.CyclicPhaseCoefficientAuthority Coefficient Q}
    (W : Born.CoefficientBornWeightAuthority A Weight)
    (state : Vector.VectorAmplitudeState Q N A) →
  Born.totalVectorWeight W state
  ≡ Born.sumExponentWeights W state
 totalWeightUsesAllExponentRows W state = refl
