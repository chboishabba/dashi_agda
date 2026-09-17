module DASHI.Crypto.ShorFiniteVectorBornWeightsExact where

open import DASHI.Core.Prelude
open import Data.Fin.Base using (Fin)
open import Data.List.Base using (List; []; _∷_; allFin)

import DASHI.Algebra.Quantum.ShorCyclicPhaseAmplitudeQFTExact as Phase
import DASHI.Algebra.Quantum.ShorFiniteVectorAmplitudeRegisterExact as Vector

------------------------------------------------------------------------
-- Q4: BORN-WEIGHT DECOMPOSITION ON THE EXACT SHOR VECTOR CARRIER
--
-- Existing repository precedent (`DASHI.Quantum.TSVF`) separates scalar
-- amplitudes, norm-squared weights, total measurement weight and normalization.
-- This owner specializes only the first two finite combinatorial layers to the
-- preferred Shor carrier itself; it does NOT identify the TSVF state carrier
-- with the Shor carrier.
--
-- For state psi : Vec (Vec Coefficient (N+1)) Q:
--
--   exponentWeight(psi,k) = sum_y ||psi[k,y]||^2
--   totalVectorWeight(psi) = sum_k exponentWeight(psi,k).
--
-- The coefficient-to-weight map and weight addition are explicit authority
-- inputs.  No division, positivity, probability normalization, random sampler,
-- or success lower bound is manufactured here.
------------------------------------------------------------------------

record CoefficientBornWeightAuthority
    {Q : Nat}
    {Coefficient : Set}
    (A : Phase.CyclicPhaseCoefficientAuthority Coefficient Q)
    (Weight : Set) : Set₁ where
  constructor coefficientBornWeightAuthority
  field
    zeroWeight : Weight
    addWeight : Weight → Weight → Weight
    normSquared : Coefficient → Weight
    zeroCoefficientWeight :
      normSquared (Phase.zeroCoefficient A) ≡ zeroWeight

open CoefficientBornWeightAuthority public

sumWeights :
  ∀ {Q Coefficient Weight}
    {A : Phase.CyclicPhaseCoefficientAuthority Coefficient Q} →
  CoefficientBornWeightAuthority A Weight →
  ∀ {I : Set} →
  (I → Weight) →
  List I →
  Weight
sumWeights W term [] = zeroWeight W
sumWeights W term (i ∷ is) =
  addWeight W (term i) (sumWeights W term is)

sumTargetWeights :
  ∀ {Q N Coefficient Weight}
    {A : Phase.CyclicPhaseCoefficientAuthority Coefficient Q} →
  CoefficientBornWeightAuthority A Weight →
  Vector.VectorAmplitudeState Q N A →
  Fin Q →
  Weight
sumTargetWeights {N = N} W state outcome =
  sumWeights W
    (λ target →
      normSquared W
        (Vector.tableLookup
          (Vector.amplitudeTable state)
          outcome
          target))
    (allFin (suc N))

exponentWeight :
  ∀ {Q N Coefficient Weight}
    {A : Phase.CyclicPhaseCoefficientAuthority Coefficient Q} →
  CoefficientBornWeightAuthority A Weight →
  Vector.VectorAmplitudeState Q N A →
  Fin Q →
  Weight
exponentWeight = sumTargetWeights

sumExponentWeights :
  ∀ {Q N Coefficient Weight}
    {A : Phase.CyclicPhaseCoefficientAuthority Coefficient Q} →
  CoefficientBornWeightAuthority A Weight →
  Vector.VectorAmplitudeState Q N A →
  Weight
sumExponentWeights {Q = Q} W state =
  sumWeights W
    (exponentWeight W state)
    (allFin Q)

totalVectorWeight :
  ∀ {Q N Coefficient Weight}
    {A : Phase.CyclicPhaseCoefficientAuthority Coefficient Q} →
  CoefficientBornWeightAuthority A Weight →
  Vector.VectorAmplitudeState Q N A →
  Weight
totalVectorWeight = sumExponentWeights

------------------------------------------------------------------------
-- Boundary / WrongType firewalls.
------------------------------------------------------------------------

data FiniteWeightsCreateProbabilityDistribution : Set where

data NonzeroSupportCreatesPositiveProbability : Set where

data WeightDecompositionCreatesSamplingLaw : Set where

finiteWeightsDoNotCreateProbabilityDistribution :
  FiniteWeightsCreateProbabilityDistribution → ⊥
finiteWeightsDoNotCreateProbabilityDistribution ()

nonzeroSupportDoesNotCreatePositiveProbability :
  NonzeroSupportCreatesPositiveProbability → ⊥
nonzeroSupportDoesNotCreatePositiveProbability ()

weightDecompositionDoesNotCreateSamplingLaw :
  WeightDecompositionCreatesSamplingLaw → ⊥
weightDecompositionDoesNotCreateSamplingLaw ()

record ShorFiniteVectorBornWeightsBoundary : Set where
  constructor shorFiniteVectorBornWeightsBoundary
  field
    exactShorVectorCarrierUsed : Bool
    targetColumnWeightsSummed : Bool
    exponentRowWeightsSummed : Bool
    totalFiniteWeightConstructed : Bool
    coefficientNormSquaredConcreteHere : Bool
    totalWeightPositiveProvedHere : Bool
    normalizedProbabilityConstructedHere : Bool
    randomOutcomeSamplerConstructedHere : Bool
    successProbabilityLowerBoundProvedHere : Bool

canonicalShorFiniteVectorBornWeightsBoundary :
  ShorFiniteVectorBornWeightsBoundary
canonicalShorFiniteVectorBornWeightsBoundary =
  shorFiniteVectorBornWeightsBoundary
    true true true true false false false false false
