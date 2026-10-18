module DASHI.Crypto.ShorFiniteVectorBornProbabilityExact where

open import DASHI.Core.Prelude
open import Data.Fin.Base using (Fin)

import DASHI.Algebra.Quantum.ShorCyclicPhaseAmplitudeQFTExact as Phase
import DASHI.Algebra.Quantum.ShorFiniteVectorAmplitudeRegisterExact as Vector
import DASHI.Crypto.ShorFiniteVectorBornWeightsExact as Weights

------------------------------------------------------------------------
-- Q4: NORMALIZED BORN-WEIGHT RATIO ON THE EXACT SHOR VECTOR CARRIER
--
-- The preceding owner constructs, on the preferred Shor state itself,
--
--   w(psi,k) = sum_y ||psi[k,y]||^2
--   W(psi)   = sum_k w(psi,k).
--
-- This owner pays only the next compiler seam.  A caller supplies the weight
-- division operation and the proposition saying when a denominator is
-- admissible for that operation.  Once W(psi) carries such a witness, the
-- exponent probability is definitionally
--
--   p(psi,k) = w(psi,k) / W(psi).
--
-- No theorem that the probabilities sum to one, no random sampler, and no
-- Shor success-probability lower bound is manufactured here.  Those remain
-- separate laws/producers.
------------------------------------------------------------------------

record FiniteBornDivisionAuthority
    {Q : Nat}
    {Coefficient Weight : Set}
    {A : Phase.CyclicPhaseCoefficientAuthority Coefficient Q}
    (W : Weights.CoefficientBornWeightAuthority A Weight) : Set₁ where
  constructor finiteBornDivisionAuthority
  field
    divideWeight : Weight → Weight → Weight
    admissibleDenominatorWeight : Weight → Set

open FiniteBornDivisionAuthority public

PositiveTotalWeight :
  ∀ {Q N Coefficient Weight}
    {A : Phase.CyclicPhaseCoefficientAuthority Coefficient Q}
    {W : Weights.CoefficientBornWeightAuthority A Weight} →
  (D : FiniteBornDivisionAuthority W) →
  Vector.VectorAmplitudeState Q N A →
  Set
PositiveTotalWeight {W = W} D state =
  admissibleDenominatorWeight D (Weights.totalVectorWeight W state)

exponentProbability :
  ∀ {Q N Coefficient Weight}
    {A : Phase.CyclicPhaseCoefficientAuthority Coefficient Q}
    {W : Weights.CoefficientBornWeightAuthority A Weight} →
  (D : FiniteBornDivisionAuthority W) →
  (state : Vector.VectorAmplitudeState Q N A) →
  PositiveTotalWeight D state →
  Fin Q →
  Weight
exponentProbability {W = W} D state positiveTotal outcome =
  divideWeight D
    (Weights.exponentWeight W state outcome)
    (Weights.totalVectorWeight W state)

------------------------------------------------------------------------
-- Boundary / WrongType firewalls.
------------------------------------------------------------------------

data NormalizedRatiosCreateNormalizationProof : Set where

data PositiveTotalCreatesRandomSampler : Set where

data NormalizedRatiosCreateShorSuccessBound : Set where

normalizedRatiosDoNotCreateNormalizationProof :
  NormalizedRatiosCreateNormalizationProof → ⊥
normalizedRatiosDoNotCreateNormalizationProof ()

positiveTotalDoesNotCreateRandomSampler :
  PositiveTotalCreatesRandomSampler → ⊥
positiveTotalDoesNotCreateRandomSampler ()

normalizedRatiosDoNotCreateShorSuccessBound :
  NormalizedRatiosCreateShorSuccessBound → ⊥
normalizedRatiosDoNotCreateShorSuccessBound ()

record ShorFiniteVectorBornProbabilityBoundary : Set where
  constructor shorFiniteVectorBornProbabilityBoundary
  field
    exactShorVectorWeightsReused : Bool
    denominatorAdmissibilityExplicit : Bool
    normalizedRowWeightConstructed : Bool
    probabilityNormalizationProvedHere : Bool
    randomOutcomeSamplerConstructedHere : Bool
    continuedFractionSuccessBoundProvedHere : Bool
    factoringSuccessBoundProvedHere : Bool

canonicalShorFiniteVectorBornProbabilityBoundary :
  ShorFiniteVectorBornProbabilityBoundary
canonicalShorFiniteVectorBornProbabilityBoundary =
  shorFiniteVectorBornProbabilityBoundary
    true true true false false false false
