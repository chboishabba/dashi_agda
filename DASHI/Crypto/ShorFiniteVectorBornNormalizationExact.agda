module DASHI.Crypto.ShorFiniteVectorBornNormalizationExact where

open import DASHI.Core.Prelude
open import Data.List.Base using (List; []; _∷_; allFin)
open import Relation.Binary.PropositionalEquality using (cong; sym; trans)

import DASHI.Algebra.Quantum.ShorCyclicPhaseAmplitudeQFTExact as Phase
import DASHI.Algebra.Quantum.ShorFiniteVectorAmplitudeRegisterExact as Vector
import DASHI.Crypto.ShorFiniteVectorBornWeightsExact as Weights
import DASHI.Crypto.ShorFiniteVectorBornProbabilityExact as Born

------------------------------------------------------------------------
-- Q4: FINITE NORMALIZATION FROM EXPLICIT QUOTIENT ALGEBRA
--
-- The probability owner deliberately stops at p(k) = w(k) / W.  This owner
-- isolates the exact additional algebra required to derive
--
--   sum_k p(k) = 1.
--
-- We do not assume that theorem directly.  The caller supplies only the laws
-- needed to move one admissible common denominator through a finite numerator
-- sum and to reduce W/W to the supplied unit.
------------------------------------------------------------------------

record FiniteBornNormalizationAlgebra
    {Q : Nat}
    {Coefficient Weight : Set}
    {A : Phase.CyclicPhaseCoefficientAuthority Coefficient Q}
    {W : Weights.CoefficientBornWeightAuthority A Weight}
    (D : Born.FiniteBornDivisionAuthority W) : Set₁ where
  constructor finiteBornNormalizationAlgebra
  field
    oneWeight : Weight

    zeroQuotient :
      ∀ {denominator} →
      Born.admissibleDenominatorWeight D denominator →
      Born.divideWeight D (Weights.zeroWeight W) denominator
      ≡ Weights.zeroWeight W

    addQuotient :
      ∀ {left right denominator} →
      Born.admissibleDenominatorWeight D denominator →
      Born.divideWeight D
        (Weights.addWeight W left right)
        denominator
      ≡ Weights.addWeight W
          (Born.divideWeight D left denominator)
          (Born.divideWeight D right denominator)

    selfQuotient :
      ∀ {denominator} →
      Born.admissibleDenominatorWeight D denominator →
      Born.divideWeight D denominator denominator ≡ oneWeight

open FiniteBornNormalizationAlgebra public

sumQuotients :
  ∀ {Q : Nat}
    {Coefficient Weight I : Set}
    {A : Phase.CyclicPhaseCoefficientAuthority Coefficient Q}
    {W : Weights.CoefficientBornWeightAuthority A Weight}
    (D : Born.FiniteBornDivisionAuthority W)
    (L : FiniteBornNormalizationAlgebra D)
    (term : I → Weight)
    (indices : List I)
    {denominator : Weight} →
  Born.admissibleDenominatorWeight D denominator →
  Weights.sumWeights W
    (λ i → Born.divideWeight D (term i) denominator)
    indices
  ≡ Born.divideWeight D
      (Weights.sumWeights W term indices)
      denominator
sumQuotients D L term [] positive =
  sym (zeroQuotient L positive)
sumQuotients {W = W} D L term (i ∷ is) {denominator = denominator} positive =
  trans
    (cong
      (Weights.addWeight W (Born.divideWeight D (term i) denominator))
      (sumQuotients D L term is positive))
    (sym (addQuotient L positive))

sumExponentProbabilities :
  ∀ {Q N : Nat}
    {Coefficient Weight : Set}
    {A : Phase.CyclicPhaseCoefficientAuthority Coefficient Q}
    {W : Weights.CoefficientBornWeightAuthority A Weight} →
  (D : Born.FiniteBornDivisionAuthority W) →
  (state : Vector.VectorAmplitudeState Q N A) →
  Born.PositiveTotalWeight D state →
  Weight
sumExponentProbabilities {Q = Q} {W = W} D state positiveTotal =
  Weights.sumWeights W
    (Born.exponentProbability D state positiveTotal)
    (allFin Q)

sumExponentProbabilitiesIsOne :
  ∀ {Q N : Nat}
    {Coefficient Weight : Set}
    {A : Phase.CyclicPhaseCoefficientAuthority Coefficient Q}
    {W : Weights.CoefficientBornWeightAuthority A Weight} →
  (D : Born.FiniteBornDivisionAuthority W) →
  (L : FiniteBornNormalizationAlgebra D) →
  (state : Vector.VectorAmplitudeState Q N A) →
  (positiveTotal : Born.PositiveTotalWeight D state) →
  sumExponentProbabilities D state positiveTotal ≡ oneWeight L
sumExponentProbabilitiesIsOne {Q = Q} {W = W} D L state positiveTotal =
  trans
    (sumQuotients
      D
      L
      (Weights.exponentWeight W state)
      (allFin Q)
      positiveTotal)
    (selfQuotient L positiveTotal)

------------------------------------------------------------------------
-- Boundary / WrongType firewalls.
------------------------------------------------------------------------

data NormalizationCreatesOutcomeSelection : Set where

data NormalizationCreatesIndependentSamples : Set where

data NormalizationCreatesSuccessProbability : Set where

normalizationDoesNotCreateOutcomeSelection :
  NormalizationCreatesOutcomeSelection → ⊥
normalizationDoesNotCreateOutcomeSelection ()

normalizationDoesNotCreateIndependentSamples :
  NormalizationCreatesIndependentSamples → ⊥
normalizationDoesNotCreateIndependentSamples ()

normalizationDoesNotCreateSuccessProbability :
  NormalizationCreatesSuccessProbability → ⊥
normalizationDoesNotCreateSuccessProbability ()

record ShorFiniteVectorBornNormalizationBoundary : Set where
  constructor shorFiniteVectorBornNormalizationBoundary
  field
    sameCarrierProbabilityReused : Bool
    finiteNormalizationDerived : Bool
    normalizationAssumedDirectly : Bool
    randomOutcomeSelectedHere : Bool
    sampleIndependenceProvedHere : Bool
    continuedFractionSuccessBoundProvedHere : Bool
    factoringSuccessBoundProvedHere : Bool

canonicalShorFiniteVectorBornNormalizationBoundary :
  ShorFiniteVectorBornNormalizationBoundary
canonicalShorFiniteVectorBornNormalizationBoundary =
  shorFiniteVectorBornNormalizationBoundary
    true true false false false false false
