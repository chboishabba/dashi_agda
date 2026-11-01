module DASHI.Analysis.NonArchimedeanTotalVariationFromL2Exact where

------------------------------------------------------------------------
-- TOTAL VARIATION FROM FINITE EUCLIDEAN L2
--
-- The source formalization defines
--
--   L2Space n = EuclideanSpace C (ZMod (2^n))
--
-- with the unweighted counting Euclidean norm.  For a probability difference
-- h = mu - pi on N finite states, the standard finite Cauchy--Schwarz bridge is
--
--   ||h||_1^2 <= N ||h||_2^2.
--
-- With dTV(mu,pi) = (1/2)||h||_1 this becomes the square-root-free form
--
--   4 dTV(mu,pi)^2 <= N ||h||_2^2.
--
-- Therefore any repaired squared L2 power estimate
--
--   ||P^t h||_2^2 <= C^2 r_t ||h||_2^2
--
-- gives
--
--   4 dTV(mu P^t,pi)^2 <= N C^2 r_t ||h||_2^2.
--
-- This module owns only the abstract inequality composition.  The finite
-- Cauchy--Schwarz inequality itself is standard/library mathematics and DASHI
-- already owns a finite squared Cauchy--Schwarz theorem in
-- NSTriadKNRationalOrderedFiniteL2.  Identifying a concrete probability vector
-- with the source Euclidean vector remains consumer data, not a new spectral
-- theorem.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Primitive using (Level; lsuc)

record OrderedScale (ℓ : Level) : Set (lsuc ℓ) where
  field
    Scalar : Set ℓ
    _≤_ : Scalar → Scalar → Set
    trans≤ : ∀ {a b c} → a ≤ b → b ≤ c → a ≤ c
    scale : Scalar → Scalar → Scalar
    scaleMonoRight : ∀ factor {a b} → a ≤ b → scale factor a ≤ scale factor b

open OrderedScale public

record SquaredTVL2Data {ℓ} (O : OrderedScale ℓ) : Set (lsuc ℓ) where
  field
    fourTVSquared : Scalar O
    stateCount : Scalar O
    currentL2Squared : Scalar O
    initialL2Squared : Scalar O
    mixingEnvelope : Scalar O

    finiteL1L2Bridge :
      _≤_ O fourTVSquared (scale O stateCount currentL2Squared)

    l2PowerBound :
      _≤_ O currentL2Squared mixingEnvelope

    envelopeMeaning :
      Scalar O

open SquaredTVL2Data public

totalVariationSquaredFromL2Squared :
  ∀ {ℓ}
    {O : OrderedScale ℓ}
    (data : SquaredTVL2Data O) →
  _≤_ O
    (fourTVSquared data)
    (scale O (stateCount data) (mixingEnvelope data))
totalVariationSquaredFromL2Squared {O = O} data =
  trans≤ O
    (finiteL1L2Bridge data)
    (scaleMonoRight O (stateCount data) (l2PowerBound data))

------------------------------------------------------------------------
-- Source / promotion boundary.
------------------------------------------------------------------------

record TotalVariationBoundary : Set where
  constructor totalVariationBoundary
  field
    sourceL2IsLiteralFiniteEuclideanSpace : Bool
    sourceTotalVariationTheoremBearing : Bool
    finiteCauchySchwarzStandard : Bool
    repairedL2PowerBoundAvailable : Bool
    squaredTVConsumerCompiled : Bool
    originalUnitPrefactorTVBoundRestored : Bool

canonicalTotalVariationBoundary : TotalVariationBoundary
canonicalTotalVariationBoundary =
  totalVariationBoundary true false true true true false

squaredTVConsumerClosed :
  TotalVariationBoundary.squaredTVConsumerCompiled
    canonicalTotalVariationBoundary
  ≡ true
squaredTVConsumerClosed = refl

sourceDoesNotOwnTVTheorem :
  TotalVariationBoundary.sourceTotalVariationTheoremBearing
    canonicalTotalVariationBoundary
  ≡ false
sourceDoesNotOwnTVTheorem = refl

unitPrefactorTVStillRejected :
  TotalVariationBoundary.originalUnitPrefactorTVBoundRestored
    canonicalTotalVariationBoundary
  ≡ false
unitPrefactorTVStillRejected = refl
