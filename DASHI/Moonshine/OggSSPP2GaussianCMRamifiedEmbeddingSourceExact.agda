module DASHI.Moonshine.OggSSPP2GaussianCMRamifiedEmbeddingSourceExact where

------------------------------------------------------------------------
-- GAUSSIAN-CM RAMIFIED EMBEDDING SOURCE AT p=2
--
-- EXTERNAL SOURCE CONTEXT
--
-- Elkies--Ono--Yang (2005), Section 3:
--   * CM embeddings occur in conjugate pairs;
--   * if p is inert or ramified, reduction is supersingular and gives an
--     optimal embedding into the supersingular endomorphism ring;
--   * in the ramified case every embedding in the conjugate pair is normalized.
--
-- Goren--Love (2025):
--   * every imaginary quadratic discriminant has exactly two oriented orders
--     up to oriented isomorphism, exchanged by nontrivial Galois;
--   * oriented optimal embeddings correspond to primitive trace-zero elements.
--
-- For Gaussian CM K = Q(i), p=2 is ramified.
--
-- This module records the source shape and the exact formal realization
-- contract.  It does not manufacture an endomorphism-ring embedding.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.String using (String)

import DASHI.Moonshine.OggSSPP2OrientedInertiaTenStateRecognitionExact as Ten
import DASHI.Moonshine.OggSSPMonstrousExponentSourceAttributionExact as Attribution

Orientation : Set
Orientation =
  Ten.ClassicalQuadraticOrientation

conjugateOrientation :
  Orientation ->
  Orientation
conjugateOrientation Ten.firstGaloisOrientation =
  Ten.conjugateGaloisOrientation
conjugateOrientation Ten.conjugateGaloisOrientation =
  Ten.firstGaloisOrientation

conjugateOrientationInvolutive :
  (orientation : Orientation) ->
  conjugateOrientation (conjugateOrientation orientation)
  ≡ orientation
conjugateOrientationInvolutive Ten.firstGaloisOrientation = refl
conjugateOrientationInvolutive Ten.conjugateGaloisOrientation = refl

record GaussianCMRamifiedSourceReceipt : Set where
  constructor gaussian-cm-ramified-source-receipt
  field
    gaussianCMFieldRecorded : Bool
    primeTwoRamifiedRecorded : Bool
    nonSplitReductionSupersingularRecorded : Bool
    reductionOptimalEmbeddingRecorded : Bool
    ramifiedPairBothNormalizedRecorded : Bool
    twoOrientedOrdersRecorded : Bool
    sourceReference : String

canonicalGaussianCMRamifiedSourceReceipt :
  GaussianCMRamifiedSourceReceipt
canonicalGaussianCMRamifiedSourceReceipt =
  gaussian-cm-ramified-source-receipt
    true true true true true true
    "Elkies-Ono-Yang, IMRN 2005(44), Section 3; Goren-Love, Canadian J. Math. 77(6), Proposition 3.7 and oriented-order discussion"

record GaussianCMEmbeddingRealization
  (EndomorphismObject : Set) : Set₁ where
  field
    Embedding : Set

    embeddingOfOrientation :
      Orientation ->
      Embedding

    targetEndomorphismObject :
      Embedding ->
      EndomorphismObject

    selectedEndomorphismObject :
      EndomorphismObject

    everyEmbeddingTargetsSelectedObject :
      (orientation : Orientation) ->
      targetEndomorphismObject (embeddingOfOrientation orientation)
      ≡ selectedEndomorphismObject

    optimal :
      Embedding ->
      Bool

    optimalIsTrue :
      (orientation : Orientation) ->
      optimal (embeddingOfOrientation orientation) ≡ true

    normalized :
      Embedding ->
      Bool

    normalizedIsTrue :
      (orientation : Orientation) ->
      normalized (embeddingOfOrientation orientation) ≡ true

    conjugatePair :
      Bool

    conjugatePairIsTrue :
      conjugatePair ≡ true

    orientationsDistinct :
      embeddingOfOrientation Ten.firstGaloisOrientation
      ≡ embeddingOfOrientation Ten.conjugateGaloisOrientation
      ->
      ⊥

open GaussianCMEmbeddingRealization public

claimOrigin : Attribution.ClaimOrigin
claimOrigin = Attribution.repositoryNewExtension

record GaussianCMRamifiedEmbeddingBoundary : Set where
  constructor gaussian-cm-ramified-embedding-boundary
  field
    ramifiedGaussianCMSourceRecorded : Bool
    conjugatePairSourceRecorded : Bool
    bothEmbeddingsNormalizedRecorded : Bool
    twoOrientedOrdersRecorded : Bool
    sameBanerjeeEndomorphismRealizationConstructed : Bool

canonicalGaussianCMRamifiedEmbeddingBoundary :
  GaussianCMRamifiedEmbeddingBoundary
canonicalGaussianCMRamifiedEmbeddingBoundary =
  gaussian-cm-ramified-embedding-boundary
    true true true true false
