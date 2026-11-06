{-# OPTIONS --safe #-}
module DASHI.Physics.Foundations.TSVFOriginalAllWordMomentTransportExact where

-- S10 / HIL07 finite word compiler, informed by the Karp-21
-- quotient/observable-separation negative control.
--
-- All-order moment equality follows from a single source map, the
-- pointwise letter interpretation, and an expectation pushforward.
-- These are actual inductive proofs over arbitrary finite words,
-- rather than promotion of the mixed two-source covariance.
--
-- To apply to the newly advanced YM #1444 source, instantiate X with
-- the fine native Wilson links, Y with actual R445 blocked links,
-- sourceMap with originalNativeBlock, and expectedPushforward with
-- that SAME original finite Gibbs pushforward.  Do not import the new
-- YM modules into #1460 until the parent branches are reconciled.
-- OS reflection positivity and physical observer state matching
-- are separate proof-producing inputs, not consequences of this file.

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Relation.Binary.PropositionalEquality using (cong; cong₂; trans)

module _
    {X Y LetterX LetterY Scalar : Set}
    (one : Scalar)
    (multiply : Scalar → Scalar → Scalar)
    (sourceMap : X → Y)
    (letterMap : LetterY → LetterX)
    (sourceLetter : LetterX → X → Scalar)
    (targetLetter : LetterY → Y → Scalar)
    (lettersAgree : (letter : LetterY) (x : X) →
      sourceLetter (letterMap letter) x
      ≡ targetLetter letter (sourceMap x))
  where

  interpretSourceWord : List LetterX → X → Scalar
  interpretSourceWord [] x = one
  interpretSourceWord (letter ∷ rest) x =
    multiply (sourceLetter letter x) (interpretSourceWord rest x)

  interpretTargetWord : List LetterY → Y → Scalar
  interpretTargetWord [] y = one
  interpretTargetWord (letter ∷ rest) y =
    multiply (targetLetter letter y) (interpretTargetWord rest y)

  mapWords : List LetterY → List LetterX
  mapWords [] = []
  mapWords (letter ∷ rest) =
    letterMap letter ∷ mapWords rest

  -- Crucial all-length induction: no restriction to degree two.
  originalWordEvaluationNaturality :
    (word : List LetterY) (x : X) →
    interpretSourceWord (mapWords word) x
    ≡ interpretTargetWord word (sourceMap x)
  originalWordEvaluationNaturality [] x = refl
  originalWordEvaluationNaturality (letter ∷ rest) x =
    cong₂ multiply
      (lettersAgree letter x)
      (originalWordEvaluationNaturality rest x)

  module _
      (expectSource : (X → Scalar) → Scalar)
      (expectTarget : (Y → Scalar) → Scalar)
      (sourceExpectationExtensional :
        (f g : X → Scalar) →
        ((x : X) → f x ≡ g x) →
        expectSource f ≡ expectSource g)
      (selectedActualPushforward :
        (f : Y → Scalar) →
        expectSource (λ x → f (sourceMap x))
        ≡ expectTarget f)
    where

    -- Source-only: original Wilson expectation on each actual
    -- pulled-back word equals the corresponding pushforward moment.
    -- The expectation pushforward must be furnished by the real
    -- measure/disintegration owner, not an arbitrary covariance.
    allOriginalFiniteWordMomentsFromSamePushforward :
      (word : List LetterY) →
      expectSource (interpretSourceWord (mapWords word))
      ≡ expectTarget (interpretTargetWord word)
    allOriginalFiniteWordMomentsFromSamePushforward word =
      trans
        (sourceExpectationExtensional
          (interpretSourceWord (mapWords word))
          (λ x → interpretTargetWord word (sourceMap x))
          (originalWordEvaluationNaturality word))
        (selectedActualPushforward (interpretTargetWord word))

    -- Select ANY word-pair composition, including star and a physical
    -- OS-reflection word ordering, without making an extra pairwise
    -- equality assertion.  The composition is applied BEFORE the
    -- all-order source transport.
    originalAllPairingWordsTransport :
      (pairWord : List LetterY → List LetterY → List LetterY) →
      (left right : List LetterY) →
      expectSource
        (interpretSourceWord (mapWords (pairWord left right)))
      ≡ expectTarget
        (interpretTargetWord (pairWord left right))
    originalAllPairingWordsTransport pairWord left right =
      allOriginalFiniteWordMomentsFromSamePushforward
        (pairWord left right)

-- Boundary: this derives all moments for a single finite *classical*
-- pushforward measure. It does not identify observer noncommutative
-- star products with OS reflection pairings, prove positivity of the
-- original TSVF state, complete GNS, or take a physical continuum limit.
