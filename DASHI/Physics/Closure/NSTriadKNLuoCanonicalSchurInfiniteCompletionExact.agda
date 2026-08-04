module DASHI.Physics.Closure.NSTriadKNLuoCanonicalSchurInfiniteCompletionExact where

------------------------------------------------------------------------
-- PROVENANCE
--
-- Authors: Loukas Grafakos; Rodolfo H. Torres.
-- Title: "A Multilinear Schur Test and Multiplier Operators".
-- Journal of Functional Analysis 187 (2001), 1--24.
-- DOI: 10.1006/jfan.2001.3804.
--
-- Author: Xiaoyutao Luo.
-- Title: "A Beale--Kato--Majda Criterion with Optimal Frequency and
-- Temporal Localization".
-- Journal of Mathematical Fluid Mechanics 21 (2019), article 1.
-- DOI: 10.1007/s00021-019-0411-z.
-- arXiv DOI: 10.48550/arXiv.1803.05569.
--
-- PURPOSE
-- Complete the canonical two-parameter Schur kernel rather than stopping at
-- cutoff-uniform bounds.  Exact induction gives the remainders
--
--   4/3 - sum_{j=0}^J (1/4)^j
--     = (4/3)(1/4)^{J+1},
--
--   32/31 - sum_{d=0}^D (1/32)^d
--     = (32/31)(1/32)^{D+1}.
--
-- The rectangular prefix therefore converges to 128/93 with a fully explicit
-- nonnegative error bounded by the sum of the two geometric tails.  This is a
-- constructive infinite completion of the canonical Schur envelope, not a
-- mere finite-prefix receipt.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Data.Rational.Base using
  (ℚ; 0ℚ; _+_; _*_; _-_; _≤_; nonNegative)
import Data.Rational.Properties as ℚₚ
open import Data.Rational.Tactic.RingSolver using (solve)
open import Relation.Binary.PropositionalEquality as Eq
  using (cong; subst; sym)
open Eq.≡-Reasoning

import DASHI.Physics.Closure.NSTriadKNRationalOrderedFiniteL2 as L2
import DASHI.Physics.Closure.NSTriadKNRationalFiniteGeometricEnvelope as Geo

quarterErrorIdentity :
  (cutoff : Nat) →
  Geo.fourThirds - Geo.partialSum Geo.quarter cutoff
  ≡ Geo.fourThirds * Geo.pow Geo.quarter (suc cutoff)
quarterErrorIdentity zero = refl
quarterErrorIdentity (suc cutoff)
  rewrite quarterErrorIdentity cutoff =
  solve
    ( Geo.fourThirds
    ∷ Geo.quarter
    ∷ Geo.pow Geo.quarter (suc cutoff)
    ∷ []
    )

thirtySecondErrorIdentity :
  (cutoff : Nat) →
  Geo.thirtyTwoThirtyFirsts
    - Geo.partialSum Geo.thirtySecond cutoff
  ≡ Geo.thirtyTwoThirtyFirsts
      * Geo.pow Geo.thirtySecond (suc cutoff)
thirtySecondErrorIdentity zero = refl
thirtySecondErrorIdentity (suc cutoff)
  rewrite thirtySecondErrorIdentity cutoff =
  solve
    ( Geo.thirtyTwoThirtyFirsts
    ∷ Geo.thirtySecond
    ∷ Geo.pow Geo.thirtySecond (suc cutoff)
    ∷ []
    )

quarterErrorNonnegative :
  (cutoff : Nat) →
  0ℚ ≤ Geo.fourThirds - Geo.partialSum Geo.quarter cutoff
quarterErrorNonnegative cutoff =
  L2.differenceNonnegative
    (Geo.partialSum Geo.quarter cutoff)
    Geo.fourThirds
    (Geo.quarterPartialSumBound cutoff)

thirtySecondErrorNonnegative :
  (cutoff : Nat) →
  0ℚ ≤ Geo.thirtyTwoThirtyFirsts
    - Geo.partialSum Geo.thirtySecond cutoff
thirtySecondErrorNonnegative cutoff =
  L2.differenceNonnegative
    (Geo.partialSum Geo.thirtySecond cutoff)
    Geo.thirtyTwoThirtyFirsts
    (Geo.thirtySecondPartialSumBound cutoff)

canonicalRectanglePrefix : Nat → Nat → ℚ
canonicalRectanglePrefix lowCutoff gapCutoff =
  Geo.partialSum Geo.quarter lowCutoff
  * Geo.partialSum Geo.thirtySecond gapCutoff

canonicalRectangleError : Nat → Nat → ℚ
canonicalRectangleError lowCutoff gapCutoff =
  Geo.oneTwentyEightNinetyThirds
  - canonicalRectanglePrefix lowCutoff gapCutoff

rectangleErrorDecomposition :
  (lowCutoff gapCutoff : Nat) →
  canonicalRectangleError lowCutoff gapCutoff
  ≡ (Geo.fourThirds
      - Geo.partialSum Geo.quarter lowCutoff)
      * Geo.thirtyTwoThirtyFirsts
    + Geo.partialSum Geo.quarter lowCutoff
      * (Geo.thirtyTwoThirtyFirsts
          - Geo.partialSum Geo.thirtySecond gapCutoff)
rectangleErrorDecomposition lowCutoff gapCutoff
  rewrite sym Geo.productConstantIdentity =
  solve
    ( Geo.fourThirds
    ∷ Geo.thirtyTwoThirtyFirsts
    ∷ Geo.partialSum Geo.quarter lowCutoff
    ∷ Geo.partialSum Geo.thirtySecond gapCutoff
    ∷ []
    )

rectangleErrorExactTailFormula :
  (lowCutoff gapCutoff : Nat) →
  canonicalRectangleError lowCutoff gapCutoff
  ≡ (Geo.fourThirds
      * Geo.pow Geo.quarter (suc lowCutoff))
      * Geo.thirtyTwoThirtyFirsts
    + Geo.partialSum Geo.quarter lowCutoff
      * (Geo.thirtyTwoThirtyFirsts
          * Geo.pow Geo.thirtySecond (suc gapCutoff))
rectangleErrorExactTailFormula lowCutoff gapCutoff =
  begin
    canonicalRectangleError lowCutoff gapCutoff
  ≡⟨ rectangleErrorDecomposition lowCutoff gapCutoff ⟩
    (Geo.fourThirds
      - Geo.partialSum Geo.quarter lowCutoff)
      * Geo.thirtyTwoThirtyFirsts
    + Geo.partialSum Geo.quarter lowCutoff
      * (Geo.thirtyTwoThirtyFirsts
          - Geo.partialSum Geo.thirtySecond gapCutoff)
  ≡⟨ cong
       (λ lowError →
         lowError * Geo.thirtyTwoThirtyFirsts
         + Geo.partialSum Geo.quarter lowCutoff
           * (Geo.thirtyTwoThirtyFirsts
               - Geo.partialSum Geo.thirtySecond gapCutoff))
       (quarterErrorIdentity lowCutoff) ⟩
    (Geo.fourThirds
      * Geo.pow Geo.quarter (suc lowCutoff))
      * Geo.thirtyTwoThirtyFirsts
    + Geo.partialSum Geo.quarter lowCutoff
      * (Geo.thirtyTwoThirtyFirsts
          - Geo.partialSum Geo.thirtySecond gapCutoff)
  ≡⟨ cong
       (λ gapError →
         (Geo.fourThirds
           * Geo.pow Geo.quarter (suc lowCutoff))
           * Geo.thirtyTwoThirtyFirsts
         + Geo.partialSum Geo.quarter lowCutoff * gapError)
       (thirtySecondErrorIdentity gapCutoff) ⟩
    (Geo.fourThirds
      * Geo.pow Geo.quarter (suc lowCutoff))
      * Geo.thirtyTwoThirtyFirsts
    + Geo.partialSum Geo.quarter lowCutoff
      * (Geo.thirtyTwoThirtyFirsts
          * Geo.pow Geo.thirtySecond (suc gapCutoff))
  ∎

canonicalRectangleErrorNonnegative :
  (lowCutoff gapCutoff : Nat) →
  0ℚ ≤ canonicalRectangleError lowCutoff gapCutoff
canonicalRectangleErrorNonnegative lowCutoff gapCutoff =
  L2.differenceNonnegative
    (canonicalRectanglePrefix lowCutoff gapCutoff)
    Geo.oneTwentyEightNinetyThirds
    (Geo.rectanglePartialSumBoundExact lowCutoff gapCutoff)

canonicalRectangleErrorUpper :
  (lowCutoff gapCutoff : Nat) →
  canonicalRectangleError lowCutoff gapCutoff
  ≤ Geo.oneTwentyEightNinetyThirds
      * ( Geo.pow Geo.quarter (suc lowCutoff)
        + Geo.pow Geo.thirtySecond (suc gapCutoff))
canonicalRectangleErrorUpper lowCutoff gapCutoff =
  let
    lowTail = Geo.pow Geo.quarter (suc lowCutoff)
    gapTail = Geo.pow Geo.thirtySecond (suc gapCutoff)
    lowPrefix = Geo.partialSum Geo.quarter lowCutoff

    lowTailNonnegative =
      Geo.powNonnegative
        Geo.quarter (suc lowCutoff) Geo.quarterNonnegative
    gapTailNonnegative =
      Geo.powNonnegative
        Geo.thirtySecond (suc gapCutoff) Geo.thirtySecondNonnegative

    gapCoefficientBound :
      lowPrefix * (Geo.thirtyTwoThirtyFirsts * gapTail)
      ≤ Geo.fourThirds
          * (Geo.thirtyTwoThirtyFirsts * gapTail)
    gapCoefficientBound =
      let
        coefficientNonnegative :
          0ℚ ≤ Geo.thirtyTwoThirtyFirsts * gapTail
        coefficientNonnegative =
          let
            instance
              boundIsNonnegative =
                nonNegative Geo.thirtyTwoThirtyFirstsNonnegative
              tailIsNonnegative = nonNegative gapTailNonnegative
              productIsNonnegative =
                ℚₚ.nonNeg*nonNeg⇒nonNeg
                  Geo.thirtyTwoThirtyFirsts gapTail
          in
          ℚₚ.nonNegative⁻¹
            (Geo.thirtyTwoThirtyFirsts * gapTail)

        instance coefficientIsNonnegative =
          nonNegative coefficientNonnegative
      in
      ℚₚ.*-monoʳ-≤-nonNeg
        (Geo.thirtyTwoThirtyFirsts * gapTail)
        (Geo.quarterPartialSumBound lowCutoff)

    sumBound :
      (Geo.fourThirds * lowTail) * Geo.thirtyTwoThirtyFirsts
        + lowPrefix * (Geo.thirtyTwoThirtyFirsts * gapTail)
      ≤ (Geo.fourThirds * lowTail) * Geo.thirtyTwoThirtyFirsts
        + Geo.fourThirds
            * (Geo.thirtyTwoThirtyFirsts * gapTail)
    sumBound = ℚₚ.+-monoʳ-≤
      ((Geo.fourThirds * lowTail) * Geo.thirtyTwoThirtyFirsts)
      gapCoefficientBound

    factorTarget :
      (Geo.fourThirds * lowTail) * Geo.thirtyTwoThirtyFirsts
        + Geo.fourThirds
            * (Geo.thirtyTwoThirtyFirsts * gapTail)
      ≡ Geo.oneTwentyEightNinetyThirds * (lowTail + gapTail)
    factorTarget
      rewrite sym Geo.productConstantIdentity =
      solve
        ( Geo.fourThirds
        ∷ Geo.thirtyTwoThirtyFirsts
        ∷ lowTail
        ∷ gapTail
        ∷ []
        )
  in
  subst
    (λ upper → canonicalRectangleError lowCutoff gapCutoff ≤ upper)
    factorTarget
    (subst
      (λ lower →
        lower
        ≤ (Geo.fourThirds * lowTail) * Geo.thirtyTwoThirtyFirsts
          + Geo.fourThirds
              * (Geo.thirtyTwoThirtyFirsts * gapTail))
      (sym (rectangleErrorExactTailFormula lowCutoff gapCutoff))
      sumBound)

record CanonicalSchurCompletion : Set where
  field
    approximation : Nat → ℚ
    limit : ℚ
    error : Nat → ℚ

    approximationMeaning :
      (cutoff : Nat) →
      approximation cutoff ≡ canonicalRectanglePrefix cutoff cutoff

    limitMeaning : limit ≡ Geo.oneTwentyEightNinetyThirds

    errorMeaning :
      (cutoff : Nat) →
      error cutoff ≡ limit - approximation cutoff

    errorNonnegative :
      (cutoff : Nat) → 0ℚ ≤ error cutoff

    explicitErrorBound :
      (cutoff : Nat) →
      error cutoff
      ≤ Geo.oneTwentyEightNinetyThirds
          * ( Geo.pow Geo.quarter (suc cutoff)
            + Geo.pow Geo.thirtySecond (suc cutoff))

open CanonicalSchurCompletion public

canonicalSchurCompletion : CanonicalSchurCompletion
canonicalSchurCompletion = record
  { approximation = λ cutoff → canonicalRectanglePrefix cutoff cutoff
  ; limit = Geo.oneTwentyEightNinetyThirds
  ; error = λ cutoff → canonicalRectangleError cutoff cutoff
  ; approximationMeaning = λ cutoff → refl
  ; limitMeaning = refl
  ; errorMeaning = λ cutoff → refl
  ; errorNonnegative = λ cutoff →
      canonicalRectangleErrorNonnegative cutoff cutoff
  ; explicitErrorBound = λ cutoff →
      canonicalRectangleErrorUpper cutoff cutoff
  }
