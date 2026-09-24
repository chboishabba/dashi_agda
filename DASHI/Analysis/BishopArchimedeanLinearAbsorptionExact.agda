module DASHI.Analysis.BishopArchimedeanLinearAbsorptionExact where

------------------------------------------------------------------------
-- ARCHIMEDEAN ABSORPTION OF A FIXED LINEAR COST INTO A STRICT RATIO GAP
--
-- DASHI CONTRIBUTION / CROSS-POLLINATION
--
-- For concrete Bishop reals with
--
--   0 <= r < s < 1
--
-- and any natural coefficient C, construct N such that every n >= N obeys
--
--   C r <= n (s-r).
--
-- This is the exact constructive bridge needed after a fixed-degree
-- polynomial successor envelope.  It uses Murray/Bishop's Archimedean theorem
-- and positive reciprocal, not logarithms or a classical limit argument.
------------------------------------------------------------------------

open import Agda.Builtin.Nat using (Nat; suc)
open import Data.Integer.Base as ℤ using (+_)
open import Data.Product.Base using (proj₁; proj₂)
open import Data.Rational.Unnormalised as ℚ using (0ℚᵘ)
import Data.Rational.Unnormalised.Properties as ℚP
open import Data.Sum.Base using (inj₂)
open import Data.Nat.Base renaming (_≤_ to _≤ℕ_)

import Inverse as BishopInverse
import Real as BishopReal
import RealProperties as BishopP

import DASHI.Foundations.BishopFiniteDegreeOneGeometricIdentityExact as NatReal
import DASHI.Foundations.BishopFiniteDegreeOneGeometricBoundExact as DegreeOne
import DASHI.Mathematics.NumberTheory.FiniteNatRationalEmbeddingExact as NatEmbed

record BishopStrictRatioPair
    (ratio largerRatio : BishopReal.ℝ) : Set₁ where
  field
    ratioNonnegative : BishopReal._≤_ BishopReal.0ℝ ratio
    ratioBelowLargerRatio : BishopReal._<_ ratio largerRatio
    largerRatioBelowOne : BishopReal._<_ largerRatio BishopReal.1ℝ

open BishopStrictRatioPair public

ratioGap :
  ∀ {ratio largerRatio} →
  BishopStrictRatioPair ratio largerRatio →
  BishopReal.ℝ
ratioGap {ratio} {largerRatio} inputs =
  BishopReal._-_ largerRatio ratio

ratioGapPositive :
  ∀ {ratio largerRatio}
    (inputs : BishopStrictRatioPair ratio largerRatio) →
  BishopReal._<_ BishopReal.0ℝ (ratioGap inputs)
ratioGapPositive {ratio} {largerRatio} inputs =
  BishopP.x<y⇒0<y-x
    ratio largerRatio (ratioBelowLargerRatio inputs)

ratioGapNonzero :
  ∀ {ratio largerRatio}
    (inputs : BishopStrictRatioPair ratio largerRatio) →
  BishopReal._≄0 (ratioGap inputs)
ratioGapNonzero inputs =
  inj₂ (ratioGapPositive inputs)

ratioGapInverse :
  ∀ {ratio largerRatio} →
  (inputs : BishopStrictRatioPair ratio largerRatio) →
  BishopReal.ℝ
ratioGapInverse inputs =
  BishopInverse._⁻¹
    (ratioGap inputs)
    (ratioGapNonzero inputs)

ratioGapInversePositive :
  ∀ {ratio largerRatio}
    (inputs : BishopStrictRatioPair ratio largerRatio) →
  BishopReal._<_ BishopReal.0ℝ (ratioGapInverse inputs)
ratioGapInversePositive inputs =
  BishopInverse.0<x⇒0<x⁻¹
    (ratioGapNonzero inputs)
    (ratioGapPositive inputs)

natRealMonotone :
  ∀ {left right : Nat} →
  left ≤ℕ right →
  BishopReal._≤_
    (NatReal.natReal left)
    (NatReal.natReal right)
natRealMonotone {left} {right} left≤right =
  BishopP.p≤q⇒p⋆≤q⋆
    (NatEmbed.natAsRational left)
    (NatEmbed.natAsRational right)
    (ℚ.*≤* (ℤ.+≤+ left≤right))

scaledRequirement :
  ∀ {ratio largerRatio} →
  BishopStrictRatioPair ratio largerRatio →
  Nat →
  BishopReal.ℝ
scaledRequirement {ratio} inputs coefficient =
  BishopReal._*_
    (BishopReal._*_
      (NatReal.natReal coefficient)
      ratio)
    (ratioGapInverse inputs)

scaledRequirementNonnegative :
  ∀ {ratio largerRatio}
    (inputs : BishopStrictRatioPair ratio largerRatio)
    coefficient →
  BishopReal.NonNegative
    (scaledRequirement inputs coefficient)
scaledRequirementNonnegative {ratio} inputs coefficient =
  BishopP.nonNegx,y⇒nonNegx*y
    (BishopP.nonNegx,y⇒nonNegx*y
      (DegreeOne.natRealNonnegative coefficient)
      (BishopP.0≤x⇒nonNegx
        (ratioNonnegative inputs)))
    (BishopP.pos⇒nonNeg
      (BishopP.0<x⇒posx
        (ratioGapInversePositive inputs)))

absorptionCutoff :
  ∀ {ratio largerRatio} →
  BishopStrictRatioPair ratio largerRatio →
  Nat →
  Nat
absorptionCutoff inputs coefficient =
  suc
    (proj₁
      (BishopP.archimedean-ℝ
        (BishopReal.∣ scaledRequirement inputs coefficient ∣)))

scaledRequirementBelowCutoff :
  ∀ {ratio largerRatio}
    (inputs : BishopStrictRatioPair ratio largerRatio)
    coefficient →
  BishopReal._<_
    (scaledRequirement inputs coefficient)
    (NatReal.natReal
      (absorptionCutoff inputs coefficient))
scaledRequirementBelowCutoff inputs coefficient =
  let
    requirement = scaledRequirement inputs coefficient
    arch =
      proj₂
        (BishopP.archimedean-ℝ
          (BishopReal.∣ requirement ∣))
    absoluteIsRequirement =
      BishopP.nonNegx⇒∣x∣≃x
        (scaledRequirementNonnegative inputs coefficient)
  in
  BishopP.<-respˡ-≃
    absoluteIsRequirement
    arch

scaledRequirementCancelsGap :
  ∀ {ratio largerRatio}
    (inputs : BishopStrictRatioPair ratio largerRatio)
    coefficient →
  BishopReal._≃_
    (BishopReal._*_
      (scaledRequirement inputs coefficient)
      (ratioGap inputs))
    (BishopReal._*_
      (NatReal.natReal coefficient)
      ratio)
scaledRequirementCancelsGap {ratio} inputs coefficient =
  let
    coefficientTimesRatio =
      BishopReal._*_
        (NatReal.natReal coefficient)
        ratio
    inverse = ratioGapInverse inputs
    gap = ratioGap inputs
    inverseLaw =
      BishopInverse.*-inverseˡ
        gap
        (ratioGapNonzero inputs)
  in
  BishopP.≃-trans
    (BishopP.*-assoc coefficientTimesRatio inverse gap)
    (BishopP.≃-trans
      (BishopP.*-congʳ inverseLaw)
      (BishopP.*-identityˡ coefficientTimesRatio))

cutoffStrictAbsorption :
  ∀ {ratio largerRatio}
    (inputs : BishopStrictRatioPair ratio largerRatio)
    coefficient →
  BishopReal._<_
    (BishopReal._*_
      (NatReal.natReal coefficient)
      ratio)
    (BishopReal._*_
      (NatReal.natReal
        (absorptionCutoff inputs coefficient))
      (ratioGap inputs))
cutoffStrictAbsorption inputs coefficient =
  let
    gapPositive =
      BishopP.0<x⇒posx
        (ratioGapPositive inputs)
    scaled =
      BishopP.*-monoˡ-<-pos
        gapPositive
        (scaledRequirementBelowCutoff inputs coefficient)
  in
  BishopP.<-respˡ-≃
    (scaledRequirementCancelsGap inputs coefficient)
    scaled

eventualLinearGapAbsorption :
  ∀ {ratio largerRatio}
    (inputs : BishopStrictRatioPair ratio largerRatio)
    coefficient →
  ∀ n →
  absorptionCutoff inputs coefficient ≤ℕ n →
  BishopReal._≤_
    (BishopReal._*_
      (NatReal.natReal coefficient)
      ratio)
    (BishopReal._*_
      (NatReal.natReal n)
      (ratioGap inputs))
eventualLinearGapAbsorption inputs coefficient n cutoff≤n =
  let
    cutoffBound =
      BishopP.<⇒≤
        (cutoffStrictAbsorption inputs coefficient)

    gapNonnegative =
      BishopP.pos⇒nonNeg
        (BishopP.0<x⇒posx
          (ratioGapPositive inputs))

    cutoffToIndex =
      BishopP.*-monoˡ-≤-nonNeg
        (natRealMonotone cutoff≤n)
        gapNonnegative
  in
  BishopP.≤-trans
    cutoffBound
    cutoffToIndex
