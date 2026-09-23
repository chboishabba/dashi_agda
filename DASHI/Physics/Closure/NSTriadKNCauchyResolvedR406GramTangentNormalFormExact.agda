{-# OPTIONS --safe #-}
module DASHI.Physics.Closure.NSTriadKNCauchyResolvedR406GramTangentNormalFormExact where

------------------------------------------------------------------------
-- CAUCHY-RESOLVED R406 = GRAM + RESOLVED GRAM-TANGENT
--
-- R291 gives, for every damped pair,
--
--   gramTangent = -pairRate * gram + nonlinearGramRemainder.
--
-- Hence
--
--   nonlinearGramRemainder = gramTangent + pairRate * gram.
--
-- Multiplying by a Cauchy resolvent K with K*pairRate = 1 gives exactly
--
--   K * nonlinearGramRemainder = K * gramTangent + gram.
--
-- This module lifts that pointwise identity to the complete finite square and
-- specializes it to the literal R538 physical pair-resolvent carrier.
-- No estimate, sign, absolute value, or spacetime argument occurs.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List)
open import Data.Rational.Base using (ℚ; 0ℚ; 1ℚ; Positive; _+_; _-_; _*_)
open import Data.Rational.Tactic.RingSolver using (solve)
open import Relation.Binary.PropositionalEquality using (cong; trans)

import DASHI.Physics.Closure.NSTriadKNPhysicalTriadEnumeration as Physical
import DASHI.Physics.Closure.NSTriadKNComplex3ExactCarrier as C3
import DASHI.Physics.Closure.NSTriadKNRationalOrderedFiniteL2 as Rational
import DASHI.Physics.Closure.NSTriadKNPeriodicHelicalFourierInfrastructure as Helical
import DASHI.Physics.Closure.NSTriadKNLiteralViscousQuadraticCoefficientRound30Exact as Field30
import DASHI.Physics.Closure.NSTriadKNPhysicalGramPairTangentRound291Exact as R291
import DASHI.Physics.Closure.NSTriadKNDoubleMixedGramPairToResolventRound389Exact as R389
import DASHI.Physics.Closure.NSTriadKNDirectResolventPairSwapSymmetryRound538Exact as R538
import DASHI.Physics.Closure.NSTriadKNFullSquareDiagonalOffDiagonalRound543Exact as R543
import DASHI.Physics.Closure.NSTriadKNCauchyResolvedFullSquareRateCancellationExact as Cauchy

resolvedTangentAtom :
  ∀ {A : Set} →
  (A → A → ℚ) → (A → A → ℚ) → A → A → ℚ
resolvedTangentAtom kernel tangent i j = kernel i j * tangent i j

gramPlusResolvedTangent :
  ∀ {A : Set} →
  (A → A → ℚ) → (A → A → ℚ) → (A → A → ℚ) → A → A → ℚ
gramPlusResolvedTangent kernel gram tangent i j =
  gram i j + resolvedTangentAtom kernel tangent i j

resolvedRemainderPointwise :
  ∀ {A : Set}
    (kernel rate gram tangent remainder : A → A → ℚ) →
  ((i j : A) →
    tangent i j ≡ (0ℚ - rate i j) * gram i j + remainder i j) →
  ((i j : A) → kernel i j * rate i j ≡ 1ℚ) →
  (i j : A) →
  kernel i j * remainder i j
  ≡ gramPlusResolvedTangent kernel gram tangent i j
resolvedRemainderPointwise kernel rate gram tangent remainder tangentLaw inverseLaw i j =
  let
    k = kernel i j
    r = rate i j
    g = gram i j
    t = tangent i j
    n = remainder i j

    remainderFromTangent :
      n ≡ t + r * g
    remainderFromTangent
      rewrite tangentLaw i j =
      solve (r ∷ g ∷ n ∷ [])

    distribute :
      k * n ≡ k * t + (k * r) * g
    distribute
      rewrite remainderFromTangent =
      solve (k ∷ t ∷ r ∷ g ∷ [])

  in
  trans distribute
    (cong (λ x → k * t + x * g) (inverseLaw i j))

resolvedRemainderFullSquare :
  ∀ {A : Set}
    (kernel rate gram tangent remainder : A → A → ℚ)
    (items : List A) →
  ((i j : A) →
    tangent i j ≡ (0ℚ - rate i j) * gram i j + remainder i j) →
  ((i j : A) → kernel i j * rate i j ≡ 1ℚ) →
  R543.fullSquareSum (λ i j → kernel i j * remainder i j) items
  ≡
  R543.fullSquareSum
    (gramPlusResolvedTangent kernel gram tangent) items
resolvedRemainderFullSquare kernel rate gram tangent remainder items tangentLaw inverseLaw =
  Cauchy.fullSquareCongruent
    (λ i j → kernel i j * remainder i j)
    (gramPlusResolvedTangent kernel gram tangent)
    (resolvedRemainderPointwise
      kernel rate gram tangent remainder tangentLaw inverseLaw)
    items

------------------------------------------------------------------------
-- Literal R538 physical specialization.
------------------------------------------------------------------------

F : C3.RealField _
F = Rational.rationalRealField

module Physical
    (physicalSystem : Field30.PhysicalFiniteComplex3GalerkinSystem F)
    (S : Helical.HelicalModeScalars F) where

  module Pair = R389.DoubleMixedPair physicalSystem S
  module Swap = R538.PairSwap physicalSystem S
  module Resolved = Cauchy.PhysicalResolved physicalSystem S

  pairRate : Physical.PhysicalTriadIncidence → Physical.PhysicalTriadIncidence → ℚ
  pairRate alpha beta =
    R291.pairRate (Pair.physicalDoubleMixedPair alpha beta)

  pairGram : Physical.PhysicalTriadIncidence → Physical.PhysicalTriadIncidence → ℚ
  pairGram alpha beta =
    R291.gram (Pair.physicalDoubleMixedPair alpha beta)

  pairTangent : Physical.PhysicalTriadIncidence → Physical.PhysicalTriadIncidence → ℚ
  pairTangent alpha beta =
    R291.gramTangent (Pair.physicalDoubleMixedPair alpha beta)

  pairRemainder : Physical.PhysicalTriadIncidence → Physical.PhysicalTriadIncidence → ℚ
  pairRemainder alpha beta =
    R291.nonlinearGramRemainder (Pair.physicalDoubleMixedPair alpha beta)

  physicalPairTangentLaw :
    (alpha beta : Physical.PhysicalTriadIncidence) →
    pairTangent alpha beta
    ≡ (0ℚ - pairRate alpha beta) * pairGram alpha beta
      + pairRemainder alpha beta
  physicalPairTangentLaw alpha beta =
    R291.gramPairDampedTangent (Pair.physicalDoubleMixedPair alpha beta)

  physicalResolvedRemainderPointwise :
    ((alpha beta : Physical.PhysicalTriadIncidence) →
      Positive (pairRate alpha beta)) →
    (alpha beta : Physical.PhysicalTriadIncidence) →
    Swap.symmetricWeightedRemainder alpha beta
    ≡
    pairGram alpha beta
      + Swap.pairResolvent alpha beta * pairTangent alpha beta
  physicalResolvedRemainderPointwise positive alpha beta =
    resolvedRemainderPointwise
      Swap.pairResolvent
      pairRate
      pairGram
      pairTangent
      pairRemainder
      physicalPairTangentLaw
      (λ i j → Resolved.physicalPairResolventLaw positive i j)
      alpha beta

  physicalResolvedFullSquare :
    (items : List Physical.PhysicalTriadIncidence) →
    ((alpha beta : Physical.PhysicalTriadIncidence) →
      Positive (pairRate alpha beta)) →
    R543.fullSquareSum Swap.symmetricWeightedRemainder items
    ≡
    R543.fullSquareSum
      (gramPlusResolvedTangent
        Swap.pairResolvent pairGram pairTangent) items
  physicalResolvedFullSquare items positive =
    Cauchy.fullSquareCongruent
      Swap.symmetricWeightedRemainder
      (gramPlusResolvedTangent
        Swap.pairResolvent pairGram pairTangent)
      (physicalResolvedRemainderPointwise positive)
      items

------------------------------------------------------------------------
-- Status.
------------------------------------------------------------------------

cauchyResolvedR406GramTangentPointwiseClosed : Bool
cauchyResolvedR406GramTangentPointwiseClosed = true

cauchyResolvedR406GramTangentFullSquareClosed : Bool
cauchyResolvedR406GramTangentFullSquareClosed = true

cauchyResolvedR406GramTangentIntroducesEstimate : Bool
cauchyResolvedR406GramTangentIntroducesEstimate = false

cauchyResolvedR406GramTangentUsesAbsoluteValue : Bool
cauchyResolvedR406GramTangentUsesAbsoluteValue = false

cauchyResolvedR406GramTangentPointwiseClosedIsTrue :
  cauchyResolvedR406GramTangentPointwiseClosed ≡ true
cauchyResolvedR406GramTangentPointwiseClosedIsTrue = refl

cauchyResolvedR406GramTangentFullSquareClosedIsTrue :
  cauchyResolvedR406GramTangentFullSquareClosed ≡ true
cauchyResolvedR406GramTangentFullSquareClosedIsTrue = refl

cauchyResolvedR406GramTangentIntroducesEstimateIsFalse :
  cauchyResolvedR406GramTangentIntroducesEstimate ≡ false
cauchyResolvedR406GramTangentIntroducesEstimateIsFalse = refl

cauchyResolvedR406GramTangentUsesAbsoluteValueIsFalse :
  cauchyResolvedR406GramTangentUsesAbsoluteValue ≡ false
cauchyResolvedR406GramTangentUsesAbsoluteValueIsFalse = refl
