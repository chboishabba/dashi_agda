module DASHI.Physics.Closure.NSTriadKNHHViscousSignedCoherenceThresholdRound88Exact where

------------------------------------------------------------------------
-- PRIMARY SOURCES / CONTEXT
--
-- Author: Terence Tao.
-- Title: "Finite time blowup for an averaged three-dimensional Navier-Stokes
-- equation".
-- DOI: 10.1090/jams/838.
--
-- Author: Alexey Cheskidov.
-- Title: "Blow-up in finite time for the dyadic model of the Navier-Stokes
-- equations".
-- DOI: 10.1090/S0002-9947-08-04494-2.
--
-- ROUND88 / SHARP SIGNED-TRANSFER COHERENCE GATE
--
-- Round87 proves that HH->low geometry supplies a negative viscous coefficient
-- but does not control the sign of each triad transfer.  Decompose selected
-- transfer into positive and negative masses
--
--     q = P - N,        P,N >= 0.
--
-- Suppose the damping magnitude a_t on the selected sector obeys
--
--     M <= a_t <= C.
--
-- Then the worst signed aggregate is bounded by
--
--     R_nu <= - M P + C N.
--
-- If the negative transfer mass is coherent in the quantitative sense
--
--     N <= theta P,
--
-- then
--
--     R_nu <= - (M - C theta) P.
--
-- Hence the exact strict gate is C theta < M.  If only the non-strict
-- inequality C theta <= M is available, the aggregate is nonpositive.  Since
-- q=P-N <= P, a nonnegative margin delta=M-C theta also gives
--
--     R_nu <= -delta q.
--
-- This file turns the vague Round87 phrase "control signed cancellation" into
-- one dimensionless physical target: prove a selected-event coherence ratio
-- theta strictly below M/C on the literal HH->low transfer carrier.
--
-- The theorem is finite rational order algebra.  The physical producer remains
-- construction of P,N and the coefficient bounds from actual Fourier triads.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using ([]; _∷_)
open import Data.Rational.Base using
  (ℚ; 0ℚ; _+_; _-_; _*_; _≤_; _<_; -_; nonNegative)
import Data.Rational.Properties as ℚP
open import Data.Rational.Tactic.RingSolver using (solve)
open import Relation.Binary.PropositionalEquality using (subst; sym)

record SignedHHViscousCoherenceBudget : Set where
  constructor signed-hh-viscous-coherence-budget
  field
    positiveMass negativeMass : ℚ
    minimumDamping maximumDamping coherence : ℚ
    positiveWeightedDamping negativeWeightedDamping : ℚ

    positiveMassNonnegative : 0ℚ ≤ positiveMass
    negativeMassNonnegative : 0ℚ ≤ negativeMass
    minimumDampingNonnegative : 0ℚ ≤ minimumDamping
    maximumDampingNonnegative : 0ℚ ≤ maximumDamping
    coherenceNonnegative : 0ℚ ≤ coherence

    negativeMassCoherent :
      negativeMass ≤ coherence * positiveMass

    positiveWeightedAtLeastMinimum :
      minimumDamping * positiveMass ≤ positiveWeightedDamping

    negativeWeightedAtMostMaximum :
      negativeWeightedDamping ≤ maximumDamping * negativeMass

open SignedHHViscousCoherenceBudget public

netTransfer : SignedHHViscousCoherenceBudget → ℚ
netTransfer budget = positiveMass budget - negativeMass budget

netViscousContribution : SignedHHViscousCoherenceBudget → ℚ
netViscousContribution budget =
  negativeWeightedDamping budget - positiveWeightedDamping budget

coerciveMargin : SignedHHViscousCoherenceBudget → ℚ
coerciveMargin budget =
  minimumDamping budget - maximumDamping budget * coherence budget

netTransferAtMostPositiveMass :
  ∀ budget → netTransfer budget ≤ positiveMass budget
netTransferAtMostPositiveMass budget =
  let
    negN≤0 : - negativeMass budget ≤ 0ℚ
    negN≤0 = ℚP.neg-antimono-≤ (negativeMassNonnegative budget)
    raw = ℚP.+-mono-≤ ℚP.≤-refl negN≤0
  in
  subst
    (λ right → netTransfer budget ≤ right)
    (solve (positiveMass budget ∷ []))
    (subst
      (λ left → left ≤ positiveMass budget + 0ℚ)
      (solve (positiveMass budget ∷ negativeMass budget ∷ []))
      raw)

weightedContributionBelowEndpoint :
  ∀ budget →
  netViscousContribution budget
  ≤ maximumDamping budget * negativeMass budget
      - minimumDamping budget * positiveMass budget
weightedContributionBelowEndpoint budget =
  let
    upperNegative = negativeWeightedAtMostMaximum budget
    lowerPositive = positiveWeightedAtLeastMinimum budget
    negUpperPositive = ℚP.neg-antimono-≤ lowerPositive
    added = ℚP.+-mono-≤ upperNegative negUpperPositive
  in
  subst
    (λ left → left ≤
      maximumDamping budget * negativeMass budget
        - minimumDamping budget * positiveMass budget)
    (solve
      ( negativeWeightedDamping budget
      ∷ positiveWeightedDamping budget
      ∷ []))
    (subst
      (λ right →
        negativeWeightedDamping budget + (- positiveWeightedDamping budget)
        ≤ right)
      (solve
        ( maximumDamping budget
        ∷ negativeMass budget
        ∷ minimumDamping budget
        ∷ positiveMass budget
        ∷ []))
      added)

maximumTimesNegativeMassBelowCoherentMass :
  ∀ budget →
  maximumDamping budget * negativeMass budget
  ≤ maximumDamping budget * coherence budget * positiveMass budget
maximumTimesNegativeMassBelowCoherentMass budget =
  let instance maxNN = nonNegative (maximumDampingNonnegative budget)
      scaled = ℚP.*-monoˡ-≤-nonNeg
        (maximumDamping budget) (negativeMassCoherent budget)
  in
  subst
    (λ right → maximumDamping budget * negativeMass budget ≤ right)
    (solve
      ( maximumDamping budget
      ∷ coherence budget
      ∷ positiveMass budget
      ∷ []))
    scaled

coherenceGivesPositiveMassMargin :
  ∀ budget →
  netViscousContribution budget
  ≤ - (coerciveMargin budget * positiveMass budget)
coherenceGivesPositiveMassMargin budget =
  let
    endpoint = weightedContributionBelowEndpoint budget
    scaledCoherence = maximumTimesNegativeMassBelowCoherentMass budget
    subtractMinimum = ℚP.+-mono-≤
      scaledCoherence ℚP.≤-refl
    middle :
      maximumDamping budget * negativeMass budget
        - minimumDamping budget * positiveMass budget
      ≤ maximumDamping budget * coherence budget * positiveMass budget
        - minimumDamping budget * positiveMass budget
    middle =
      subst
        (λ left → left ≤
          maximumDamping budget * coherence budget * positiveMass budget
            - minimumDamping budget * positiveMass budget)
        (solve
          ( maximumDamping budget
          ∷ negativeMass budget
          ∷ minimumDamping budget
          ∷ positiveMass budget
          ∷ []))
        (subst
          (λ right →
            maximumDamping budget * negativeMass budget
              + (- (minimumDamping budget * positiveMass budget))
            ≤ right)
          (solve
            ( maximumDamping budget
            ∷ coherence budget
            ∷ positiveMass budget
            ∷ minimumDamping budget
            ∷ []))
          subtractMinimum)
    endpointMeaning :
      maximumDamping budget * coherence budget * positiveMass budget
        - minimumDamping budget * positiveMass budget
      ≡ - (coerciveMargin budget * positiveMass budget)
    endpointMeaning = solve
      ( maximumDamping budget
      ∷ coherence budget
      ∷ minimumDamping budget
      ∷ positiveMass budget
      ∷ [])
  in
  ℚP.≤-trans endpoint
    (subst
      (λ upper →
        maximumDamping budget * negativeMass budget
          - minimumDamping budget * positiveMass budget
        ≤ upper)
      endpointMeaning middle)

coherenceGivesNetTransferMargin :
  ∀ budget →
  0ℚ ≤ coerciveMargin budget →
  netViscousContribution budget
  ≤ - (coerciveMargin budget * netTransfer budget)
coherenceGivesNetTransferMargin budget marginNN =
  let
    toPositive = coherenceGivesPositiveMassMargin budget
    q≤P = netTransferAtMostPositiveMass budget
    marginTimesQ≤marginTimesP :
      coerciveMargin budget * netTransfer budget
      ≤ coerciveMargin budget * positiveMass budget
    marginTimesQ≤marginTimesP =
      let instance marginNNI = nonNegative marginNN
      in ℚP.*-monoˡ-≤-nonNeg (coerciveMargin budget) q≤P
    negateReverses :
      - (coerciveMargin budget * positiveMass budget)
      ≤ - (coerciveMargin budget * netTransfer budget)
    negateReverses = ℚP.neg-antimono-≤ marginTimesQ≤marginTimesP
  in
  ℚP.≤-trans toPositive negateReverses

coherenceThresholdGivesNonnegativeMargin :
  ∀ budget →
  maximumDamping budget * coherence budget ≤ minimumDamping budget →
  0ℚ ≤ coerciveMargin budget
coherenceThresholdGivesNonnegativeMargin budget threshold =
  let
    shifted = ℚP.+-mono-≤ threshold ℚP.≤-refl
  in
  subst
    (λ left → left ≤ coerciveMargin budget)
    (solve
      ( maximumDamping budget
      ∷ coherence budget
      ∷ []))
    (subst
      (λ right →
        maximumDamping budget * coherence budget
          + (- (maximumDamping budget * coherence budget))
        ≤ right)
      (solve
        ( minimumDamping budget
        ∷ maximumDamping budget
        ∷ coherence budget
        ∷ []))
      shifted)

coherenceThresholdNonpositive :
  ∀ budget →
  maximumDamping budget * coherence budget ≤ minimumDamping budget →
  netViscousContribution budget ≤ 0ℚ
coherenceThresholdNonpositive budget threshold =
  let
    marginNN = coherenceThresholdGivesNonnegativeMargin budget threshold
    toMargin = coherenceGivesPositiveMassMargin budget
    productNN :
      0ℚ ≤ coerciveMargin budget * positiveMass budget
    productNN =
      let instance
        marginNNI = nonNegative marginNN
        massNNI = nonNegative (positiveMassNonnegative budget)
        productNNI = ℚP.nonNeg*nonNeg⇒nonNeg
          (coerciveMargin budget) (positiveMass budget)
      in ℚP.nonNegative⁻¹ _
    negProduct≤0 = ℚP.neg-antimono-≤ productNN
  in
  ℚP.≤-trans toMargin negProduct≤0

round88SignedHHViscousCoherenceGateIsCThetaBelowM : Bool
round88SignedHHViscousCoherenceGateIsCThetaBelowM = true

round88AggregatePositiveTransferAloneClosesViscousSign : Bool
round88AggregatePositiveTransferAloneClosesViscousSign = false

round88SignedHHViscousCoherenceGateIsCThetaBelowMIsTrue :
  round88SignedHHViscousCoherenceGateIsCThetaBelowM ≡ true
round88SignedHHViscousCoherenceGateIsCThetaBelowMIsTrue = refl

round88AggregatePositiveTransferAloneClosesViscousSignIsFalse :
  round88AggregatePositiveTransferAloneClosesViscousSign ≡ false
round88AggregatePositiveTransferAloneClosesViscousSignIsFalse = refl
