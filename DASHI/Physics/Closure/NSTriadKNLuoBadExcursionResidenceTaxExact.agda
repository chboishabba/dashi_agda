module DASHI.Physics.Closure.NSTriadKNLuoBadExcursionResidenceTaxExact where

------------------------------------------------------------------------
-- PRIMARY CONTEXT
--
-- Author: Runlong Yu.
-- Title: "A Structural Audit of Navier-Stokes Obstruction Calculus".
-- DOI: 10.48550/arXiv.2606.25341.
--
-- Author: Runlong Yu.
-- Title: "Filtered Vortex Stretching and Subgrid Defects for the
-- Three-Dimensional Navier-Stokes Equations".
-- DOI: 10.48550/arXiv.2606.27560.
--
-- Author: Runlong Yu.
-- Title: "Invisible Defect Cascades for Navier-Stokes Regularity".
-- DOI: 10.48550/arXiv.2606.12756.
--
-- DASHI CONTRIBUTION
--
-- This is the deterministic core of K8.  On each bad excursion interval,
-- suppose
--
--   a_right + lambda * integral(a) <= a_left + integral(f_+)
--
-- and badness supplies
--
--   threshold * duration <= integral(a).
--
-- Then
--
--   lambda * threshold * duration
--     <= a_left + integral(f_+).
--
-- Recursive finite summation keeps every excursion-entry charge explicit.
-- A separate boundary-crossing budget converts the sum of entry charges into
-- initial defect plus crossing cost.  Thus a residence estimate is not
-- obtained merely by saying the bad set is short: recurrence must pay through
-- forcing or boundary crossings.
------------------------------------------------------------------------

open import Agda.Builtin.List using (List; []; _∷_)
open import Data.Rational.Base using
  (ℚ; 0ℚ; _+_; _*_; _≤_; nonNegative)
import Data.Rational.Properties as ℚₚ
open import Data.Rational.Tactic.RingSolver using (solve)
open import Relation.Binary.PropositionalEquality using (_≡_; subst)

import DASHI.Physics.Closure.NSTriadKNRationalOrderedFiniteL2 as L2

record ExcursionTaxParameters : Set where
  constructor excursionTaxParameters
  field
    damping threshold : ℚ
    dampingNonnegative : 0ℚ ≤ damping
    thresholdNonnegative : 0ℚ ≤ threshold

open ExcursionTaxParameters public

record BadExcursionInterval (parameters : ExcursionTaxParameters) : Set where
  constructor badExcursionInterval
  field
    leftDefect rightDefect integratedDefect positiveForcing duration : ℚ

    leftDefectNonnegative : 0ℚ ≤ leftDefect
    rightDefectNonnegative : 0ℚ ≤ rightDefect
    integratedDefectNonnegative : 0ℚ ≤ integratedDefect
    positiveForcingNonnegative : 0ℚ ≤ positiveForcing
    durationNonnegative : 0ℚ ≤ duration

    integratedEvolutionTax :
      rightDefect + damping parameters * integratedDefect
      ≤ leftDefect + positiveForcing

    badThresholdLowerBound :
      threshold parameters * duration ≤ integratedDefect

open BadExcursionInterval public

thresholdDurationNonnegative :
  ∀ {parameters}
    (interval : BadExcursionInterval parameters) →
  0ℚ ≤ threshold parameters * duration interval
thresholdDurationNonnegative {parameters} interval =
  let
    instance
      thresholdNN = nonNegative (thresholdNonnegative parameters)
      durationNN = nonNegative (durationNonnegative interval)
      productNN =
        ℚₚ.nonNeg*nonNeg⇒nonNeg
          (threshold parameters) (duration interval)
  in
  ℚₚ.nonNegative⁻¹
    (threshold parameters * duration interval)

dampedThresholdBelowDampedDefect :
  ∀ {parameters}
    (interval : BadExcursionInterval parameters) →
  damping parameters *
    (threshold parameters * duration interval)
  ≤ damping parameters * integratedDefect interval
dampedThresholdBelowDampedDefect {parameters} interval =
  L2.nonnegativeProductMonotone
    (dampingNonnegative parameters)
    (thresholdDurationNonnegative interval)
    (dampingNonnegative parameters)
    (integratedDefectNonnegative interval)
    ℚₚ.≤-refl
    (badThresholdLowerBound interval)

dampedDefectBelowEvolutionBudget :
  ∀ {parameters}
    (interval : BadExcursionInterval parameters) →
  damping parameters * integratedDefect interval
  ≤ leftDefect interval + positiveForcing interval
dampedDefectBelowEvolutionBudget {parameters} interval =
  let
    damped = damping parameters * integratedDefect interval

    addRight :
      0ℚ + damped ≤ rightDefect interval + damped
    addRight =
      ℚₚ.+-mono-≤
        (rightDefectNonnegative interval)
        ℚₚ.≤-refl

    leftClosed : 0ℚ + damped ≡ damped
    leftClosed = solve (damped ∷ [])

    dampedBelowWithRight :
      damped ≤ rightDefect interval + damped
    dampedBelowWithRight =
      subst
        (λ left → left ≤ rightDefect interval + damped)
        leftClosed
        addRight
  in
  ℚₚ.≤-trans
    dampedBelowWithRight
    (integratedEvolutionTax interval)

localBadExcursionResidenceTax :
  ∀ {parameters}
    (interval : BadExcursionInterval parameters) →
  damping parameters * threshold parameters * duration interval
  ≤ leftDefect interval + positiveForcing interval
localBadExcursionResidenceTax {parameters} interval =
  let
    scaled = dampedThresholdBelowDampedDefect interval

    reassociated :
      damping parameters *
        (threshold parameters * duration interval)
      ≡ damping parameters * threshold parameters * duration interval
    reassociated =
      solve
        ( damping parameters
        ∷ threshold parameters
        ∷ duration interval
        ∷ [])

    normalized :
      damping parameters * threshold parameters * duration interval
      ≤ damping parameters * integratedDefect interval
    normalized =
      subst
        (λ left →
          left ≤ damping parameters * integratedDefect interval)
        reassociated
        scaled
  in
  ℚₚ.≤-trans normalized (dampedDefectBelowEvolutionBudget interval)

totalBadDuration :
  ∀ {parameters} → List (BadExcursionInterval parameters) → ℚ
totalBadDuration [] = 0ℚ
totalBadDuration (interval ∷ intervals) =
  duration interval + totalBadDuration intervals

totalEntryCharge :
  ∀ {parameters} → List (BadExcursionInterval parameters) → ℚ
totalEntryCharge [] = 0ℚ
totalEntryCharge (interval ∷ intervals) =
  leftDefect interval + totalEntryCharge intervals

totalPositiveForcing :
  ∀ {parameters} → List (BadExcursionInterval parameters) → ℚ
totalPositiveForcing [] = 0ℚ
totalPositiveForcing (interval ∷ intervals) =
  positiveForcing interval + totalPositiveForcing intervals

finiteBadExcursionResidenceTax :
  ∀ {parameters}
    (intervals : List (BadExcursionInterval parameters)) →
  damping parameters * threshold parameters * totalBadDuration intervals
  ≤ totalEntryCharge intervals + totalPositiveForcing intervals
finiteBadExcursionResidenceTax [] = ℚₚ.≤-refl
finiteBadExcursionResidenceTax {parameters} (interval ∷ intervals) =
  let
    local = localBadExcursionResidenceTax interval
    tail = finiteBadExcursionResidenceTax intervals
    summed = ℚₚ.+-mono-≤ local tail

    leftMeaning :
      damping parameters * threshold parameters * duration interval
      + damping parameters * threshold parameters
        * totalBadDuration intervals
      ≡
      damping parameters * threshold parameters
        * (duration interval + totalBadDuration intervals)
    leftMeaning =
      solve
        ( damping parameters
        ∷ threshold parameters
        ∷ duration interval
        ∷ totalBadDuration intervals
        ∷ [])

    rightMeaning :
      (leftDefect interval + positiveForcing interval)
      + (totalEntryCharge intervals + totalPositiveForcing intervals)
      ≡
      (leftDefect interval + totalEntryCharge intervals)
      + (positiveForcing interval + totalPositiveForcing intervals)
    rightMeaning =
      solve
        ( leftDefect interval
        ∷ positiveForcing interval
        ∷ totalEntryCharge intervals
        ∷ totalPositiveForcing intervals
        ∷ [])
  in
  subst
    (λ left →
      left
      ≤ (leftDefect interval + totalEntryCharge intervals)
        + (positiveForcing interval + totalPositiveForcing intervals))
    leftMeaning
    (subst
      (λ right →
        damping parameters * threshold parameters * duration interval
        + damping parameters * threshold parameters
          * totalBadDuration intervals
        ≤ right)
      rightMeaning
      summed)

record ExcursionBoundaryBudget
    {parameters : ExcursionTaxParameters}
    (intervals : List (BadExcursionInterval parameters)) : Set where
  constructor excursionBoundaryBudget
  field
    initialDefect crossingCharge : ℚ
    initialDefectNonnegative : 0ℚ ≤ initialDefect
    crossingChargeNonnegative : 0ℚ ≤ crossingCharge
    entryChargesPaid :
      totalEntryCharge intervals ≤ initialDefect + crossingCharge

open ExcursionBoundaryBudget public

badResidenceWithCrossingBudget :
  ∀ {parameters intervals}
    (budget : ExcursionBoundaryBudget {parameters} intervals) →
  damping parameters * threshold parameters * totalBadDuration intervals
  ≤
  initialDefect budget
  + crossingCharge budget
  + totalPositiveForcing intervals
badResidenceWithCrossingBudget {parameters} {intervals} budget =
  let
    residence = finiteBadExcursionResidenceTax intervals
    forcing = totalPositiveForcing intervals

    rawWithForcing :
      forcing + totalEntryCharge intervals
      ≤ forcing + (initialDefect budget + crossingCharge budget)
    rawWithForcing =
      ℚₚ.+-monoʳ-≤ forcing (entryChargesPaid budget)

    withForcing :
      totalEntryCharge intervals + forcing
      ≤
      (initialDefect budget + crossingCharge budget) + forcing
    withForcing =
      subst
        (λ left →
          left ≤ (initialDefect budget + crossingCharge budget) + forcing)
        (solve (forcing ∷ totalEntryCharge intervals ∷ []))
        (subst
          (λ right → forcing + totalEntryCharge intervals ≤ right)
          (solve
            ( forcing ∷ initialDefect budget
            ∷ crossingCharge budget ∷ []))
          rawWithForcing)
  in
  ℚₚ.≤-trans residence withForcing

record ResidenceTaxAuthorityBoundary : Set where
  constructor residenceTaxAuthorityBoundary
  field
    deterministicIntervalTaxProved : Set
    finiteExcursionSummationProved : Set
    boundaryCrossingChargeExposed : Set
    navierStokesCrossingBudgetProduced : Set

canonicalResidenceTaxAuthorityBoundary :
  ResidenceTaxAuthorityBoundary
canonicalResidenceTaxAuthorityBoundary =
  residenceTaxAuthorityBoundary ⊤ ⊤ ⊤ ⊥
  where
  open import Data.Unit using (⊤)
  open import Data.Empty using (⊥)
