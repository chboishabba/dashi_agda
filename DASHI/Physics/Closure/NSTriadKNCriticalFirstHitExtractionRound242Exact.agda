module DASHI.Physics.Closure.NSTriadKNCriticalFirstHitExtractionRound242Exact where

------------------------------------------------------------------------
-- ROUND242 / FIRST-HIT CRITICAL-SEQUENCE EXTRACTION
--
-- Round241 gives the decisive contrapositive architecture:
--
--   a uniform H^(1/2) barrier + uniform integrated dissipation
--     => a uniform Q_+- spacetime budget.
--
-- Therefore, if the corrected Round240 physical Galerkin family violates the
-- cutoff-uniform Q_+- budget, its critical H^(1/2) size must cross every fixed
-- finite threshold K along sufficiently bad cutoffs.
--
-- Finite-dimensional Galerkin trajectories are continuous in time.  Hence a
-- fixed threshold K can be converted into FIRST HITTING TIMES t_N(K) with
--
--   A_N(t_N(K)) = K,
--
-- where A_N = ||u_N||_{H^(1/2)}^2.
--
-- This is the noncircular bounded critical sequence required by Gallagher
-- profile decomposition: the selected states are bounded by construction,
-- rather than by assuming Package A.
--
-- The topology/continuity theorem is continuous analysis and is not faked as
-- finite Agda arithmetic here.  Instead the module isolates the exact
-- producer interface and proves the downstream boundedness compiler once a
-- genuine first-hit selector is supplied.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Data.Rational.Base using (ℚ; _≤_)
import Data.Rational.Properties as ℚP

record ThresholdCrossing (Time : Set)
    (criticalSize : Nat → Time → ℚ)
    (threshold : ℚ)
    (cutoff : Nat) : Set where
  constructor threshold-crossing
  field
    crossingTime : Time
    reachesThreshold : threshold ≤ criticalSize cutoff crossingTime

open ThresholdCrossing public

record FirstHitLaw (Time : Set)
    (Before : Time → Time → Set)
    (criticalSize : Nat → Time → ℚ)
    (threshold : ℚ) : Set₁ where
  field
    firstHit :
      (cutoff : Nat) →
      ThresholdCrossing Time criticalSize threshold cutoff → Time

    firstHitExact :
      (cutoff : Nat)
      (crossing : ThresholdCrossing Time criticalSize threshold cutoff) →
      criticalSize cutoff (firstHit cutoff crossing) ≡ threshold

    priorStrictlyBelow :
      (cutoff : Nat)
      (crossing : ThresholdCrossing Time criticalSize threshold cutoff)
      (t : Time) →
      Before t (firstHit cutoff crossing) →
      criticalSize cutoff t ≤ threshold

open FirstHitLaw public

record CriticalFirstHitSequence (Time : Set)
    (criticalSize : Nat → Time → ℚ)
    (threshold : ℚ) : Set where
  constructor critical-first-hit-sequence
  field
    selectedCutoff : Nat → Nat
    selectedTime : Nat → Time
    selectedCriticalSizeExact :
      (n : Nat) →
      criticalSize (selectedCutoff n) (selectedTime n) ≡ threshold

open CriticalFirstHitSequence public

selectedCriticalSizeBounded :
  ∀ {Time criticalSize threshold}
    (S : CriticalFirstHitSequence Time criticalSize threshold) →
    (n : Nat) →
    criticalSize (selectedCutoff S n) (selectedTime S n) ≤ threshold
selectedCriticalSizeBounded S n
  rewrite selectedCriticalSizeExact S n =
  ℚP.≤-refl

firstHitLawBuildsCriticalSequence :
  ∀ {Time Before criticalSize threshold}
    (law : FirstHitLaw Time Before criticalSize threshold)
    (cutoffs : Nat → Nat)
    (crosses : (n : Nat) →
      ThresholdCrossing Time criticalSize threshold (cutoffs n)) →
    CriticalFirstHitSequence Time criticalSize threshold
firstHitLawBuildsCriticalSequence law cutoffs crosses =
  critical-first-hit-sequence
    cutoffs
    (λ n → firstHit law (cutoffs n) (crosses n))
    (λ n → firstHitExact law (cutoffs n) (crosses n))

round242DefectFailureCanBeReducedToThresholdCrossings : Bool
round242DefectFailureCanBeReducedToThresholdCrossings = true

round242FiniteDimensionalCriticalNormContinuityInstalled : Bool
round242FiniteDimensionalCriticalNormContinuityInstalled = false

round242FirstHitSelectorAnalyticInstanceInstalled : Bool
round242FirstHitSelectorAnalyticInstanceInstalled = false

round242FirstHitCompilerProducesBoundedCriticalSequence : Bool
round242FirstHitCompilerProducesBoundedCriticalSequence = true

round242GallagherInputSequenceProducedFromPhysicalFailure : Bool
round242GallagherInputSequenceProducedFromPhysicalFailure = false

round242PackageAClosed : Bool
round242PackageAClosed = false

round242ClayPromotion : Bool
round242ClayPromotion = false

round242DefectFailureCanBeReducedToThresholdCrossingsIsTrue :
  round242DefectFailureCanBeReducedToThresholdCrossings ≡ true
round242DefectFailureCanBeReducedToThresholdCrossingsIsTrue = refl

round242FiniteDimensionalCriticalNormContinuityInstalledIsFalse :
  round242FiniteDimensionalCriticalNormContinuityInstalled ≡ false
round242FiniteDimensionalCriticalNormContinuityInstalledIsFalse = refl

round242FirstHitSelectorAnalyticInstanceInstalledIsFalse :
  round242FirstHitSelectorAnalyticInstanceInstalled ≡ false
round242FirstHitSelectorAnalyticInstanceInstalledIsFalse = refl

round242FirstHitCompilerProducesBoundedCriticalSequenceIsTrue :
  round242FirstHitCompilerProducesBoundedCriticalSequence ≡ true
round242FirstHitCompilerProducesBoundedCriticalSequenceIsTrue = refl

round242GallagherInputSequenceProducedFromPhysicalFailureIsFalse :
  round242GallagherInputSequenceProducedFromPhysicalFailure ≡ false
round242GallagherInputSequenceProducedFromPhysicalFailureIsFalse = refl

round242PackageAClosedIsFalse : round242PackageAClosed ≡ false
round242PackageAClosedIsFalse = refl

round242ClayPromotionIsFalse : round242ClayPromotion ≡ false
round242ClayPromotionIsFalse = refl
