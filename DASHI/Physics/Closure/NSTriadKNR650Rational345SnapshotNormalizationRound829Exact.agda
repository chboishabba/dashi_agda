{-# OPTIONS --safe #-}
module DASHI.Physics.Closure.NSTriadKNR650Rational345SnapshotNormalizationRound829Exact where

------------------------------------------------------------------------
-- R829 / EXACT RATIONAL 3-4-5 SNAPSHOT NORMALIZATION RECEIPT
--
-- R828 independently evaluates the radius-four rational 3-4-5 snapshot:
--
--   coherent commutator work = -557627 / 125
--   critical production      = 0
--   critical dissipation     = 15834
--
-- R815's canonical nu=delta=1 convention consumes these as
--
--   6 * (12 * coherentWork - criticalProduction + criticalDissipation).
--
-- This owner kernel-checks that normalization and its strict sign.  It also
-- makes the remaining same-object boundary explicit: an actual repository
-- snapshot evaluation must identify R230/R692/R744 with the three scalars.
-- No R408 real-time rational trajectory is assumed or fabricated here.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Integer.Base using (+_)
open import Data.Rational.Base using
  (ℚ; 0ℚ; _+_; _-_; _*_; _/_; -_; _<_)
import Data.Rational.Properties as ℚP
open import Data.Rational.Tactic.RingSolver using (solve)
open import Relation.Binary.PropositionalEquality using (cong; subst; sym; trans)
open import Relation.Nullary.Decidable.Core using (toWitness)

coherentWork345 : ℚ
coherentWork345 = - ((+ 557627) / 125)

criticalProduction345 : ℚ
criticalProduction345 = 0ℚ

criticalDissipation345 : ℚ
criticalDissipation345 = 15834

canonicalSignedRate :
  ℚ → ℚ → ℚ → ℚ
canonicalSignedRate coherent production dissipation =
  6 * (12 * coherent - production + dissipation)

expectedRate345 : ℚ
expectedRate345 = - ((+ 28273644) / 125)

canonical345RateExact :
  canonicalSignedRate
    coherentWork345 criticalProduction345 criticalDissipation345
  ≡ expectedRate345
canonical345RateExact = solve []

expectedRate345Negative : expectedRate345 < 0ℚ
expectedRate345Negative =
  toWitness (ℚP._<?_ expectedRate345 0ℚ)

canonical345RateNegative :
  canonicalSignedRate
    coherentWork345 criticalProduction345 criticalDissipation345
  < 0ℚ
canonical345RateNegative =
  subst (_< 0ℚ) (sym canonical345RateExact) expectedRate345Negative

------------------------------------------------------------------------
-- The exact remaining R829 physical identification.
--
-- This record is intentionally only an interface for the concrete component
-- evaluator.  Supplying it requires proofs about the ACTUAL repository
-- R230/R692/R744 values at the selected finite Fourier state.
------------------------------------------------------------------------

record Repository345SnapshotIdentification
    (repositoryCoherentWork
     repositoryCriticalProduction
     repositoryCriticalDissipation : ℚ) : Set where
  field
    coherentWorkSameObject :
      repositoryCoherentWork ≡ coherentWork345
    criticalProductionSameObject :
      repositoryCriticalProduction ≡ criticalProduction345
    criticalDissipationSameObject :
      repositoryCriticalDissipation ≡ criticalDissipation345

open Repository345SnapshotIdentification public

identifiedCanonicalRateExact :
  (repositoryCoherentWork
   repositoryCriticalProduction
   repositoryCriticalDissipation : ℚ) →
  Repository345SnapshotIdentification
    repositoryCoherentWork
    repositoryCriticalProduction
    repositoryCriticalDissipation →
  canonicalSignedRate
    repositoryCoherentWork
    repositoryCriticalProduction
    repositoryCriticalDissipation
  ≡ expectedRate345
identifiedCanonicalRateExact c p d identification
  rewrite coherentWorkSameObject identification
        | criticalProductionSameObject identification
        | criticalDissipationSameObject identification =
  canonical345RateExact

identifiedCanonicalRateNegative :
  (repositoryCoherentWork
   repositoryCriticalProduction
   repositoryCriticalDissipation : ℚ) →
  Repository345SnapshotIdentification
    repositoryCoherentWork
    repositoryCriticalProduction
    repositoryCriticalDissipation →
  canonicalSignedRate
    repositoryCoherentWork
    repositoryCriticalProduction
    repositoryCriticalDissipation
  < 0ℚ
identifiedCanonicalRateNegative c p d identification =
  subst (_< 0ℚ)
    (sym (identifiedCanonicalRateExact c p d identification))
    expectedRate345Negative

------------------------------------------------------------------------
-- Trust/status boundary.
------------------------------------------------------------------------

round829R815NormalizationArithmeticClosed : Bool
round829R815NormalizationArithmeticClosed = true

round829RationalStrictNegativeRateClosed : Bool
round829RationalStrictNegativeRateClosed = true

round829R230R692R744ConcreteSameObjectEvaluationClosed : Bool
round829R230R692R744ConcreteSameObjectEvaluationClosed = false

round829R408RealTimeTrajectoryRequiredForSnapshotTheorem : Bool
round829R408RealTimeTrajectoryRequiredForSnapshotTheorem = false

round829IntegratedR823CounterexampleClosed : Bool
round829IntegratedR823CounterexampleClosed = false

round829ClayPromotion : Bool
round829ClayPromotion = false

round829R815NormalizationArithmeticClosedIsTrue :
  round829R815NormalizationArithmeticClosed ≡ true
round829R815NormalizationArithmeticClosedIsTrue = refl

round829R230R692R744ConcreteSameObjectEvaluationClosedIsFalse :
  round829R230R692R744ConcreteSameObjectEvaluationClosed ≡ false
round829R230R692R744ConcreteSameObjectEvaluationClosedIsFalse = refl
