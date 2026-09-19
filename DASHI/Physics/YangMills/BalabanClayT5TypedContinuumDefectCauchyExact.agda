{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.BalabanClayT5TypedContinuumDefectCauchyExact where

------------------------------------------------------------------------
-- TYPED T5 CONTINUUM DEFECT TELESCOPING -> EXPLICIT CAUCHY MODULUS
--
-- The historical configured T5 ABI stores
--
--   expectationDifferenceIsDefect
--   finiteTailControlsTelescopingDifference
--   continuumDefectLimitExists
--
-- only as Set-valued names.  They cannot consume the rational dyadic theorem
-- proved in BalabanClayT5ConfiguredDyadicTailSummationExact.
--
-- This module strengthens exactly the two physical facts needed for the
-- quantitative continuum argument, on the SAME existing physical instance:
--
--   (1) |delta_k(O)| <= (1/4) 2^{-k};
--   (2) E_k(O) - E_{k+N}(O) is exactly the signed finite defect sum.
--
-- The absolute finite-tail estimate and uniform Cauchy modulus are then
-- machine theorems.  No rational limit is manufactured here: ℚ is not
-- complete, so passage from this modulus to an actual continuum expectation
-- belongs to the repository's completion / measure-topology machinery.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Data.Rational.Base as ℚ using
  (ℚ; 0ℚ; _+_; _-_; _≤_; ∣_∣)
import Data.Rational.Properties as ℚP
open import Relation.Binary.PropositionalEquality using (subst; sym; trans)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Analysis.CanonicalRationalMetric as Metric
import DASHI.Physics.YangMills.BalabanClayT5ConfiguredGeometricTailExact as Tail
import DASHI.Physics.YangMills.BalabanClayT5ConfiguredPhysicalTailMomentInstanceExact as Configured
import DASHI.Physics.YangMills.BalabanClayT5ConfiguredDyadicTailSummationExact as Sum

------------------------------------------------------------------------
-- Literal successor iteration used by the exact telescoping endpoint.
-- Keeping this recursive definition local avoids smuggling in a separate
-- cutoff arithmetic convention.
------------------------------------------------------------------------

advance : Nat → Nat → Nat
advance start zero = start
advance start (suc count) = advance (suc start) count

record TypedContinuumDefectCauchyUpgrade (Observable : Set) : Set₁ where
  field
    legacy : Configured.PhysicalContinuumDefectInstance Observable

    -- This is the physically correct strengthening of the old signed upper
    -- bound when the consumer is a metric/Cauchy theorem.
    oneStepDefectAbsoluteBound :
      ∀ cutoff observable →
      ∣ Configured.oneStepDefect legacy cutoff observable ∣
      ≤ Tail.rootedShellTail cutoff

    -- Same-object typed replacement for the old Set-valued telescoping name.
    telescopingExpectationDifferenceExact :
      ∀ start count observable →
      Configured.expectation legacy start observable
        - Configured.expectation legacy (advance start count) observable
      ≡ Sum.defectPartial
          (λ cutoff →
            Configured.oneStepDefect legacy cutoff observable)
          start count

open TypedContinuumDefectCauchyUpgrade public

------------------------------------------------------------------------
-- Absolute finite defect sum.
------------------------------------------------------------------------

absoluteDefectPartialBelowFiniteDyadicTail :
  ∀ {Observable} →
  (dataSet : TypedContinuumDefectCauchyUpgrade Observable) →
  ∀ start count observable →
  ∣ Sum.defectPartial
      (λ cutoff →
        Configured.oneStepDefect (legacy dataSet) cutoff observable)
      start count ∣
  ≤ Configured.finiteDyadicTail start count
absoluteDefectPartialBelowFiniteDyadicTail dataSet start zero observable
  rewrite Metric.absZeroℚ =
  ℚP.≤-refl
absoluteDefectPartialBelowFiniteDyadicTail dataSet start (suc count) observable =
  ℚP.≤-trans
    (ℚP.∣p+q∣≤∣p∣+∣q∣
      (Configured.oneStepDefect (legacy dataSet) start observable)
      (Sum.defectPartial
        (λ cutoff →
          Configured.oneStepDefect (legacy dataSet) cutoff observable)
        (suc start) count))
    (ℚP.+-mono-≤
      (oneStepDefectAbsoluteBound dataSet start observable)
      (absoluteDefectPartialBelowFiniteDyadicTail
        dataSet (suc start) count observable))

absoluteDefectPartialBelowInfiniteMajorant :
  ∀ {Observable} →
  (dataSet : TypedContinuumDefectCauchyUpgrade Observable) →
  ∀ start count observable →
  ∣ Sum.defectPartial
      (λ cutoff →
        Configured.oneStepDefect (legacy dataSet) cutoff observable)
      start count ∣
  ≤ Configured.configuredInfiniteTailMajorant start
absoluteDefectPartialBelowInfiniteMajorant dataSet start count observable =
  trans
    (absoluteDefectPartialBelowFiniteDyadicTail
      dataSet start count observable)
    (Sum.configuredFiniteDyadicTailBelowInfiniteMajorant start count)

------------------------------------------------------------------------
-- Exact physical telescoping + absolute defect summation -> Cauchy modulus.
------------------------------------------------------------------------

expectationDifferenceBelowFiniteDyadicTail :
  ∀ {Observable} →
  (dataSet : TypedContinuumDefectCauchyUpgrade Observable) →
  ∀ start count observable →
  ∣ Configured.expectation (legacy dataSet) start observable
      - Configured.expectation
          (legacy dataSet) (advance start count) observable ∣
  ≤ Configured.finiteDyadicTail start count
expectationDifferenceBelowFiniteDyadicTail dataSet start count observable =
  subst
    (λ difference →
      ∣ difference ∣ ≤ Configured.finiteDyadicTail start count)
    (sym
      (telescopingExpectationDifferenceExact
        dataSet start count observable))
    (absoluteDefectPartialBelowFiniteDyadicTail
      dataSet start count observable)

expectationCauchyModulus :
  ∀ {Observable} →
  (dataSet : TypedContinuumDefectCauchyUpgrade Observable) →
  ∀ start count observable →
  ∣ Configured.expectation (legacy dataSet) start observable
      - Configured.expectation
          (legacy dataSet) (advance start count) observable ∣
  ≤ Configured.configuredInfiniteTailMajorant start
expectationCauchyModulus dataSet start count observable =
  trans
    (expectationDifferenceBelowFiniteDyadicTail
      dataSet start count observable)
    (Sum.configuredFiniteDyadicTailBelowInfiniteMajorant start count)

------------------------------------------------------------------------
-- Canonical proposition exported to legacy/topology consumers.
------------------------------------------------------------------------

ExpectationHasConfiguredCauchyModulus :
  ∀ {Observable} →
  TypedContinuumDefectCauchyUpgrade Observable →
  Observable → Set
ExpectationHasConfiguredCauchyModulus dataSet observable =
  ∀ start count →
  ∣ Configured.expectation (legacy dataSet) start observable
      - Configured.expectation
          (legacy dataSet) (advance start count) observable ∣
  ≤ Configured.configuredInfiniteTailMajorant start

expectationHasConfiguredCauchyModulus :
  ∀ {Observable} →
  (dataSet : TypedContinuumDefectCauchyUpgrade Observable) →
  ∀ observable →
  ExpectationHasConfiguredCauchyModulus dataSet observable
expectationHasConfiguredCauchyModulus dataSet observable =
  λ start count →
    expectationCauchyModulus dataSet start count observable

typedAbsoluteDefectSummationLevel : ProofLevel
typedAbsoluteDefectSummationLevel = machineChecked

typedTelescopingToCauchyCompilerLevel : ProofLevel
typedTelescopingToCauchyCompilerLevel = machineChecked

physicalAbsoluteOneStepDefectLevel : ProofLevel
physicalAbsoluteOneStepDefectLevel = conditional

physicalTypedTelescopingIdentityLevel : ProofLevel
physicalTypedTelescopingIdentityLevel = conditional

-- Deliberately not promoted: a Cauchy sequence of rationals need not converge
-- to a rational.  Completion/continuum-measure realization remains downstream.
rationalLimitExistenceFromCauchyAloneLevel : ProofLevel
rationalLimitExistenceFromCauchyAloneLevel = conjectural
