module DASHI.Physics.YangMills.BalabanBetaHistoryLocalizedInfluenceExact where

------------------------------------------------------------------------
-- ROUND82/83: LOCALIZED IRRELEVANT MEMORY -> UNIFORM BETA CORRECTION
--
-- PRIMARY SOURCE / MOTIVATION
--
-- Tadeusz Bałaban,
-- "Renormalization Group Approach to Lattice Gauge Field Theories. I.
-- Generation of Effective Actions in a Small Field Approximation and a
-- Coupling Constant Renormalization in Four Dimensions",
-- Communications in Mathematical Physics 109 (1987), 249--301.
-- DOI: 10.1007/BF01215223.
--
-- CORRECTION OF THE ROUND82 INTERPRETATION
--
-- At the end of Sect. 5 Bałaban explicitly says beta_j depends on all preceding
-- coupling constants and that the dependence on g_{j-1} is important for the RG
-- equations.  A marginal running coupling must therefore NOT be assigned an
-- artificial exponential-forgetting law.
--
-- The geometric shell below is only for the IRRELEVANT / localized memory
-- channel after the current marginal data have been held fixed.  The current-
-- step/marginal nonlinear correction is a separate regular-remainder budget.
--
-- Thus the safe decomposition is schematically
--
--   beta_j = b_G + r_local(g_{j-1}, declared marginal data)
--                  + r_irrelevant-memory(history),
--
-- and only the last term is controlled here.
--
-- DASHI CONTRIBUTION
--
-- If an irrelevant-memory difference is resolved into shells with
--
--   memoryDifference <= sum influence_d,
--   influence_d <= C gamma (1/4) 2^{-d},
--
-- then every finite irrelevant-memory correction is bounded by C gamma / 2,
-- independently of the number of RG steps.  The theorem is generic and remains
-- useful, but it is NOT a theorem that the marginal coupling trajectory itself
-- forgets exponentially.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Nat using (Nat)
open import Data.Rational.Base as ℚ using (ℚ; 0ℚ; _+_; _*_; _≤_)
import Data.Rational.Properties as ℚP
import Data.Rational.Tactic.RingSolver as ℚRing
open import Relation.Binary.PropositionalEquality using (subst)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanContinuumScaleLocalObservableCauchyExact as Scale
import DASHI.Physics.YangMills.BalabanTraceKoteckyPreissGeometricExact as Geo

record LocalizedBetaHistoryInfluence : Set₁ where
  field
    coefficient gamma : ℚ
    coefficientNonnegative : 0ℚ ≤ coefficient
    gammaNonnegative : 0ℚ ≤ gamma

    influenceMajorant : Scale.ScaleLocalIncrementMajorant
    majorantCoefficientExact :
      Scale.coefficient influenceMajorant ≡ coefficient * gamma

    -- Backward-compatible field name.  Semantically this is an
    -- IRRELEVANT-MEMORY difference at fixed declared marginal data.
    historyDifference : Nat → Nat → ℚ
    historyDifferenceNonnegative : ∀ start count →
      0ℚ ≤ historyDifference start count
    historyDifferenceBelowInfluenceTail : ∀ start count →
      historyDifference start count
      ≤ Scale.scaleIncrementTail influenceMajorant start count

open LocalizedBetaHistoryInfluence public

irrelevantMemoryDifference :
  LocalizedBetaHistoryInfluence → Nat → Nat → ℚ
irrelevantMemoryDifference = historyDifference

historyDifferenceUniform :
  (dataSet : LocalizedBetaHistoryInfluence) → ∀ start count →
  historyDifference dataSet start count
  ≤ (coefficient dataSet * gamma dataSet)
      * (Geo.half * Geo.halfPower start)
historyDifferenceUniform dataSet start count =
  let
    tail = Scale.scaleLocalCauchyTail
      (influenceMajorant dataSet) start count
  in
  ℚP.≤-trans
    (historyDifferenceBelowInfluenceTail dataSet start count)
    (subst
      (λ c → Scale.scaleIncrementTail (influenceMajorant dataSet) start count
        ≤ c * (Geo.half * Geo.halfPower start))
      (majorantCoefficientExact dataSet)
      tail)

historyDifferenceFromPresentScale :
  (dataSet : LocalizedBetaHistoryInfluence) → ∀ count →
  historyDifference dataSet 0 count
  ≤ (coefficient dataSet * gamma dataSet) * Geo.half
historyDifferenceFromPresentScale dataSet count =
  subst
    (λ right → historyDifference dataSet 0 count ≤ right)
    (ℚRing.solve-∀
      (coefficient dataSet) (gamma dataSet) Geo.half
      (Geo.halfPower 0))
    (historyDifferenceUniform dataSet 0 count)

record PositiveReferenceAgainstIrrelevantMemory
    (history : LocalizedBetaHistoryInfluence) : Set₁ where
  field
    -- This reference may already include the declared current/marginal local
    -- remainder.  It need not be the zero-history Gaussian coefficient.
    referenceCoefficient : ℚ
    fullBeta : Nat → ℚ

    referenceCoefficientNonnegative : 0ℚ ≤ referenceCoefficient

    memoryBudgetFitsHalfReference :
      (coefficient history * gamma history) * Geo.half
      + referenceCoefficient * Geo.half
      ≤ referenceCoefficient

    betaAboveReferenceMinusMemory : ∀ count →
      referenceCoefficient
      ≤ fullBeta count + historyDifference history 0 count

open PositiveReferenceAgainstIrrelevantMemory public

fullBetaKeepsHalfReference :
  ∀ {history}
    (dataSet : PositiveReferenceAgainstIrrelevantMemory history) count →
  referenceCoefficient dataSet * Geo.half ≤ fullBeta dataSet count
fullBetaKeepsHalfReference {history} dataSet count =
  let
    h = historyDifference history 0 count
    hBound = historyDifferenceFromPresentScale history count
    budget = memoryBudgetFitsHalfReference dataSet

    halfPlusHBelowReference :
      referenceCoefficient dataSet * Geo.half + h
      ≤ referenceCoefficient dataSet
    halfPlusHBelowReference =
      ℚP.≤-trans
        (ℚP.+-mono-≤ ℚP.≤-refl hBound)
        (subst
          (λ left → left ≤ referenceCoefficient dataSet)
          (ℚRing.solve-∀
            (referenceCoefficient dataSet)
            (coefficient history * gamma history)
            Geo.half)
          budget)

    chained :
      referenceCoefficient dataSet * Geo.half + h
      ≤ fullBeta dataSet count + h
    chained = ℚP.≤-trans halfPlusHBelowReference
      (betaAboveReferenceMinusMemory dataSet count)
  in
  ℚP.+-cancelʳ-≤ h chained

localizedBetaHistoryInfluenceCompilerLevel : ProofLevel
localizedBetaHistoryInfluenceCompilerLevel = machineChecked

localizedBetaIrrelevantMemoryCompilerLevel : ProofLevel
localizedBetaIrrelevantMemoryCompilerLevel = machineChecked

-- Correct physical target: prove a summable influence only for the localized
-- irrelevant/polymer memory at fixed declared marginal data.  The local
-- current-coupling/Bishop remainder is budgeted separately.
literalBetaIrrelevantMemoryInfluenceLevel : ProofLevel
literalBetaIrrelevantMemoryInfluenceLevel = conditional

-- Compatibility name retained, with corrected semantics above.
literalBetaLocalizedHistoryInfluenceLevel : ProofLevel
literalBetaLocalizedHistoryInfluenceLevel = conditional
