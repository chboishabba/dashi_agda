module DASHI.Physics.YangMills.BalabanClayGate4BlockAveragingResidualSummabilityExact where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Data.Integer.Base using (+_)
open import Data.Rational using (ℚ; 0ℚ; 1ℚ; _*_; _≤_; _/_)
import Data.Rational.Tactic.RingSolver as ℚRing
open import Relation.Binary.PropositionalEquality using (subst)

open import DASHI.Physics.YangMills.CompactLieProofLevel

------------------------------------------------------------------------
-- Primary and locator provenance.
--
-- Tadeusz Bałaban,
-- "Renormalization Group Approach to Lattice Gauge Field Theories. II.
-- Cluster Expansions", Communications in Mathematical Physics 116 (1988),
-- 1--22. DOI: 10.1007/BF01239022.
--
-- Tadeusz Bałaban,
-- "Convergent Renormalization Expansions for Lattice Gauge Theories",
-- Communications in Mathematical Physics 119 (1988), 243--285.
-- DOI: 10.1007/BF01217741.
--
-- Lluis Eriksson,
-- "Uniform Poincare Inequality for Lattice Yang-Mills Theory Via Multiscale
-- Martingale Decomposition", ai.viXra:2602.0040, no DOI.
-- Status: not admissible as theorem authority. It is retained only as a
-- mechanism locator for the proposed squared-adjoint factor 2^{-3k}; its
-- RG-normalized disintegration is explicitly conditional.
--
-- This module proves the independent implication actually needed by DASHI:
-- residual growth <= 4 per step and squared-adjoint decay = 1/8 per step give
-- a combined contraction <= 1/2. No claim that the physical Q_k^* has this
-- norm is imported from the locator.
------------------------------------------------------------------------

oneEighth four half : ℚ
oneEighth = + 1 / 8
four = + 4 / 1
half = + 1 / 2

fourTimesOneEighth : four * oneEighth ≡ half
fourTimesOneEighth = ℚRing.solve-∀
powEighth : Nat → ℚ
powEighth zero = 1ℚ
powEighth (suc scale) = oneEighth * powEighth scale

powEighthStepExact : ∀ scale →
  powEighth (suc scale) ≡ oneEighth * powEighth scale
powEighthStepExact scale = refl

record BlockAveragingResidualEnvelope : Set₁ where
  field
    residualEnvelope : Nat → ℚ

    reflexive : ∀ value → value ≤ value
    transitive : ∀ {left middle right} →
      left ≤ middle → middle ≤ right → left ≤ right
    multiplyNonnegative : ∀ {left right} →
      0ℚ ≤ left → 0ℚ ≤ right → 0ℚ ≤ left * right
    multiplyMonotoneNonnegative :
      ∀ {left leftUpper right rightUpper} →
      0ℚ ≤ left → 0ℚ ≤ leftUpper →
      0ℚ ≤ right → 0ℚ ≤ rightUpper →
      left ≤ leftUpper → right ≤ rightUpper →
      left * right ≤ leftUpper * rightUpper

    oneNonnegative : 0ℚ ≤ 1ℚ
    oneEighthNonnegative : 0ℚ ≤ oneEighth
    fourNonnegative : 0ℚ ≤ four
    halfNonnegative : 0ℚ ≤ half

    residualNonnegative : ∀ scale → 0ℚ ≤ residualEnvelope scale
    residualGrowthAtMostFour : ∀ scale →
      residualEnvelope (suc scale) ≤ four * residualEnvelope scale

open BlockAveragingResidualEnvelope public

weightedResidual : BlockAveragingResidualEnvelope → Nat → ℚ
weightedResidual dataSet scale =
  residualEnvelope dataSet scale * powEighth scale

powEighthNonnegative :
  (dataSet : BlockAveragingResidualEnvelope) →
  ∀ scale → 0ℚ ≤ powEighth scale
powEighthNonnegative dataSet zero = oneNonnegative dataSet
powEighthNonnegative dataSet (suc scale) =
  multiplyNonnegative dataSet
    (oneEighthNonnegative dataSet)
    (powEighthNonnegative dataSet scale)

weightedResidualNonnegative :
  (dataSet : BlockAveragingResidualEnvelope) →
  ∀ scale → 0ℚ ≤ weightedResidual dataSet scale
weightedResidualNonnegative dataSet scale =
  multiplyNonnegative dataSet
    (residualNonnegative dataSet scale)
    (powEighthNonnegative dataSet scale)

fourResidualNonnegative :
  (dataSet : BlockAveragingResidualEnvelope) →
  ∀ scale → 0ℚ ≤ four * residualEnvelope dataSet scale
fourResidualNonnegative dataSet scale =
  multiplyNonnegative dataSet
    (fourNonnegative dataSet)
    (residualNonnegative dataSet scale)

weightedResidualStepEquation :
  ∀ R P →
  four * R * (oneEighth * P) ≡ half * (R * P)
weightedResidualStepEquation = ℚRing.solve-∀

weightedResidualStepBelowHalf :
  (dataSet : BlockAveragingResidualEnvelope) →
  ∀ scale →
  weightedResidual dataSet (suc scale)
  ≤ half * weightedResidual dataSet scale
weightedResidualStepBelowHalf dataSet scale =
  subst
    (λ upper → weightedResidual dataSet (suc scale) ≤ upper)
    (weightedResidualStepEquation (residualEnvelope dataSet scale) (powEighth scale))
    (multiplyMonotoneNonnegative dataSet
      (residualNonnegative dataSet (suc scale))
      (fourResidualNonnegative dataSet scale)
      (powEighthNonnegative dataSet (suc scale))
      (powEighthNonnegative dataSet (suc scale))
      (residualGrowthAtMostFour dataSet scale)
      (reflexive dataSet (powEighth (suc scale))))

record HalfContractiveSummabilityAuthority : Set₁ where
  field
    Summable : (Nat → ℚ) → Set
    halfContractiveNonnegativeSummable :
      (term : Nat → ℚ) →
      (∀ scale → 0ℚ ≤ term scale) →
      (∀ scale → term (suc scale) ≤ half * term scale) →
      Summable term

open HalfContractiveSummabilityAuthority public

weightedResidualSummable :
  (authority : HalfContractiveSummabilityAuthority) →
  (dataSet : BlockAveragingResidualEnvelope) →
  Summable authority (weightedResidual dataSet)
weightedResidualSummable authority dataSet =
  halfContractiveNonnegativeSummable authority
    (weightedResidual dataSet)
    (weightedResidualNonnegative dataSet)
    (weightedResidualStepBelowHalf dataSet)

blockAdjointDyadicArithmeticLevel : ProofLevel
blockAdjointDyadicArithmeticLevel = machineChecked

polynomialGrowthTimesAdjointContractionLevel : ProofLevel
polynomialGrowthTimesAdjointContractionLevel = machineChecked

weightedResidualSummabilityReductionLevel : ProofLevel
weightedResidualSummabilityReductionLevel = machineChecked

physicalBlockAveragingAdjointNormInputsLevel : ProofLevel
physicalBlockAveragingAdjointNormInputsLevel = conditional

physicalResidualGrowthAtMostFourInputsLevel : ProofLevel
physicalResidualGrowthAtMostFourInputsLevel = conditional

constructiveHalfGeometricSummabilityInputsLevel : ProofLevel
constructiveHalfGeometricSummabilityInputsLevel = conditional

-- The locator is explicitly inadmissible. Its authority field therefore remains
-- an open/conjectural claim rather than a nonexistent proof-level constructor.
rgNormalizedDisintegrationLocatorAcceptedAsAuthority : ProofLevel
rgNormalizedDisintegrationLocatorAcceptedAsAuthority = conjectural
