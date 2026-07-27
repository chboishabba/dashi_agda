module DASHI.Physics.YangMills.BalabanClayT2ConfiguredStrictLossMarginExact where

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Unit using (tt)
open import Data.Integer.Base using (+_)
open import Data.Rational using (ℚ; 0ℚ; 1ℚ; _+_; _-_; _*_; _≤_; _≤ᵇ_; _/_)
import Data.Rational.Properties as ℚP
import Data.Rational.Tactic.RingSolver as ℚRing
open import Relation.Binary.PropositionalEquality using (cong; subst; sym)

open import DASHI.Physics.YangMills.CompactLieProofLevel

------------------------------------------------------------------------
-- Literature normalization.
--
-- Tadeusz Bałaban,
-- "Renormalization Group Approach to Lattice Gauge Field Theories. I.
-- Generation of Effective Actions in a Small Field Approximation and a
-- Coupling Constant Renormalization in Four Dimensions",
-- Communications in Mathematical Physics 109 (1987), 249--301.
-- DOI: 10.1007/BF01215223
--
-- Comparison role: Eqs. (0.29)--(0.31) track a main logarithmic contribution
-- and an explicit higher-order error uniformly across scales.  The rational
-- margin below is DASHI-owned and records that the configured 1/16 ledger has
-- a certified perturbation tolerance rather than only a decimal approximation.
------------------------------------------------------------------------

fourteenFifths sixteenℚ threeℚ oneFifth : ℚ
fourteenFifths = + 14 / 5
sixteenℚ = + 16 / 1
threeℚ = + 3 / 1
oneFifth = + 1 / 5

-- Sum_{n=0}^6 (14/5)^n/n! = 11280391/703125 > 16.
expFourteenFifthsSixthPartialSum : ℚ
expFourteenFifthsSixthPartialSum =
  1ℚ
  + fourteenFifths
  + (fourteenFifths * fourteenFifths) * (+ 1 / 2)
  + (fourteenFifths * fourteenFifths * fourteenFifths) * (+ 1 / 6)
  + (fourteenFifths * fourteenFifths * fourteenFifths * fourteenFifths)
      * (+ 1 / 24)
  + (fourteenFifths * fourteenFifths * fourteenFifths * fourteenFifths
      * fourteenFifths) * (+ 1 / 120)
  + (fourteenFifths * fourteenFifths * fourteenFifths * fourteenFifths
      * fourteenFifths * fourteenFifths) * (+ 1 / 720)

expFourteenFifthsSixthPartialSumExact :
  expFourteenFifthsSixthPartialSum ≡ + 11280391 / 703125
expFourteenFifthsSixthPartialSumExact = ℚRing.solve

sixteenBelowExpFourteenFifthsPartialSum :
  sixteenℚ ≤ expFourteenFifthsSixthPartialSum
sixteenBelowExpFourteenFifthsPartialSum = ℚP.≤ᵇ⇒≤ tt

configuredSharpSlackExact : threeℚ - fourteenFifths ≡ oneFifth
configuredSharpSlackExact = ℚRing.solve

record SharpLogSixteenAnalyticAuthority (Scalar : Set) : Set₁ where
  field
    rational : ℚ → Scalar
    exponential logarithm : Scalar → Scalar
    LessEqual : Scalar → Scalar → Set

    transitive : ∀ {left middle right} →
      LessEqual left middle → LessEqual middle right → LessEqual left right

    rationalOrderEmbedding : ∀ {left right} →
      left ≤ right → LessEqual (rational left) (rational right)

    exponentialFourteenFifthsAboveSixthPartialSum :
      LessEqual (rational expFourteenFifthsSixthPartialSum)
        (exponential (rational fourteenFifths))

    logarithmMonotone : ∀ {left right} →
      LessEqual left right → LessEqual (logarithm left) (logarithm right)

    logarithmExponentialFourteenFifths :
      logarithm (exponential (rational fourteenFifths))
      ≡ rational fourteenFifths

open SharpLogSixteenAnalyticAuthority public

logSixteenBelowFourteenFifths :
  ∀ {Scalar} (dataSet : SharpLogSixteenAnalyticAuthority Scalar) →
  LessEqual dataSet
    (logarithm dataSet (rational dataSet sixteenℚ))
    (rational dataSet fourteenFifths)
logSixteenBelowFourteenFifths dataSet =
  subst
    (λ upper → LessEqual dataSet
      (logarithm dataSet (rational dataSet sixteenℚ)) upper)
    (logarithmExponentialFourteenFifths dataSet)
    (logarithmMonotone dataSet
      (transitive dataSet
        (rationalOrderEmbedding dataSet
          sixteenBelowExpFourteenFifthsPartialSum)
        (exponentialFourteenFifthsAboveSixthPartialSum dataSet)))

record ConfiguredStrictLossRobustness (Scalar : Set) : Set₁ where
  field
    analytic : SharpLogSixteenAnalyticAuthority Scalar
    subtract : Scalar → Scalar → Scalar

    netGain extraLoss perturbedNetGain : Scalar

    netGainExact : netGain ≡ rational analytic threeℚ
    extraLossBelowSlack :
      LessEqual analytic extraLoss (rational analytic oneFifth)

    perturbedNetGainDefinition :
      perturbedNetGain ≡ subtract netGain extraLoss

    rationalSubtractionExact :
      subtract (rational analytic threeℚ) (rational analytic oneFifth)
      ≡ rational analytic fourteenFifths

    subtractMonotoneAntitone : ∀ {left leftUpper right rightUpper} →
      LessEqual analytic left leftUpper →
      LessEqual analytic right rightUpper →
      LessEqual analytic
        (subtract left rightUpper) (subtract leftUpper right)

open ConfiguredStrictLossRobustness public

configuredPerturbedNetGainAboveFourteenFifths :
  ∀ {Scalar} (dataSet : ConfiguredStrictLossRobustness Scalar) →
  LessEqual (analytic dataSet)
    (rational (analytic dataSet) fourteenFifths)
    (perturbedNetGain dataSet)
configuredPerturbedNetGainAboveFourteenFifths dataSet =
  subst
    (λ lower → LessEqual (analytic dataSet) lower
      (perturbedNetGain dataSet))
    (sym (rationalSubtractionExact dataSet))
    (subst
      (λ upper → LessEqual (analytic dataSet)
        (subtract dataSet
          (rational (analytic dataSet) threeℚ)
          (rational (analytic dataSet) oneFifth)) upper)
      (sym (perturbedNetGainDefinition dataSet))
      (subtractMonotoneAntitone dataSet
        (subst
          (λ value → LessEqual (analytic dataSet)
            (rational (analytic dataSet) threeℚ) value)
          (sym (netGainExact dataSet))
          (rationalOrderEmbedding (analytic dataSet)
            (ℚP.≤-refl threeℚ)))
        (extraLossBelowSlack dataSet)))

configuredPerturbedNetGainAtLeastLogSixteen :
  ∀ {Scalar} (dataSet : ConfiguredStrictLossRobustness Scalar) →
  LessEqual (analytic dataSet)
    (logarithm (analytic dataSet)
      (rational (analytic dataSet) sixteenℚ))
    (perturbedNetGain dataSet)
configuredPerturbedNetGainAtLeastLogSixteen dataSet =
  transitive (analytic dataSet)
    (logSixteenBelowFourteenFifths (analytic dataSet))
    (configuredPerturbedNetGainAboveFourteenFifths dataSet)

sharpPartialSumArithmeticLevel : ProofLevel
sharpPartialSumArithmeticLevel = machineChecked

configuredOneFifthRobustnessReductionLevel : ProofLevel
configuredOneFifthRobustnessReductionLevel = machineChecked

positiveExponentialTailAndLogInputsLevel : ProofLevel
positiveExponentialTailAndLogInputsLevel = conditional
