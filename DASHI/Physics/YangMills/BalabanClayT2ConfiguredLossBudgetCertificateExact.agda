module DASHI.Physics.YangMills.BalabanClayT2ConfiguredLossBudgetCertificateExact where

open import Agda.Builtin.Equality using (_≡_)
open import Data.Integer.Base using (+_)
open import Data.Rational using (ℚ; 0ℚ; 1ℚ; _+_; _-_; _*_; _≤_; _/_)
import Data.Rational.Tactic.RingSolver as ℚRing
open import Relation.Binary.PropositionalEquality using (cong; subst; sym; trans)

open import DASHI.Physics.YangMills.CompactLieProofLevel

------------------------------------------------------------------------
-- Literature normalization.
--
-- Tadeusz Bałaban, "Ultraviolet Stability of Three-Dimensional Lattice Pure
-- Gauge Field Theories", Communications in Mathematical Physics 102 (1985),
-- 255--275. DOI: 10.1007/BF01229380
--
-- Tadeusz Bałaban, "Renormalization Group Approach to Lattice Gauge Field
-- Theories. II. Cluster Expansions", Communications in Mathematical Physics
-- 116 (1988), 1--22. DOI: 10.1007/BF01239022
--
-- Barry Simon, "Trace Ideals and Their Applications", second edition,
-- American Mathematical Society (2005). DOI: 10.1090/surv/120
--
-- Relationship: the papers provide the analytic mechanisms.  The rational
-- allocation and exact slack calculation below are DASHI-owned bookkeeping.
------------------------------------------------------------------------

twoℚ threeℚ fourℚ eightℚ sixteenℚ : ℚ
twoℚ = 1ℚ + 1ℚ
threeℚ = twoℚ + 1ℚ
fourℚ = twoℚ + twoℚ
eightℚ = fourℚ + fourℚ
sixteenℚ = eightℚ + eightℚ

configuredJacobianLoss configuredDeterminantLoss configuredBCHLoss : ℚ
configuredJacobianLoss = + 1 / 16
configuredDeterminantLoss = + 1 / 4
configuredBCHLoss = + 1 / 8

configuredLocalizationLoss configuredPatchLoss : ℚ
configuredLocalizationLoss = + 1 / 8
configuredPatchLoss = + 1 / 8

configuredTotalLoss : ℚ
configuredTotalLoss =
  configuredJacobianLoss
  + (configuredDeterminantLoss
  + (configuredBCHLoss
  + (configuredLocalizationLoss
  + configuredPatchLoss)))

-- Choosing action gain 59/16 makes the net gain exactly 3, leaving the
-- elementary analytic obligation log 16 <= 3 as a separate one-line receipt.
configuredActionGain : ℚ
configuredActionGain = + 59 / 16

configuredNetGain configuredLogSixteenUpper configuredNetSlack : ℚ
configuredNetGain = configuredActionGain - configuredTotalLoss
configuredLogSixteenUpper = threeℚ
configuredNetSlack = configuredNetGain - configuredLogSixteenUpper

configuredTotalLossExact : configuredTotalLoss ≡ + 11 / 16
configuredTotalLossExact = ℚRing.solve

configuredNetGainExact : configuredNetGain ≡ threeℚ
configuredNetGainExact = ℚRing.solve

configuredNetSlackExact : configuredNetSlack ≡ 0ℚ
configuredNetSlackExact = ℚRing.solve

------------------------------------------------------------------------
-- Physical domination data.  Each actual loss must be bounded by its assigned
-- rational slot and the actual action gain must dominate 59/16.  No factor is
-- individually required to be below 1/16.
------------------------------------------------------------------------

record ConfiguredPhysicalLossDomination
    (Scale Polymer Scalar : Set) : Set₁ where
  field
    actionGain jacobianLoss determinantLoss bchLoss localizationLoss patchLoss :
      Scale → Polymer → Scalar

    rational : ℚ → Scalar
    add subtract : Scalar → Scalar → Scalar
    LessEqual : Scalar → Scalar → Set
    transitive : ∀ {left middle right} →
      LessEqual left middle → LessEqual middle right → LessEqual left right
    addMonotone : ∀ {a b c d} →
      LessEqual a b → LessEqual c d → LessEqual (add a c) (add b d)

    actionGainDominatesConfigured : ∀ scale polymer →
      LessEqual (rational configuredActionGain) (actionGain scale polymer)

    jacobianLossBelowConfigured : ∀ scale polymer →
      LessEqual (jacobianLoss scale polymer)
        (rational configuredJacobianLoss)
    determinantLossBelowConfigured : ∀ scale polymer →
      LessEqual (determinantLoss scale polymer)
        (rational configuredDeterminantLoss)
    bchLossBelowConfigured : ∀ scale polymer →
      LessEqual (bchLoss scale polymer) (rational configuredBCHLoss)
    localizationLossBelowConfigured : ∀ scale polymer →
      LessEqual (localizationLoss scale polymer)
        (rational configuredLocalizationLoss)
    patchLossBelowConfigured : ∀ scale polymer →
      LessEqual (patchLoss scale polymer) (rational configuredPatchLoss)

    rationalPreservesConfiguredArithmetic : Set

    -- Elementary transcendental receipt, preferably discharged by the same
    -- rational interval engine as the sinc/log chart certificate.
    logSixteen : Scalar
    logSixteenBelowThree : LessEqual logSixteen (rational threeℚ)

    totalLoss netGain : Scale → Polymer → Scalar
    totalLossDefinition : ∀ scale polymer →
      totalLoss scale polymer
      ≡ add (jacobianLoss scale polymer)
          (add (determinantLoss scale polymer)
            (add (bchLoss scale polymer)
              (add (localizationLoss scale polymer)
                (patchLoss scale polymer))))
    netGainDefinition : ∀ scale polymer →
      netGain scale polymer
      ≡ subtract (actionGain scale polymer) (totalLoss scale polymer)

    configuredLossSumBound : ∀ scale polymer →
      LessEqual (totalLoss scale polymer) (rational configuredTotalLoss)

    configuredGainMinusLossBound : ∀ scale polymer →
      LessEqual (rational configuredNetGain) (netGain scale polymer)

open ConfiguredPhysicalLossDomination public

physicalNetGainAtLeastLogSixteenConfigured :
  ∀ {Scale Polymer Scalar}
    (dataSet : ConfiguredPhysicalLossDomination Scale Polymer Scalar)
    scale polymer →
  LessEqual dataSet (logSixteen dataSet) (netGain dataSet scale polymer)
physicalNetGainAtLeastLogSixteenConfigured dataSet scale polymer =
  transitive dataSet
    (logSixteenBelowThree dataSet)
    (subst
      (λ value → LessEqual dataSet value (netGain dataSet scale polymer))
      (sym (cong (rational dataSet) configuredNetGainExact))
      (configuredGainMinusLossBound dataSet scale polymer))

------------------------------------------------------------------------
-- Endpoint adapter: the exponential/product comparison remains explicit, but
-- the common numerical budget is no longer a free physical input.
------------------------------------------------------------------------

record ConfiguredOneSixteenthEndpoint
    (Scale Polymer Scalar : Set) : Set₁ where
  field
    budget : ConfiguredPhysicalLossDomination Scale Polymer Scalar
    activity factorProduct oneSixteenth : Scale → Polymer → Scalar

    activityBelowFactorProduct : ∀ scale polymer →
      LessEqual budget (activity scale polymer) (factorProduct scale polymer)

    netGainImpliesFactorProductBelow : ∀ scale polymer →
      LessEqual budget (logSixteen budget) (netGain budget scale polymer) →
      LessEqual budget (factorProduct scale polymer) (oneSixteenth scale polymer)

open ConfiguredOneSixteenthEndpoint public

literalWilsonActivityPerTraversalBelowOneSixteenthConfigured :
  ∀ {Scale Polymer Scalar}
    (dataSet : ConfiguredOneSixteenthEndpoint Scale Polymer Scalar)
    scale polymer →
  LessEqual (budget dataSet)
    (activity dataSet scale polymer)
    (oneSixteenth dataSet scale polymer)
literalWilsonActivityPerTraversalBelowOneSixteenthConfigured dataSet scale polymer =
  transitive (budget dataSet)
    (activityBelowFactorProduct dataSet scale polymer)
    (netGainImpliesFactorProductBelow dataSet scale polymer
      (physicalNetGainAtLeastLogSixteenConfigured
        (budget dataSet) scale polymer))

configuredLossArithmeticLevel : ProofLevel
configuredLossArithmeticLevel = machineChecked

configuredOneSixteenthAssemblyLevel : ProofLevel
configuredOneSixteenthAssemblyLevel = machineChecked

physicalLossDominationInputsLevel : ProofLevel
physicalLossDominationInputsLevel = conditional

logSixteenIntervalReceiptLevel : ProofLevel
logSixteenIntervalReceiptLevel = conditional
