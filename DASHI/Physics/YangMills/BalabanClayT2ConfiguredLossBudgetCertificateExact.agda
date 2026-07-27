module DASHI.Physics.YangMills.BalabanClayT2ConfiguredLossBudgetCertificateExact where

open import Agda.Builtin.Equality using (_≡_)
open import Data.Integer.Base using (+_)
open import Data.Rational using (ℚ; 0ℚ; 1ℚ; _+_; _-_; _*_; _/_)
import Data.Rational.Tactic.RingSolver as ℚRing
open import Relation.Binary.PropositionalEquality using (cong; subst; sym; trans)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanClayCommonLogSixteenCertificateExact as Log16

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
-- Marc Daumas, David Lester and César Muñoz, "Verified Real Number
-- Calculations: A Library for Interval Arithmetic", IEEE Transactions on
-- Computers 58 (2009), 226--237. DOI: 10.1109/TC.2008.213
--
-- Relationship: the first three sources provide the analytic mechanisms; the
-- last provides verified elementary-function evaluation architecture.  The
-- rational allocation and exact slack calculation are DASHI-owned.
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
-- Physical domination data.  The order and rational embedding are owned by the
-- common logarithm certificate, so log 16 <= 3 is derived rather than supplied
-- again as an independent field.
------------------------------------------------------------------------

record ConfiguredPhysicalLossDomination
    (Scale Polymer Scalar : Set) : Set₁ where
  field
    logAuthority : Log16.LogSixteenAnalyticAuthority Scalar

    actionGain jacobianLoss determinantLoss bchLoss localizationLoss patchLoss :
      Scale → Polymer → Scalar

    add subtract : Scalar → Scalar → Scalar

    addMonotone : ∀ {a b c d} →
      Log16.LessEqual logAuthority a b →
      Log16.LessEqual logAuthority c d →
      Log16.LessEqual logAuthority (add a c) (add b d)

    actionGainDominatesConfigured : ∀ scale polymer →
      Log16.LessEqual logAuthority
        (Log16.rational logAuthority configuredActionGain)
        (actionGain scale polymer)

    jacobianLossBelowConfigured : ∀ scale polymer →
      Log16.LessEqual logAuthority (jacobianLoss scale polymer)
        (Log16.rational logAuthority configuredJacobianLoss)
    determinantLossBelowConfigured : ∀ scale polymer →
      Log16.LessEqual logAuthority (determinantLoss scale polymer)
        (Log16.rational logAuthority configuredDeterminantLoss)
    bchLossBelowConfigured : ∀ scale polymer →
      Log16.LessEqual logAuthority (bchLoss scale polymer)
        (Log16.rational logAuthority configuredBCHLoss)
    localizationLossBelowConfigured : ∀ scale polymer →
      Log16.LessEqual logAuthority (localizationLoss scale polymer)
        (Log16.rational logAuthority configuredLocalizationLoss)
    patchLossBelowConfigured : ∀ scale polymer →
      Log16.LessEqual logAuthority (patchLoss scale polymer)
        (Log16.rational logAuthority configuredPatchLoss)

    rationalPreservesConfiguredArithmetic : Set

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
      Log16.LessEqual logAuthority (totalLoss scale polymer)
        (Log16.rational logAuthority configuredTotalLoss)

    configuredGainMinusLossBound : ∀ scale polymer →
      Log16.LessEqual logAuthority
        (Log16.rational logAuthority configuredNetGain)
        (netGain scale polymer)

open ConfiguredPhysicalLossDomination public

configuredLogSixteen :
  ∀ {Scale Polymer Scalar} →
  ConfiguredPhysicalLossDomination Scale Polymer Scalar → Scalar
configuredLogSixteen dataSet =
  Log16.logarithm (logAuthority dataSet)
    (Log16.rational (logAuthority dataSet) Log16.sixteenℚ)

physicalNetGainAtLeastLogSixteenConfigured :
  ∀ {Scale Polymer Scalar}
    (dataSet : ConfiguredPhysicalLossDomination Scale Polymer Scalar)
    scale polymer →
  Log16.LessEqual (logAuthority dataSet)
    (configuredLogSixteen dataSet)
    (netGain dataSet scale polymer)
physicalNetGainAtLeastLogSixteenConfigured dataSet scale polymer =
  Log16.transitive (logAuthority dataSet)
    (Log16.logSixteenBelowThree (logAuthority dataSet))
    (subst
      (λ value →
        Log16.LessEqual (logAuthority dataSet) value
          (netGain dataSet scale polymer))
      (cong
        (Log16.rational (logAuthority dataSet))
        configuredNetGainExact)
      (configuredGainMinusLossBound dataSet scale polymer))

------------------------------------------------------------------------
-- Endpoint adapter: the exponential/product comparison remains explicit, but
-- the common numerical budget and log 16 <= 3 receipt are no longer free.
------------------------------------------------------------------------

record ConfiguredOneSixteenthEndpoint
    (Scale Polymer Scalar : Set) : Set₁ where
  field
    budget : ConfiguredPhysicalLossDomination Scale Polymer Scalar
    activity factorProduct oneSixteenth : Scale → Polymer → Scalar

    activityBelowFactorProduct : ∀ scale polymer →
      Log16.LessEqual (logAuthority budget)
        (activity scale polymer) (factorProduct scale polymer)

    netGainImpliesFactorProductBelow : ∀ scale polymer →
      Log16.LessEqual (logAuthority budget)
        (configuredLogSixteen budget) (netGain budget scale polymer) →
      Log16.LessEqual (logAuthority budget)
        (factorProduct scale polymer) (oneSixteenth scale polymer)

open ConfiguredOneSixteenthEndpoint public

literalWilsonActivityPerTraversalBelowOneSixteenthConfigured :
  ∀ {Scale Polymer Scalar}
    (dataSet : ConfiguredOneSixteenthEndpoint Scale Polymer Scalar)
    scale polymer →
  Log16.LessEqual (logAuthority (budget dataSet))
    (activity dataSet scale polymer)
    (oneSixteenth dataSet scale polymer)
literalWilsonActivityPerTraversalBelowOneSixteenthConfigured dataSet scale polymer =
  Log16.transitive (logAuthority (budget dataSet))
    (activityBelowFactorProduct dataSet scale polymer)
    (netGainImpliesFactorProductBelow dataSet scale polymer
      (physicalNetGainAtLeastLogSixteenConfigured
        (budget dataSet) scale polymer))

configuredLossArithmeticLevel : ProofLevel
configuredLossArithmeticLevel = machineChecked

configuredLogSixteenReductionLevel : ProofLevel
configuredLogSixteenReductionLevel = machineChecked

configuredOneSixteenthAssemblyLevel : ProofLevel
configuredOneSixteenthAssemblyLevel = machineChecked

physicalLossDominationInputsLevel : ProofLevel
physicalLossDominationInputsLevel = conditional
