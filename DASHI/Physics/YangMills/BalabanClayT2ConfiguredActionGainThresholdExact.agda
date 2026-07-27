module DASHI.Physics.YangMills.BalabanClayT2ConfiguredActionGainThresholdExact where

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Unit using (tt)
open import Data.Integer.Base using (+_)
open import Data.Rational using (ℚ; 0ℚ; _*_; _≤_; _≤ᵇ_; _/_)
import Data.Rational.Properties as ℚP
import Data.Rational.Tactic.RingSolver as ℚRing
open import Relation.Binary.PropositionalEquality using (subst; sym; trans)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanSU2RationalWilsonLargeFieldGapExact as Gap
import DASHI.Physics.YangMills.BalabanClayT2ConfiguredLossBudgetCertificateExact as Budget

------------------------------------------------------------------------
-- Literature normalization.
--
-- Tadeusz Bałaban, "Ultraviolet Stability of Three-Dimensional Lattice Pure
-- Gauge Field Theories", Communications in Mathematical Physics 102 (1985),
-- 255--275. DOI: 10.1007/BF01229380
-- Relationship: large-field Wilson suppression architecture.  The threshold
-- calculation below is DASHI-owned exact rational arithmetic.
------------------------------------------------------------------------

configuredBadChordalRadius configuredBadChordalRadiusSq : ℚ
configuredBadChordalRadius = + 1 / 4
configuredBadChordalRadiusSq = + 1 / 16

configuredBetaThreshold : ℚ
configuredBetaThreshold = + 118 / 1

configuredGainFactor : ℚ
configuredGainFactor = (+ 1 / 2) * configuredBadChordalRadiusSq

configuredBadRadiusSquareExact :
  configuredBadChordalRadius * configuredBadChordalRadius
  ≡ configuredBadChordalRadiusSq
configuredBadRadiusSquareExact = ℚRing.solve

configuredGainFactorExact : configuredGainFactor ≡ + 1 / 32
configuredGainFactorExact = ℚRing.solve

configuredLocalWilsonGapAtThreshold : ℚ
configuredLocalWilsonGapAtThreshold = configuredGainFactor * configuredBetaThreshold

configuredLocalGapFillsActionSlot :
  configuredLocalWilsonGapAtThreshold ≡ Budget.configuredActionGain
configuredLocalGapFillsActionSlot = ℚRing.solve

configuredGainFactorNonnegative : 0ℚ ≤ configuredGainFactor
configuredGainFactorNonnegative = ℚP.≤ᵇ⇒≤ tt

configuredCurrentGapNormalForm : ∀ beta →
  configuredGainFactor * beta
  ≡ (+ 1 / 2) * beta * configuredBadChordalRadiusSq
configuredCurrentGapNormalForm = ℚRing.solve-∀

record ConfiguredWilsonActionGainInput (Plaquette : Set) : Set₁ where
  field
    order : Gap.RationalWilsonGapOrder
    beta : ℚ
    betaAboveConfigured : configuredBetaThreshold ≤ beta

    largeFieldPlaquette : Plaquette → Set
    holonomy : Plaquette → Gap.RationalUnitQuaternion

    plaquetteChordalGap : ∀ plaquette → largeFieldPlaquette plaquette →
      configuredBadChordalRadiusSq
      ≤ Gap.literalChordalDistanceSq (holonomy plaquette)

    betaMonotone : ∀ {left right coefficient : ℚ} →
      0ℚ ≤ coefficient → left ≤ right →
      coefficient * left ≤ coefficient * right

    halfBetaNonnegative : 0ℚ ≤ (+ 1 / 2) * beta

open ConfiguredWilsonActionGainInput public

configuredGainBelowCurrentLocalGap :
  ∀ {Plaquette} (dataSet : ConfiguredWilsonActionGainInput Plaquette) →
  Budget.configuredActionGain
  ≤ (+ 1 / 2) * beta dataSet * configuredBadChordalRadiusSq
configuredGainBelowCurrentLocalGap dataSet =
  subst
    (λ upper → Budget.configuredActionGain ≤ upper)
    (configuredCurrentGapNormalForm (beta dataSet))
    (subst
      (λ lower → lower ≤ configuredGainFactor * beta dataSet)
      configuredLocalGapFillsActionSlot
      (betaMonotone dataSet
        configuredGainFactorNonnegative
        (betaAboveConfigured dataSet)))

configuredPlaquetteActionGain :
  ∀ {Plaquette}
    (dataSet : ConfiguredWilsonActionGainInput Plaquette)
    plaquette → largeFieldPlaquette dataSet plaquette →
  Budget.configuredActionGain
  ≤ Gap.wilsonPlaquetteAction (beta dataSet) (holonomy dataSet plaquette)
configuredPlaquetteActionGain dataSet plaquette large =
  Gap.transitive (order dataSet)
    (configuredGainBelowCurrentLocalGap dataSet)
    (Gap.localWilsonActionGap
      (order dataSet)
      (beta dataSet)
      configuredBadChordalRadius
      (holonomy dataSet plaquette)
      (halfBetaNonnegative dataSet)
      (subst
        (λ radiusSq → radiusSq
          ≤ Gap.literalChordalDistanceSq (holonomy dataSet plaquette))
        configuredBadRadiusSquareExact
        (plaquetteChordalGap dataSet plaquette large)))

configuredActionThresholdArithmeticLevel : ProofLevel
configuredActionThresholdArithmeticLevel = machineChecked

configuredActionGainReductionLevel : ProofLevel
configuredActionGainReductionLevel = machineChecked

physicalLargeFieldPlaquetteAndBetaInputsLevel : ProofLevel
physicalLargeFieldPlaquetteAndBetaInputsLevel = conditional
