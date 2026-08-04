module DASHI.Physics.YangMills.BalabanClayGate4WilsonAnimalEntropyLedgerExact where

open import Agda.Builtin.Equality using (_≡_)
open import Data.Rational using (ℚ; _+_; _*_; _≤_)

open import DASHI.Physics.YangMills.CompactLieProofLevel

import DASHI.Physics.YangMills.BalabanClayGate4WilsonPlaquetteBadCubeBudgetExact as WilsonBudget
import DASHI.Physics.YangMills.BalabanClayGate4LiteralWilsonLargeFieldPredicateExact as Wilson
import DASHI.Physics.YangMills.BalabanSU2RationalWilsonLargeFieldGapExact as Gap

------------------------------------------------------------------------
-- Separate Wilson payment for animal entropy, decay weight and reserved slack.
--
-- Tadeusz Bałaban,
-- "Large Field Renormalization I: The Basic Step of the R-Operation",
-- Communications in Mathematical Physics 122 (1989), 175--202.
-- DOI: 10.1007/BF01257412.
--
-- Tadeusz Bałaban,
-- "Large Field Renormalization II: Localization, Exponentiation, and Bounds
-- for the R-Operation", Communications in Mathematical Physics 122 (1989),
-- 355--392. DOI: 10.1007/BF01238433.
--
-- Roman Kotecký and David Preiss,
-- "Cluster Expansion for Abstract Polymer Models",
-- Communications in Mathematical Physics 103 (1986), 491--498.
-- DOI: 10.1007/BF01211762.
------------------------------------------------------------------------

record WilsonAnimalEntropyInputs
    {Scale Configuration Gauge Block Plaquette : Set}
    (largeField : Wilson.LiteralWilsonLargeFieldData
      Scale Configuration Gauge Block Plaquette)
    (cost : Wilson.LiteralWilsonCostData largeField) : Set₁ where
  field
    scale : Scale
    animalEntropy decayWeight reservedSlack entropyWithDecay : ℚ

    entropyWithDecayMeaning :
      entropyWithDecay ≡ animalEntropy + decayWeight

    entropyDecaySlackBelowPenalty :
      entropyWithDecay + reservedSlack
      ≤ (Gap.halfℚ * Wilson.beta cost scale)
          * Gap.squareℚ (Wilson.threshold largeField scale)

open WilsonAnimalEntropyInputs public

asWilsonPlaquetteBadCubeBudget :
  ∀ {Scale Configuration Gauge Block Plaquette}
    {largeField : Wilson.LiteralWilsonLargeFieldData
      Scale Configuration Gauge Block Plaquette}
    {cost : Wilson.LiteralWilsonCostData largeField} →
  WilsonAnimalEntropyInputs largeField cost →
  WilsonBudget.WilsonPlaquetteBadCubeBudget largeField cost
asWilsonPlaquetteBadCubeBudget inputs = record
  { scale = scale inputs
  ; entropyPerBadCube =
      entropyWithDecay inputs
  ; reservedSlackPerBadCube =
      reservedSlack inputs
  ; entropyAndSlackBelowWilsonPenalty =
      entropyDecaySlackBelowPenalty inputs
  }

wilsonAnimalEntropySeparationLevel : ProofLevel
wilsonAnimalEntropySeparationLevel = machineChecked

wilsonAnimalEntropyBudgetAdapterLevel : ProofLevel
wilsonAnimalEntropyBudgetAdapterLevel = machineChecked

physicalAnimalEntropyInputsLevel : ProofLevel
physicalAnimalEntropyInputsLevel = conditional

physicalWilsonDecayWeightInputsLevel : ProofLevel
physicalWilsonDecayWeightInputsLevel = conditional
