module DASHI.Physics.Closure.KnownLimitsFullMatterGaugeTheorem where

open import Agda.Primitive using (Setω)

open import DASHI.Physics.Closure.KnownLimitsMatterGaugeTheorem as KLMGT
open import DASHI.Physics.Closure.KnownLimitsRecoveryWitness as KLRW

record KnownLimitsFullMatterGaugeTheorem : Setω where
  field
    matterGauge : KLMGT.KnownLimitsMatterGaugeTheorem
    recoveryWitness : KLRW.KnownLimitsRecoveryWitnessPlus

canonicalKnownLimitsFullMatterGaugeTheorem :
  KnownLimitsFullMatterGaugeTheorem
canonicalKnownLimitsFullMatterGaugeTheorem =
  record
    { matterGauge = KLMGT.canonicalKnownLimitsMatterGaugeTheorem
    ; recoveryWitness = KLRW.canonicalKnownLimitsRecoveryWitness
    }
