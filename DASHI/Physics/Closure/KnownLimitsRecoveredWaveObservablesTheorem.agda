module DASHI.Physics.Closure.KnownLimitsRecoveredWaveObservablesTheorem where

open import Agda.Primitive using (Setω)

open import DASHI.Physics.Closure.KnownLimitsRecoveredWaveRegimeTheorem as KLRWR
open import DASHI.Physics.Closure.KnownLimitsRecoveredObservablesTheorem as KLROT

record KnownLimitsRecoveredWaveObservablesTheorem : Setω where
  field
    recoveredWaveRegime : KLRWR.KnownLimitsRecoveredWaveRegimeTheorem
    recoveredObservables : KLROT.KnownLimitsRecoveredObservablesTheorem

canonicalKnownLimitsRecoveredWaveObservablesTheorem :
  KnownLimitsRecoveredWaveObservablesTheorem
canonicalKnownLimitsRecoveredWaveObservablesTheorem =
  record
    { recoveredWaveRegime =
        KLRWR.canonicalKnownLimitsRecoveredWaveRegimeTheorem
    ; recoveredObservables =
        KLROT.canonicalKnownLimitsRecoveredObservablesTheorem
    }
