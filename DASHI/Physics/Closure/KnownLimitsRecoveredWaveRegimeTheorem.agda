module DASHI.Physics.Closure.KnownLimitsRecoveredWaveRegimeTheorem where

open import Agda.Primitive using (Setω)

open import DASHI.Physics.Closure.KnownLimitsRecoveredWaveGeometryTheorem as KLRWG
open import DASHI.Physics.Closure.KnownLimitsRecoveredLocalRegimeTheorem as KLRLR

record KnownLimitsRecoveredWaveRegimeTheorem : Setω where
  field
    recoveredWaveGeometry : KLRWG.KnownLimitsRecoveredWaveGeometryTheorem
    recoveredLocalRegime : KLRLR.KnownLimitsRecoveredLocalRegimeTheorem

canonicalKnownLimitsRecoveredWaveRegimeTheorem :
  KnownLimitsRecoveredWaveRegimeTheorem
canonicalKnownLimitsRecoveredWaveRegimeTheorem =
  record
    { recoveredWaveGeometry =
        KLRWG.canonicalKnownLimitsRecoveredWaveGeometryTheorem
    ; recoveredLocalRegime =
        KLRLR.canonicalKnownLimitsRecoveredLocalRegimeTheorem
    }
