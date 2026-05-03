module DASHI.Physics.Closure.KnownLimitsFullMatterGaugeTheorem where

open import Agda.Primitive using (Setω)

open import DASHI.Physics.Closure.CanonicalGaugeMatterInterpretableObservableTheorem as CGMIOT
open import DASHI.Physics.Closure.CanonicalGaugeMatterRecoveredMatterFieldTheorem as CGMRMFT
open import DASHI.Physics.Closure.CanonicalGaugeMatterStrengtheningTheorem as CGMST
open import DASHI.Physics.Closure.KnownLimitsMatterGaugeTheorem as KLMGT
open import DASHI.Physics.Closure.KnownLimitsRecoveryWitness as KLRW

record KnownLimitsFullMatterGaugeTheorem : Setω where
  field
    matterGauge : KLMGT.KnownLimitsMatterGaugeTheorem
    canonicalGaugeMatterStrengthening :
      CGMST.CanonicalGaugeMatterStrengtheningTheorem
    canonicalGaugeMatterInterpretableObservable :
      CGMIOT.CanonicalGaugeMatterInterpretableObservableTheorem
    canonicalGaugeMatterRecoveredMatterField :
      CGMRMFT.CanonicalGaugeMatterRecoveredMatterFieldTheorem
    recoveryWitness : KLRW.KnownLimitsRecoveryWitnessPlus

canonicalKnownLimitsFullMatterGaugeTheorem :
  KnownLimitsFullMatterGaugeTheorem
canonicalKnownLimitsFullMatterGaugeTheorem =
  record
    { matterGauge = KLMGT.canonicalKnownLimitsMatterGaugeTheorem
    ; canonicalGaugeMatterStrengthening =
        CGMST.canonicalGaugeMatterStrengtheningTheorem
    ; canonicalGaugeMatterInterpretableObservable =
        CGMIOT.canonicalGaugeMatterInterpretableObservableTheorem
    ; canonicalGaugeMatterRecoveredMatterField =
        CGMRMFT.canonicalGaugeMatterRecoveredMatterFieldTheorem
    ; recoveryWitness = KLRW.canonicalKnownLimitsRecoveryWitness
    }
