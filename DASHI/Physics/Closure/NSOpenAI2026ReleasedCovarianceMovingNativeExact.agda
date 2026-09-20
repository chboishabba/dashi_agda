module DASHI.Physics.Closure.NSOpenAI2026ReleasedCovarianceMovingNativeExact where

------------------------------------------------------------------------
-- RELEASED C/D / NATIVE PORT OF CorrectionAnalyticStep.WaveData.covariance_moving
--
-- Public released Lean proof:
--
--   first covariance:
--     covarianceIncrement_moving u particular
--
--   second covariance:
--     covarianceIncrement_moving (u + particular) signed
--
-- with smoothness and periodicity of u+particular obtained by closure under
-- addition.  This theorem is shared by C and D: domain-specific forcing /
-- periodicity enters later, not in this local covariance-preservation body.
--
-- The module ports exactly that dependency shape.  It does not postulate the
-- resulting particular/signed covariance leaves independently.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)

record CovarianceMovingSurface : Set₁ where
  field
    Field : Set
    Region : Set
    Smooth : Region → Field → Set
    Periodic : Field → Set
    RadialSupport : Region → Field → Set
    Moving : Region → Field → Field → Set

    _addField_ : Field → Field → Field
    covarianceIncrement : Field → Field → Field

open CovarianceMovingSurface public

record CovarianceMovingRules
    (S : CovarianceMovingSurface) : Set₁ where
  field
    smoothAdd :
      (region : Region S) →
      (u v : Field S) →
      Smooth S region u →
      Smooth S region v →
      Smooth S region (_addField_ S u v)

    periodicAdd :
      (u v : Field S) →
      Periodic S u →
      Periodic S v →
      Periodic S (_addField_ S u v)

    covarianceIncrementMoving :
      (region : Region S) →
      (u wave : Field S) →
      Smooth S region u →
      Smooth S region wave →
      RadialSupport S region wave →
      Periodic S u →
      Periodic S wave →
      Moving S region u
        (covarianceIncrement S u wave)

open CovarianceMovingRules public

record TwoWaveCovarianceInputs
    (S : CovarianceMovingSurface)
    (R : CovarianceMovingRules S) : Set₁ where
  field
    region : Region S
    incoming particular signed : Field S

    incomingSmooth : Smooth S region incoming
    particularSmooth : Smooth S region particular
    signedSmooth : Smooth S region signed

    incomingPeriodic : Periodic S incoming
    particularPeriodic : Periodic S particular
    signedPeriodic : Periodic S signed

    particularSupport : RadialSupport S region particular
    signedSupport : RadialSupport S region signed

open TwoWaveCovarianceInputs public

record TwoWaveCovarianceMoving
    {S : CovarianceMovingSurface}
    {R : CovarianceMovingRules S}
    (I : TwoWaveCovarianceInputs S R) : Set₁ where
  field
    particularCovarianceMoving :
      Moving S (region I) (incoming I)
        (covarianceIncrement S (incoming I) (particular I))

    signedCovarianceMoving :
      Moving S (region I)
        (_addField_ S (incoming I) (particular I))
        (covarianceIncrement S
          (_addField_ S (incoming I) (particular I))
          (signed I))

open TwoWaveCovarianceMoving public

releasedCovarianceMoving :
  ∀ {S R} →
  (I : TwoWaveCovarianceInputs S R) →
  TwoWaveCovarianceMoving I
releasedCovarianceMoving {S} {R} I =
  record
    { particularCovarianceMoving =
        covarianceIncrementMoving R
          (region I)
          (incoming I)
          (particular I)
          (incomingSmooth I)
          (particularSmooth I)
          (particularSupport I)
          (incomingPeriodic I)
          (particularPeriodic I)

    ; signedCovarianceMoving =
        covarianceIncrementMoving R
          (region I)
          (_addField_ S (incoming I) (particular I))
          (signed I)
          (smoothAdd R
            (region I)
            (incoming I)
            (particular I)
            (incomingSmooth I)
            (particularSmooth I))
          (signedSmooth I)
          (signedSupport I)
          (periodicAdd R
            (incoming I)
            (particular I)
            (incomingPeriodic I)
            (particularPeriodic I))
          (signedPeriodic I)
    }

releasedCovarianceMovingBodyPorted : Bool
releasedCovarianceMovingBodyPorted = true

particularCovarianceIndependentLeafAfterThisPort : Bool
particularCovarianceIndependentLeafAfterThisPort = false

signedCovarianceIndependentLeafAfterThisPort : Bool
signedCovarianceIndependentLeafAfterThisPort = false

actualReleasedWaveSmoothSupportInputsPopulatedHere : Bool
actualReleasedWaveSmoothSupportInputsPopulatedHere = false

clayPromotion : Bool
clayPromotion = false

releasedCovarianceMovingBodyPortedIsTrue :
  releasedCovarianceMovingBodyPorted ≡ true
releasedCovarianceMovingBodyPortedIsTrue = refl
