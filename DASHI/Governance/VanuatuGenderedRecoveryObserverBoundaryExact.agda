module DASHI.Governance.VanuatuGenderedRecoveryObserverBoundaryExact where

open import DASHI.Core.Prelude
import DASHI.Core.MeasurementBoundaryNonfactorabilityExact as Measurement
import DASHI.Core.ObserverRefinementLatticeExact as Observer
import DASHI.Core.ConsumerDescentMinimalObserverExact as Consumer
import DASHI.Governance.FeministClimateJusticeSourceRegistryExact as Sources

------------------------------------------------------------------------
-- ALSTON / FULLER / KWARNEY: EVENT STATUS != SITUATED RECOVERY FUNCTIONING
--
-- Margaret Alston, Sascha Fuller & Nikita Kwarney,
-- "Women and climate change in Vanuatu, Pacific Islands Region",
-- Gender, Place & Culture 32(1):83-104.
-- DOI: 10.1080/0966369X.2023.2229530.
-- Online publication 2023; issue publication 2025.
--
-- The source documents women's climate experiences, food-production / food-
-- security impacts and gendered social expectations.  The finite witness below
-- is deliberately generic: equal event-level status need not recover situated
-- recovery functioning.  It does not attribute unverified numerical effects or
-- a universal woman/man comparison to the paper.
------------------------------------------------------------------------

data SituatedRecoveryState : Set where
  lowerBurdenContext higherBurdenContext : SituatedRecoveryState

data EventStatus : Set where sameClimateEventStatus : EventStatus

data RecoveryFunctioning : Set where lessConstrainedRecovery moreConstrainedRecovery : RecoveryFunctioning

eventStatus : SituatedRecoveryState → EventStatus
eventStatus _ = sameClimateEventStatus

recoveryFunctioning : SituatedRecoveryState → RecoveryFunctioning
recoveryFunctioning lowerBurdenContext = lessConstrainedRecovery
recoveryFunctioning higherBurdenContext = moreConstrainedRecovery

recoveryBoundary :
  Measurement.MeasurementBoundary SituatedRecoveryState EventStatus RecoveryFunctioning
recoveryBoundary = Measurement.measurementBoundary eventStatus recoveryFunctioning

sameEventDifferentRecovery : Measurement.BoundaryLossWitness recoveryBoundary
sameEventDifferentRecovery =
  Measurement.boundaryLossWitness lowerBurdenContext higherBurdenContext refl (λ ())

recoveryDoesNotDescendThroughEventStatus :
  Consumer.FactorsThrough eventStatus recoveryFunctioning → ⊥
recoveryDoesNotDescendThroughEventStatus =
  Measurement.boundaryLossBlocksFactorization sameEventDifferentRecovery

joinedEventAndRecoveryStrictlyRefinesEvent :
  Observer.StrictRefinement
    eventStatus
    (Observer.pairObserver eventStatus recoveryFunctioning)
joinedEventAndRecoveryStrictlyRefinesEvent =
  Observer.strictPairRefinement
    eventStatus recoveryFunctioning
    lowerBurdenContext higherBurdenContext refl (λ ())

source : Sources.SourceReference
source = Sources.alstonFullerKwarney2023

record VanuatuGenderedRecoveryBoundary : Set where
  constructor vanuatuGenderedRecoveryBoundary
  field
    eventLevelStatusDeterminesSituatedRecovery : Bool
    eventLevelStatusDeterminesSituatedRecoveryIsFalse :
      eventLevelStatusDeterminesSituatedRecovery ≡ false
    eventObserverExhaustsGenderedSocialContext : Bool
    eventObserverExhaustsGenderedSocialContextIsFalse :
      eventObserverExhaustsGenderedSocialContext ≡ false
    finiteWitnessIsUniversalGenderLaw : Bool
    finiteWitnessIsUniversalGenderLawIsFalse : finiteWitnessIsUniversalGenderLaw ≡ false

canonicalVanuatuGenderedRecoveryBoundary : VanuatuGenderedRecoveryBoundary
canonicalVanuatuGenderedRecoveryBoundary =
  vanuatuGenderedRecoveryBoundary false refl false refl false refl
