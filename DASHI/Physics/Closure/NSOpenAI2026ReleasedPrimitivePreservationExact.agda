module DASHI.Physics.Closure.NSOpenAI2026ReleasedPrimitivePreservationExact where

------------------------------------------------------------------------
-- NATIVE PORT:
--   MeanStateRegularity.PrimitiveData.waveStage
--   MeanStageRegularity.temporalStage_primitive
--   MeanStageRegularity.rankStage_primitive
--
-- These released theorem bodies are preservation algebra.  Operators, base
-- data and virtual stresses are reused; only the mean and/or covariance change.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)

record PrimitivePreservationSurface : Set₁ where
  field
    State : Set
    Component : Set
    Wave : Set

    OperatorEvidence : State → Set
    BaseEvidence : State → Set
    MeanEvidence : State → Set
    CovarianceEvidence : State → Component → Component → Set
    VirtualThetaEvidence : State → Set
    VirtualAxialEvidence : State → Set

    CovarianceIncrementEvidence :
      State → Wave → Component → Component → Set

open PrimitivePreservationSurface public

record PrimitiveData
    (S : PrimitivePreservationSurface)
    (u : State S) : Set₁ where
  field
    operators : OperatorEvidence S u
    base : BaseEvidence S u
    mean : MeanEvidence S u
    covariance :
      (i j : Component S) →
      CovarianceEvidence S u i j
    virtualTheta : VirtualThetaEvidence S u
    virtualAxial : VirtualAxialEvidence S u

open PrimitiveData public

record PrimitiveStageOperations
    (S : PrimitivePreservationSurface) : Set₁ where
  field
    waveStage : State S → Wave S → State S
    temporalStage : State S → State S
    rankStage : State S → State S

open PrimitiveStageOperations public

------------------------------------------------------------------------
-- Evidence transport rules exactly matching the source rewrites.
------------------------------------------------------------------------

record PrimitivePreservationRules
    (S : PrimitivePreservationSurface)
    (O : PrimitiveStageOperations S) : Set₁ where
  field
    waveOperators :
      (u : State S) (w : Wave S) →
      OperatorEvidence S u →
      OperatorEvidence S (waveStage O u w)

    waveBase :
      (u : State S) (w : Wave S) →
      BaseEvidence S u →
      BaseEvidence S (waveStage O u w)

    waveMean :
      (u : State S) (w : Wave S) →
      MeanEvidence S u →
      MeanEvidence S (waveStage O u w)

    waveCovariance :
      (u : State S) (w : Wave S) →
      (i j : Component S) →
      CovarianceEvidence S u i j →
      CovarianceIncrementEvidence S u w i j →
      CovarianceEvidence S (waveStage O u w) i j

    waveVirtualTheta :
      (u : State S) (w : Wave S) →
      VirtualThetaEvidence S u →
      VirtualThetaEvidence S (waveStage O u w)

    waveVirtualAxial :
      (u : State S) (w : Wave S) →
      VirtualAxialEvidence S u →
      VirtualAxialEvidence S (waveStage O u w)

    temporalOperators :
      (u : State S) →
      OperatorEvidence S u →
      OperatorEvidence S (temporalStage O u)

    temporalBase :
      (u : State S) →
      BaseEvidence S u →
      BaseEvidence S (temporalStage O u)

    temporalMean :
      (u : State S) →
      MeanEvidence S u →
      MeanEvidence S (temporalStage O u)

    temporalCovariance :
      (u : State S) →
      (i j : Component S) →
      CovarianceEvidence S u i j →
      CovarianceEvidence S (temporalStage O u) i j

    temporalVirtualTheta :
      (u : State S) →
      VirtualThetaEvidence S u →
      VirtualThetaEvidence S (temporalStage O u)

    temporalVirtualAxial :
      (u : State S) →
      VirtualAxialEvidence S u →
      VirtualAxialEvidence S (temporalStage O u)

    rankOperators :
      (u : State S) →
      OperatorEvidence S u →
      OperatorEvidence S (rankStage O u)

    rankBase :
      (u : State S) →
      BaseEvidence S u →
      BaseEvidence S (rankStage O u)

    rankMean :
      (u : State S) →
      MeanEvidence S u →
      MeanEvidence S (rankStage O u)

    rankCovariance :
      (u : State S) →
      (i j : Component S) →
      CovarianceEvidence S u i j →
      CovarianceEvidence S (rankStage O u) i j

    rankVirtualTheta :
      (u : State S) →
      VirtualThetaEvidence S u →
      VirtualThetaEvidence S (rankStage O u)

    rankVirtualAxial :
      (u : State S) →
      VirtualAxialEvidence S u →
      VirtualAxialEvidence S (rankStage O u)

open PrimitivePreservationRules public

------------------------------------------------------------------------
-- 1. Native PrimitiveData.waveStage.
------------------------------------------------------------------------

waveStagePrimitive :
  ∀ {S O} →
  (R : PrimitivePreservationRules S O) →
  {u : State S} →
  (w : Wave S) →
  PrimitiveData S u →
  ((i j : Component S) →
    CovarianceIncrementEvidence S u w i j) →
  PrimitiveData S (waveStage O u w)
waveStagePrimitive R {u} w H hX =
  record
    { operators = waveOperators R u w (operators H)
    ; base = waveBase R u w (base H)
    ; mean = waveMean R u w (mean H)
    ; covariance = λ i j →
        waveCovariance R u w i j
          (covariance H i j)
          (hX i j)
    ; virtualTheta =
        waveVirtualTheta R u w (virtualTheta H)
    ; virtualAxial =
        waveVirtualAxial R u w (virtualAxial H)
    }

------------------------------------------------------------------------
-- 2. Native temporalStage_primitive.
------------------------------------------------------------------------

temporalStagePrimitive :
  ∀ {S O} →
  (R : PrimitivePreservationRules S O) →
  {u : State S} →
  PrimitiveData S u →
  PrimitiveData S (temporalStage O u)
temporalStagePrimitive R {u} H =
  record
    { operators = temporalOperators R u (operators H)
    ; base = temporalBase R u (base H)
    ; mean = temporalMean R u (mean H)
    ; covariance = λ i j →
        temporalCovariance R u i j (covariance H i j)
    ; virtualTheta =
        temporalVirtualTheta R u (virtualTheta H)
    ; virtualAxial =
        temporalVirtualAxial R u (virtualAxial H)
    }

------------------------------------------------------------------------
-- 3. Native rankStage_primitive.
------------------------------------------------------------------------

rankStagePrimitive :
  ∀ {S O} →
  (R : PrimitivePreservationRules S O) →
  {u : State S} →
  PrimitiveData S u →
  PrimitiveData S (rankStage O u)
rankStagePrimitive R {u} H =
  record
    { operators = rankOperators R u (operators H)
    ; base = rankBase R u (base H)
    ; mean = rankMean R u (mean H)
    ; covariance = λ i j →
        rankCovariance R u i j (covariance H i j)
    ; virtualTheta =
        rankVirtualTheta R u (virtualTheta H)
    ; virtualAxial =
        rankVirtualAxial R u (virtualAxial H)
    }

------------------------------------------------------------------------
-- 4. Two wave stages compose with no extra primitive-data hypothesis.
------------------------------------------------------------------------

twoWaveStagesPrimitive :
  ∀ {S O} →
  (R : PrimitivePreservationRules S O) →
  {u : State S} →
  (particular signed : Wave S) →
  PrimitiveData S u →
  ((i j : Component S) →
    CovarianceIncrementEvidence S u particular i j) →
  ((i j : Component S) →
    CovarianceIncrementEvidence S
      (waveStage O u particular) signed i j) →
  PrimitiveData S
    (waveStage O (waveStage O u particular) signed)
twoWaveStagesPrimitive R particular signed H hParticular hSigned =
  waveStagePrimitive R signed
    (waveStagePrimitive R particular H hParticular)
    hSigned

releasedWaveStagePrimitiveBodyPorted : Bool
releasedWaveStagePrimitiveBodyPorted = true

releasedTemporalStagePrimitiveBodyPorted : Bool
releasedTemporalStagePrimitiveBodyPorted = true

releasedRankStagePrimitiveBodyPorted : Bool
releasedRankStagePrimitiveBodyPorted = true

twoWavePrimitiveCompositionClosed : Bool
twoWavePrimitiveCompositionClosed = true

actualCovarianceIncrementRegularityPopulatedHere : Bool
actualCovarianceIncrementRegularityPopulatedHere = false

releasedWaveStagePrimitiveBodyPortedIsTrue :
  releasedWaveStagePrimitiveBodyPorted ≡ true
releasedWaveStagePrimitiveBodyPortedIsTrue = refl

releasedTemporalStagePrimitiveBodyPortedIsTrue :
  releasedTemporalStagePrimitiveBodyPorted ≡ true
releasedTemporalStagePrimitiveBodyPortedIsTrue = refl

releasedRankStagePrimitiveBodyPortedIsTrue :
  releasedRankStagePrimitiveBodyPorted ≡ true
releasedRankStagePrimitiveBodyPortedIsTrue = refl

actualCovarianceIncrementRegularityPopulatedHereIsFalse :
  actualCovarianceIncrementRegularityPopulatedHere ≡ false
actualCovarianceIncrementRegularityPopulatedHereIsFalse = refl
