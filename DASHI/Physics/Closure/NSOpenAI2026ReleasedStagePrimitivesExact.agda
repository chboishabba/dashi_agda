module DASHI.Physics.Closure.NSOpenAI2026ReleasedStagePrimitivesExact where

------------------------------------------------------------------------
-- NATIVE PORT: CycleStateCoherence.stage_primitives
--
-- Source:
--   openai/NavierStokesAndEuler
--   NavierStokes/CycleStateCoherence.lean
--   theorem stage_primitives
--
-- The released theorem is a composition theorem:
--
--   incoming primitive
--     --particular wave/covariance--> particular primitive
--     --signed wave/covariance-----> signed primitive
--     --temporal regularity--------> temporal primitive
--     --rank geometry--------------> ranked primitive
--
-- This module ports that theorem body natively.  It deliberately does not
-- identify DASHI's existing Fourier/Gram covariance with the released
-- GaugeMomentBalances.MovingField hypothesis; such a same-object theorem is a
-- separate obligation.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)

------------------------------------------------------------------------
-- 1. Source-faithful abstract carriers.
------------------------------------------------------------------------

record ReleasedPrimitiveSurface : Set₁ where
  field
    State : Set
    PrimitiveData : State → Set

    ParticularWave : Set
    SignedWave : Set

    ParticularCovariance : State → ParticularWave → Set
    SignedCovariance : State → SignedWave → Set

    RankGeometry : State → Set

open ReleasedPrimitiveSurface public

------------------------------------------------------------------------
-- 2. The four literal state transformations used by the released theorem.
------------------------------------------------------------------------

record ReleasedPrimitiveStageOperations
    (S : ReleasedPrimitiveSurface) : Set₁ where
  field
    afterParticular :
      State S → ParticularWave S → State S

    afterSigned :
      State S → SignedWave S → State S

    afterTemporal :
      State S → State S

    afterRank :
      State S → State S

open ReleasedPrimitiveStageOperations public

------------------------------------------------------------------------
-- 3. Analytic rules corresponding exactly to:
--
--   PrimitiveData.waveStage
--   MeanStageRegularity.temporalStage_primitive
--   MeanStageRegularity.rankGeometry_for_state
--   MeanStageRegularity.rankStage_primitive
------------------------------------------------------------------------

record ReleasedPrimitiveAnalyticRules
    (S : ReleasedPrimitiveSurface)
    (O : ReleasedPrimitiveStageOperations S) : Set₁ where
  field
    particularWaveStage :
      (u : State S) →
      (w : ParticularWave S) →
      PrimitiveData S u →
      ParticularCovariance S u w →
      PrimitiveData S (afterParticular O u w)

    signedWaveStage :
      (u : State S) →
      (w : SignedWave S) →
      PrimitiveData S u →
      SignedCovariance S u w →
      PrimitiveData S (afterSigned O u w)

    temporalStagePrimitive :
      (u : State S) →
      PrimitiveData S u →
      PrimitiveData S (afterTemporal O u)

    rankGeometryForState :
      (u v : State S) →
      PrimitiveData S u →
      RankGeometry S v →
      RankGeometry S u

    rankStagePrimitive :
      (u : State S) →
      PrimitiveData S u →
      RankGeometry S u →
      PrimitiveData S (afterRank O u)

open ReleasedPrimitiveAnalyticRules public

------------------------------------------------------------------------
-- 4. Inputs to one source-exact stage_primitives invocation.
------------------------------------------------------------------------

record ReleasedStagePrimitiveInputs
    (S : ReleasedPrimitiveSurface)
    (O : ReleasedPrimitiveStageOperations S)
    (R : ReleasedPrimitiveAnalyticRules S O)
    : Set₁ where
  field
    incomingState : State S
    particularWave : ParticularWave S
    signedWave : SignedWave S

    incomingPrimitive :
      PrimitiveData S incomingState

    particularCovariance :
      ParticularCovariance S incomingState particularWave

    signedCovariance :
      SignedCovariance S
        (afterParticular O incomingState particularWave)
        signedWave

    incomingRankGeometry :
      RankGeometry S incomingState

open ReleasedStagePrimitiveInputs public

------------------------------------------------------------------------
-- 5. Literal intermediate states.
------------------------------------------------------------------------

particularState :
  ∀ {S O R} →
  ReleasedStagePrimitiveInputs S O R →
  State S
particularState {O = O} I =
  afterParticular O
    (incomingState I)
    (particularWave I)

signedState :
  ∀ {S O R} →
  ReleasedStagePrimitiveInputs S O R →
  State S
signedState {O = O} I =
  afterSigned O
    (particularState I)
    (signedWave I)

temporalState :
  ∀ {S O R} →
  ReleasedStagePrimitiveInputs S O R →
  State S
temporalState {O = O} I =
  afterTemporal O (signedState I)

rankedState :
  ∀ {S O R} →
  ReleasedStagePrimitiveInputs S O R →
  State S
rankedState {O = O} I =
  afterRank O (temporalState I)

------------------------------------------------------------------------
-- 6. Native StagePrimitives result.
------------------------------------------------------------------------

-- The source result depends on the analytic rules as well, so expose the useful
-- fully-indexed result separately rather than hiding those dependencies.
record ReleasedStagePrimitivesFor
    {S : ReleasedPrimitiveSurface}
    {O : ReleasedPrimitiveStageOperations S}
    {R : ReleasedPrimitiveAnalyticRules S O}
    (I : ReleasedStagePrimitiveInputs S O R) : Set₁ where
  field
    particular :
      PrimitiveData S (particularState I)

    signed :
      PrimitiveData S (signedState I)

    temporal :
      PrimitiveData S (temporalState I)

    ranked :
      PrimitiveData S (rankedState I)

    rankGeometry :
      RankGeometry S (temporalState I)

open ReleasedStagePrimitivesFor public

------------------------------------------------------------------------
-- 7. The actual source theorem body.
------------------------------------------------------------------------

stagePrimitives :
  ∀ {S O R} →
  (I : ReleasedStagePrimitiveInputs S O R) →
  ReleasedStagePrimitivesFor I
stagePrimitives {O = O} {R = R} I =
  let
    H0 = incomingPrimitive I

    H1 =
      particularWaveStage R
        (incomingState I)
        (particularWave I)
        H0
        (particularCovariance I)

    H2 =
      signedWaveStage R
        (particularState I)
        (signedWave I)
        H1
        (signedCovariance I)

    H3 =
      temporalStagePrimitive R
        (signedState I)
        H2

    HG =
      rankGeometryForState R
        (temporalState I)
        (incomingState I)
        H3
        (incomingRankGeometry I)

    H4 =
      rankStagePrimitive R
        (temporalState I)
        H3
        HG
  in
  record
    { particular = H1
    ; signed = H2
    ; temporal = H3
    ; ranked = H4
    ; rankGeometry = HG
    }

------------------------------------------------------------------------
-- 8. Dependency cut exposed by the native theorem.
------------------------------------------------------------------------

record ReleasedStagePrimitiveLeafProducers
    (S : ReleasedPrimitiveSurface)
    (O : ReleasedPrimitiveStageOperations S)
    (R : ReleasedPrimitiveAnalyticRules S O)
    (u : State S)
    (particular : ParticularWave S)
    (signed : SignedWave S)
    : Set₁ where
  field
    incomingPrimitive :
      PrimitiveData S u

    particularCovariance :
      ParticularCovariance S u particular

    signedCovariance :
      SignedCovariance S (afterParticular O u particular) signed

    rankGeometry :
      RankGeometry S u

open ReleasedStagePrimitiveLeafProducers public

compileStagePrimitiveInputs :
  ∀ {S O R u particular signed} →
  ReleasedStagePrimitiveLeafProducers
    S O R u particular signed →
  ReleasedStagePrimitiveInputs S O R
compileStagePrimitiveInputs {u = u} {particular = particular} {signed = signed} L =
  record
    { incomingState = u
    ; particularWave = particular
    ; signedWave = signed
    ; incomingPrimitive = incomingPrimitive L
    ; particularCovariance = particularCovariance L
    ; signedCovariance = signedCovariance L
    ; incomingRankGeometry = rankGeometry L
    }

compileStagePrimitives :
  ∀ {S O R u particular signed} →
  (L : ReleasedStagePrimitiveLeafProducers
    S O R u particular signed) →
  ReleasedStagePrimitivesFor
    (compileStagePrimitiveInputs L)
compileStagePrimitives L =
  stagePrimitives (compileStagePrimitiveInputs L)

------------------------------------------------------------------------
-- 9. Trust ledger.
------------------------------------------------------------------------

releasedStagePrimitivesBodyPorted : Bool
releasedStagePrimitivesBodyPorted = true

particularCovarianceProducerPopulatedHere : Bool
particularCovarianceProducerPopulatedHere = false

signedCovarianceProducerPopulatedHere : Bool
signedCovarianceProducerPopulatedHere = false

rankGeometryProducerPopulatedHere : Bool
rankGeometryProducerPopulatedHere = false

existingFourierGramCovarianceIdentifiedWithReleasedMovingField : Bool
existingFourierGramCovarianceIdentifiedWithReleasedMovingField = false

releasedStagePrimitivesBodyPortedIsTrue :
  releasedStagePrimitivesBodyPorted ≡ true
releasedStagePrimitivesBodyPortedIsTrue = refl

existingFourierGramCovarianceIdentifiedWithReleasedMovingFieldIsFalse :
  existingFourierGramCovarianceIdentifiedWithReleasedMovingField ≡ false
existingFourierGramCovarianceIdentifiedWithReleasedMovingFieldIsFalse = refl
