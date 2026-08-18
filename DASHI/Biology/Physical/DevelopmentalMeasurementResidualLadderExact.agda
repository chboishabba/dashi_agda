module DASHI.Biology.Physical.DevelopmentalMeasurementResidualLadderExact where

------------------------------------------------------------------------
-- DEVELOPMENTAL MEASUREMENT AS A RECOVERABLE REFINEMENT LADDER
--
-- This reuses DevelopmentalMeasurementQuotientExact rather than inventing a
-- new biological carrier.  The exact five-Boolean cell state admits the ladder
--
--   nominal measurement
--     = (genome, transcript, phenotype)
--   < measurement + chromatin
--   < full cell state.
--
-- The first refinement repairs the existing chromatin collision but remains
-- insufficient against a source-native bioelectric collision.  Exact
-- recoverability identifies the residual of the nominal measurement as the
-- product (bioelectric × chromatin), up to the declared stage ordering.
------------------------------------------------------------------------

open import DASHI.Core.Prelude

import DASHI.Biology.Physical.DevelopmentalMeasurementQuotientExact as Dev
import DASHI.Core.AdmissibleReachability as Reachability
import DASHI.Core.FutureLanguageProjectionDefectExact as FutureDefect
import DASHI.Core.FutureObservationLanguageQuotientExact as Future
import DASHI.Core.ObserverRefinementFutureSafetyExact as FutureBridge
import DASHI.Core.ObserverRefinementLatticeExact as Observer
import DASHI.Core.RecoverableObserverRefinementExact as Refinement
import DASHI.Core.RecoverableQuotientCompositionExact as Recoverable
import DASHI.Core.TypedDependencyCore as Dependency

record NominalMeasurement : Set where
  constructor nominalMeasurement
  field
    measuredGenome : Bool
    measuredTranscript : Bool
    measuredPhenotype : Bool
open NominalMeasurement public

record ChromatinMeasurement : Set where
  constructor chromatinMeasurement
  field
    fineGenome : Bool
    fineTranscript : Bool
    finePhenotype : Bool
    fineChromatin : Bool
open ChromatinMeasurement public

nominalObserver : Dev.CellState → NominalMeasurement
nominalObserver x =
  nominalMeasurement
    (Dev.genome x)
    (Dev.transcript x)
    (Dev.phenotype x)

chromatinObserver : Dev.CellState → ChromatinMeasurement
chromatinObserver x =
  chromatinMeasurement
    (Dev.genome x)
    (Dev.transcript x)
    (Dev.phenotype x)
    (Dev.chromatin x)

forgetChromatin : ChromatinMeasurement → NominalMeasurement
forgetChromatin x =
  nominalMeasurement
    (fineGenome x)
    (fineTranscript x)
    (finePhenotype x)

fineResidual : Dev.CellState → Bool
fineResidual = Dev.bioelectric

reopenFine : ChromatinMeasurement → Bool → Dev.CellState
reopenFine x b =
  Dev.cellState
    (fineGenome x)
    (fineTranscript x)
    (fineChromatin x)
    b
    (finePhenotype x)

reopenFineExact :
  (x : Dev.CellState) →
  reopenFine (chromatinObserver x) (fineResidual x) ≡ x
reopenFineExact (Dev.cellState g t c b p) = refl

fineRecoverable :
  Recoverable.ExactRecoverableProjection Dev.CellState ChromatinMeasurement
fineRecoverable =
  Recoverable.exactRecoverableProjection
    Bool chromatinObserver fineResidual reopenFine reopenFineExact

coarseResidual : ChromatinMeasurement → Bool
coarseResidual = fineChromatin

reopenCoarse : NominalMeasurement → Bool → ChromatinMeasurement
reopenCoarse x c =
  chromatinMeasurement
    (measuredGenome x)
    (measuredTranscript x)
    (measuredPhenotype x)
    c

reopenCoarseExact :
  (x : ChromatinMeasurement) →
  reopenCoarse (forgetChromatin x) (coarseResidual x) ≡ x
reopenCoarseExact (chromatinMeasurement g t p c) = refl

coarseRecoverable :
  Recoverable.ExactRecoverableProjection ChromatinMeasurement NominalMeasurement
coarseRecoverable =
  Recoverable.exactRecoverableProjection
    Bool forgetChromatin coarseResidual reopenCoarse reopenCoarseExact

measurementRefinementStep :
  Refinement.RecoverableRefinementStep
    Dev.CellState ChromatinMeasurement NominalMeasurement
measurementRefinementStep =
  Refinement.recoverableRefinementStep fineRecoverable coarseRecoverable

chromatinRefinesNominalMeasurement :
  Observer.Refines nominalObserver chromatinObserver
chromatinRefinesNominalMeasurement =
  Refinement.fineRefinesCompositeCoarse measurementRefinementStep

nominalResidualDecomposesAsBioelectricTimesChromatin :
  Recoverable.Residual
    (Refinement.compositeRecoverableProjection measurementRefinementStep)
  ≡ (Bool × Bool)
nominalResidualDecomposesAsBioelectricTimesChromatin = refl

------------------------------------------------------------------------
-- The existing source-native chromatin collision is separated by the first
-- refinement.
------------------------------------------------------------------------

nominalCollisionOnExistingWitness :
  nominalObserver Dev.left ≡ nominalObserver Dev.right
nominalCollisionOnExistingWitness = refl

chromatinSeparatesExistingWitness :
  chromatinObserver Dev.left ≡ chromatinObserver Dev.right → ⊥
chromatinSeparatesExistingWitness ()

nominalToChromatinStrictRefinement :
  Observer.StrictRefinement nominalObserver chromatinObserver
nominalToChromatinStrictRefinement =
  Observer.strictRefinement
    chromatinRefinesNominalMeasurement
    Dev.left
    Dev.right
    nominalCollisionOnExistingWitness
    chromatinSeparatesExistingWitness

------------------------------------------------------------------------
-- But chromatin is not the end of the ladder: equal measured+chromatin state
-- can still hide a bioelectric difference that changes the next phenotype.
------------------------------------------------------------------------

bioelectricLeft bioelectricRight : Dev.CellState
bioelectricLeft = Dev.cellState false false false false false
bioelectricRight = Dev.cellState false false false true false

sameChromatinMeasurement :
  chromatinObserver bioelectricLeft ≡ chromatinObserver bioelectricRight
sameChromatinMeasurement = refl

futurePhenotypeBioelectricDiffers :
  Dev.phenotypeObservation (Dev.cellUpdate bioelectricLeft)
    ≡ Dev.phenotypeObservation (Dev.cellUpdate bioelectricRight) → ⊥
futurePhenotypeBioelectricDiffers ()

rightBioelectricFuture :
  Future.FutureObservation
    Dev.system
    Dev.phenotypeObservation
    bioelectricRight
    (Dev.develop ∷ [])
    true
rightBioelectricFuture =
  Future.futureObservation
    (Dev.cellUpdate bioelectricRight)
    (Reachability.executesCons
      (Dev.admissible bioelectricRight)
      Reachability.executesNil)
    refl

leftBioelectricFutureImpossible :
  Future.FutureObservation
    Dev.system
    Dev.phenotypeObservation
    bioelectricLeft
    (Dev.develop ∷ [])
    true →
  ⊥
leftBioelectricFutureImpossible
  (Future.futureObservation after
    (Reachability.executesCons step Reachability.executesNil)
    observed)
  with Dependency.postcondition step
... | refl = false≢true observed
  where
    false≢true : false ≡ true → ⊥
    false≢true ()

chromatinFutureLanguageDefect :
  FutureDefect.FutureLanguageProjectionDefect
    Dev.system
    Dev.phenotypeObservation
    chromatinObserver
chromatinFutureLanguageDefect =
  FutureDefect.futureLanguageProjectionDefect
    bioelectricLeft
    bioelectricRight
    sameChromatinMeasurement
    (Dev.develop ∷ [])
    true
    rightBioelectricFuture
    leftBioelectricFutureImpossible

chromatinObserverStillNotFutureSafe :
  Future.FutureLanguageSafeProjection
    Dev.system
    Dev.phenotypeObservation
    chromatinObserver →
  ⊥
chromatinObserverStillNotFutureSafe safety =
  FutureDefect.futureLanguageDefectContradictsSafety
    safety
    chromatinFutureLanguageDefect

------------------------------------------------------------------------
-- The identity observer closes the finite ladder and is future-safe for every
-- declared future language on this exact carrier.
------------------------------------------------------------------------

fullStateObserver : Observer.Observer Dev.CellState Dev.CellState
fullStateObserver x = x

fullStateSeparating : Observer.Separating fullStateObserver
fullStateSeparating x y same = same

fullStateIsFutureSafeForPhenotypeLanguage :
  Future.FutureLanguageSafeProjection
    Dev.system
    Dev.phenotypeObservation
    fullStateObserver
fullStateIsFutureSafeForPhenotypeLanguage =
  FutureBridge.separatingObserverIsFutureLanguageSafe fullStateSeparating

record DevelopmentalMeasurementResidualLadderBoundary : Set where
  constructor developmentalMeasurementResidualLadderBoundary
  field
    chromatinStrictlyRefinesNominalMeasurement : Bool
    chromatinStrictlyRefinesNominalMeasurementIsTrue :
      chromatinStrictlyRefinesNominalMeasurement ≡ true
    nominalResidualFactorsIntoBioelectricAndChromatin : Bool
    nominalResidualFactorsIntoBioelectricAndChromatinIsTrue :
      nominalResidualFactorsIntoBioelectricAndChromatin ≡ true
    chromatinMeasurementStillFutureUnsafe : Bool
    chromatinMeasurementStillFutureUnsafeIsTrue :
      chromatinMeasurementStillFutureUnsafe ≡ true
    fullStateSeparatesAndIsFutureSafe : Bool
    fullStateSeparatesAndIsFutureSafeIsTrue :
      fullStateSeparatesAndIsFutureSafe ≡ true

canonicalDevelopmentalMeasurementResidualLadderBoundary :
  DevelopmentalMeasurementResidualLadderBoundary
canonicalDevelopmentalMeasurementResidualLadderBoundary =
  developmentalMeasurementResidualLadderBoundary
    true refl true refl true refl true refl
