module DASHI.Wikimedia.KeyShoeCLARAOperatorBoundaryExact where

-- Source: @bigshoesjqz CLARA J13 Point Flow / Observer Shoe diagrams,
-- 10 September and 12 July screenshots supplied on 2026-11-16.
-- The symbol labels, diagram shape and order are source transcriptions.
-- Physical calibration, linguistic interpretation and modular j-identity
-- remain UNPROVED. J, Q and Z are distinct types/roles in this adapter.

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.Bool using (Bool; true; false)
open import Data.Empty using (⊥)

import DASHI.Wikimedia.KeyShoeCLARAR13DihedralExact as R13

data Port : Set where
  previousJ qPort zBoundary nextJ returnJ : Port

data Gate : Set where
  mContinue fReturn : Gate

data PortTransition : Port → Port → Set where
  entryInterval : PortTransition previousJ qPort
  exitInterval : PortTransition qPort zBoundary
  mBranch : PortTransition zBoundary nextJ
  fBranch : PortTransition zBoundary returnJ
  relativeReturn : PortTransition returnJ previousJ

-- The source has two outgoing Z arrows. Determinism requires a chosen gate.
chosenExit : Gate → Port
chosenExit mContinue = nextJ
chosenExit fReturn = returnJ

chosenExitProof : (gate : Gate) → PortTransition zBoundary (chosenExit gate)
chosenExitProof mContinue = mBranch
chosenExitProof fReturn = fBranch

chosenM : chosenExit mContinue ≡ nextJ
chosenM = refl

chosenF : chosenExit fReturn ≡ returnJ
chosenF = refl

data MeasurementBody : Set where
  preparedSource waveField apparatusBoundary
    detectorBody storedRecord interpretingObserver : MeasurementBody

data MeasurementTransition : MeasurementBody → MeasurementBody → Set where
  sourcePreparesWave :
    MeasurementTransition preparedSource waveField
  waveMeetsBoundary :
    MeasurementTransition waveField apparatusBoundary
  apparatusCouplesDetector :
    MeasurementTransition apparatusBoundary detectorBody
  detectorProducesRecord :
    MeasurementTransition detectorBody storedRecord
  recordPrecedesObserver :
    MeasurementTransition storedRecord interpretingObserver

-- The six-body chain does not include an observer -> source arrow.
noDirectObserverToSource :
  MeasurementTransition interpretingObserver preparedSource → ⊥
noDirectObserverToSource ()

-- CLARA D0..D13: 14 *named stages*, distinct from 13 radial bodies
-- and from DASHI's semantic 0..12 stage carrier.
data ObserverDStage : Set where
  d0 d1 d2 d3 d4 d5 d6 d7 d8 d9 d10 d11 d12 d13 : ObserverDStage

observerDStageCount : Nat
observerDStageCount = 14

observerD0IsNotD13 : d0 ≡ d13 → ⊥
observerD0IsNotD13 ()

-- The hand-drawn 5..0 ladder is not an arithmetic physics law.
-- Only the source-order labels are transcribed here; ambiguous
-- assignments (shape, handwritten value, Roman form) remain in docs.
data HandwrittenDepth : Set where
  h5 h4 h3 h2 h1 h0 : HandwrittenDepth

data HandwrittenShape : Set where
  circle square triangle segment cross undecidedZero : HandwrittenShape

sourceShape : HandwrittenDepth → HandwrittenShape
sourceShape h5 = circle
sourceShape h4 = square
sourceShape h3 = triangle
sourceShape h2 = segment
sourceShape h1 = cross
sourceShape h0 = undecidedZero

-- Source-derived structure is not an actual measurement or Monster action.
record CLARASourceBoundary : Set where
  constructor clara-source-boundary
  field
    jQZEntryExitGraphCaptured : Bool
    branchNeedsGateSelection : Bool
    sixBodiesKeptDistinct : Bool
    fourteenDStagesNotThirteenBodies : Bool
    sourceAssignedDetectorUnitsAndCalibration : Bool
    creatorDeclaredExactModularJIdentification : Bool
    sourceDefinedMonsterVOAActionPaid : Bool

canonicalCLARASourceBoundary : CLARASourceBoundary
canonicalCLARASourceBoundary =
  clara-source-boundary true true true true false false false
