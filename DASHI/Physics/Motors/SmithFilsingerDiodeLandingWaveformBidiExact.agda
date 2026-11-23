module DASHI.Physics.Motors.SmithFilsingerDiodeLandingWaveformBidiExact where

-- Source-first continuation of SmithFilsingerCapCoilParallelNodeQuotientBidiExact.
-- Earlier user-supplied Filsinger midpoint transcript states two diodes off
-- the capacitor, two off another wire/coil, four 'all forward facing', and
-- common positive output/return 'to midpoint, earth, ground'.
--
-- IF the capacitor is physically across the chosen coil, its component pins
-- have the same U,V electrical-node quotient as that coil. BUT NOTHING IN
-- THAT FACT asserts that M is halfway between U and V, or that U,V are the
-- full outer ends of a centre-tapped secondary. In particular:
--  - full-winding U-M=+v,V-M=-v, groups on opposite nodes: full-wave
--  - full-winding, all diode anodes at U: half-wave
--  - half-winding U-M=+v,V=M, groups on opposite nodes: half-wave.
-- Finite model assumes no output storage, sinusoidal active source, ideal
-- zero-drop forward diodes and resistive P-M return. This is NOT a readback
-- of the original filmed circuit or any source-work experiment.
--
-- Local SymPy companion (64/64 conditional checks):
-- /mnt/data/check_filsinger_diode_node_landing_half_full_sympy_20261122.py

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Data.Empty using (⊥)
open import Relation.Binary.PropositionalEquality using (sym; trans)

import DASHI.Physics.Motors.SmithFilsingerCapCoilParallelNodeQuotientBidiExact as CapCoil
import DASHI.Physics.Motors.SmithFilsingerTranscriptDiagramNumbersSourceIndexExact as Speech

data CoilSpan : Set where
  selectedFullSecondary selectedHalfSecondary : CoilSpan

data InputLanding : Set where
  fromOppositeElectricalEnds fromOneElectricalEnd : InputLanding

data HalfCycle : Set where
  positiveHalf negativeHalf : HalfCycle

data LoadConduction : Set where
  receivesPositiveCurrent disconnectedAtIdealDiodes : LoadConduction

-- Conditional forward semantics of P=max(0,U-M,V-M).
-- In the full-secondary case U-M=v,V-M=-v.
-- In the half-secondary case U-M=v,V=M.
forwardConduction :
  CoilSpan → InputLanding → HalfCycle → LoadConduction
forwardConduction selectedFullSecondary fromOppositeElectricalEnds
  positiveHalf = receivesPositiveCurrent
forwardConduction selectedFullSecondary fromOppositeElectricalEnds
  negativeHalf = receivesPositiveCurrent
forwardConduction selectedFullSecondary fromOneElectricalEnd
  positiveHalf = receivesPositiveCurrent
forwardConduction selectedFullSecondary fromOneElectricalEnd
  negativeHalf = disconnectedAtIdealDiodes
forwardConduction selectedHalfSecondary fromOppositeElectricalEnds
  positiveHalf = receivesPositiveCurrent
forwardConduction selectedHalfSecondary fromOppositeElectricalEnds
  negativeHalf = disconnectedAtIdealDiodes
forwardConduction selectedHalfSecondary fromOneElectricalEnd
  positiveHalf = receivesPositiveCurrent
forwardConduction selectedHalfSecondary fromOneElectricalEnd
  negativeHalf = disconnectedAtIdealDiodes

-- Four physical packages do not determine full versus half winding.
nNarratedDiodes : Nat
nNarratedDiodes = Speech.numberMagnitude Speech.midpointFourDiodes

sourceFour : nNarratedDiodes ≡ 4
sourceFour = refl

fullOppositeConductsBothPositive :
  forwardConduction selectedFullSecondary fromOppositeElectricalEnds
    positiveHalf ≡ receivesPositiveCurrent
fullOppositeConductsBothPositive = refl

fullOppositeConductsBothNegative :
  forwardConduction selectedFullSecondary fromOppositeElectricalEnds
    negativeHalf ≡ receivesPositiveCurrent
fullOppositeConductsBothNegative = refl

oneEndHasNoNegativeHalfCurrent :
  (span : CoilSpan) →
  forwardConduction span fromOneElectricalEnd negativeHalf
    ≡ disconnectedAtIdealDiodes
oneEndHasNoNegativeHalfCurrent selectedFullSecondary = refl
oneEndHasNoNegativeHalfCurrent selectedHalfSecondary = refl

halfSecondaryHasNoNegativeHalfCurrent :
  (landing : InputLanding) →
  forwardConduction selectedHalfSecondary landing negativeHalf
    ≡ disconnectedAtIdealDiodes
halfSecondaryHasNoNegativeHalfCurrent fromOppositeElectricalEnds = refl
halfSecondaryHasNoNegativeHalfCurrent fromOneElectricalEnd = refl

positivePeakCannotSelectSpan :
  (span : CoilSpan) (landing : InputLanding) →
  forwardConduction span landing positiveHalf
    ≡ receivesPositiveCurrent
positivePeakCannotSelectSpan selectedFullSecondary fromOppositeElectricalEnds = refl
positivePeakCannotSelectSpan selectedFullSecondary fromOneElectricalEnd = refl
positivePeakCannotSelectSpan selectedHalfSecondary fromOppositeElectricalEnds = refl
positivePeakCannotSelectSpan selectedHalfSecondary fromOneElectricalEnd = refl

-- Strong inverse discriminator IF the selected ideal-output model has
-- verified positive load conduction in the second half cycle.
negativeHalfConductionForcesFullSpan :
  (span : CoilSpan) (landing : InputLanding) →
  forwardConduction span landing negativeHalf
    ≡ receivesPositiveCurrent →
  span ≡ selectedFullSecondary
negativeHalfConductionForcesFullSpan selectedFullSecondary fromOppositeElectricalEnds p = refl
negativeHalfConductionForcesFullSpan selectedFullSecondary fromOneElectricalEnd ()
negativeHalfConductionForcesFullSpan selectedHalfSecondary fromOppositeElectricalEnds ()
negativeHalfConductionForcesFullSpan selectedHalfSecondary fromOneElectricalEnd ()

negativeHalfConductionForcesOppositeInputs :
  (span : CoilSpan) (landing : InputLanding) →
  forwardConduction span landing negativeHalf
    ≡ receivesPositiveCurrent →
  landing ≡ fromOppositeElectricalEnds
negativeHalfConductionForcesOppositeInputs selectedFullSecondary fromOppositeElectricalEnds p = refl
negativeHalfConductionForcesOppositeInputs selectedFullSecondary fromOneElectricalEnd ()
negativeHalfConductionForcesOppositeInputs selectedHalfSecondary fromOppositeElectricalEnds ()
negativeHalfConductionForcesOppositeInputs selectedHalfSecondary fromOneElectricalEnd ()

-- An observed positive load current in the first half-cycle alone has no
-- unique inverse: both electrically distinct source graph completions
-- satisfy the same positive answer. The full waveform disambiguates only
-- under the IDEAL unsmoothed, independent fixed sine model. Actual capacitor
-- output storage, spark-gaps, nonlinear source and external signed work
-- invalidate these finite inference premises and require other owners.
