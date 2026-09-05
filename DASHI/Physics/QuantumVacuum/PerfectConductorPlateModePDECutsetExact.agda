module DASHI.Physics.QuantumVacuum.PerfectConductorPlateModePDECutsetExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)

import DASHI.Physics.QuantumVacuum.CasimirParallelPlateKernel as Casimir
import DASHI.Physics.QuantumVacuum.PerfectConductorMaxwellSpectrumBidiExact as Spectrum

------------------------------------------------------------------------
-- PERFECT-CONDUCTOR PLATE PDE CUTSET
--
-- This is the literal producer-side decomposition needed to discharge the
-- existing spectral interface.  No source-free Maxwell statement, separation
-- ansatz, sine/cosine zero theorem, or completeness theorem is hidden inside a
-- Boolean status flag.
------------------------------------------------------------------------

record PerfectConductorTraceProblem : Set₁ where
  field
    FieldConfiguration : Set
    BoundaryPoint : Set
    TangentialElectricZero : FieldConfiguration → BoundaryPoint → Set
    NormalMagneticZero : FieldConfiguration → BoundaryPoint → Set
    traceTheorem : Set
    reading : String

open PerfectConductorTraceProblem public

record SourceFreeInteriorWaveProblem : Set₁ where
  field
    FieldConfiguration : Set
    InteriorPoint : Set
    Frequency : Set
    sourceFreeMaxwell : FieldConfiguration → Set
    waveEquation : FieldConfiguration → Frequency → Set
    maxwellImpliesWaveEquation : Set
    reading : String

open SourceFreeInteriorWaveProblem public

record PlateSeparationOfVariables : Set₁ where
  field
    TransverseCoordinate LongitudinalCoordinate Scalar : Set
    longitudinalMode : Nat → LongitudinalCoordinate → Scalar
    transverseMode : TransverseCoordinate → Scalar
    separatedField : Nat → TransverseCoordinate → LongitudinalCoordinate → Scalar

    separationLaw : Set
    boundaryTraceReducesToEndpointZeros : Set
    reading : String

open PlateSeparationOfVariables public

record LongitudinalQuantisationReceipt : Set₁ where
  field
    Scalar : Set
    Length : Set
    WaveNumber : Set
    pi : Scalar
    divide : Scalar → Scalar → Scalar
    fromNat : Nat → Scalar
    lengthValue : Length → Scalar
    longitudinalWaveNumber : Length → Nat → WaveNumber

    endpointZeroTheorem : Set
    noMissingPositiveModes : Set
    quantisationLaw : Set
    reading : String

open LongitudinalQuantisationReceipt public

record TETMCompletenessReceipt : Set₁ where
  field
    PhysicalMode : Set
    TE TM : PhysicalMode → Set
    longitudinalIndex : PhysicalMode → Nat
    zeroSector : PhysicalMode → Set

    everyPhysicalModeTEorTM : Set
    noDoubleCountingAwayFromZeroSector : Set
    zeroSectorCountingCorrect : Set
    transverseCompleteness : Set
    longitudinalCompleteness : Set
    reading : String

open TETMCompletenessReceipt public

record PerfectConductorPDECompletion
    (kernel : Casimir.CasimirScalarModel) : Set₁ where
  field
    trace : PerfectConductorTraceProblem
    interior : SourceFreeInteriorWaveProblem
    separation : PlateSeparationOfVariables
    quantisation : LongitudinalQuantisationReceipt
    completeness : TETMCompletenessReceipt

    sameFieldObjectAcrossStages : Set
    sameBoundarySeparationAcrossStages : Set
    sameModeIndexAcrossStages : Set

    spectralProducer : Spectrum.PerfectConductorSpectrumProducer kernel
    producerGeneratedByTheseStages : Set
    reading : String

open PerfectConductorPDECompletion public

------------------------------------------------------------------------
-- Reverse obligations and no-promotion boundaries.
------------------------------------------------------------------------

record PerfectConductorPDEObligations : Set where
  field
    traceBoundaryTheorem : Set
    sourceFreeWaveTheorem : Set
    separationTheorem : Set
    endpointZeroClassification : Set
    teTmCompleteness : Set
    zeroModeCounting : Set
    transverseCompleteness : Set

open PerfectConductorPDEObligations public

data BoundaryTraceImpliesCompleteness : Set where
data QuantisationFormulaImpliesPhysicalCompleteness : Set where

traceDoesNotAutoSupplyCompleteness : BoundaryTraceImpliesCompleteness → ⊥
traceDoesNotAutoSupplyCompleteness ()

quantisationDoesNotAutoSupplyCompleteness :
  QuantisationFormulaImpliesPhysicalCompleteness → ⊥
quantisationDoesNotAutoSupplyCompleteness ()
