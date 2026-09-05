module DASHI.Physics.QuantumVacuum.ParallelPlateCasimirAnalyticWallExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

import DASHI.Physics.QuantumVacuum.CasimirParallelPlateKernel as Kernel
import DASHI.Physics.QuantumVacuum.PhysicalQuantities as Q
import DASHI.Physics.QuantumVacuum.ParallelPlateModeSpectrumCutsetExact as Cutset

------------------------------------------------------------------------
-- MINIMAL ANALYTIC WALL
--
-- Everything in the zero-point/Casimir lane before this file is either exact
-- finite algebra, generic non-factorability, a typed physical-spectrum
-- interface, or an already-owned Casimir equation kernel.
--
-- What remains is the actual continuum spectral calculation.  We split it into
-- receipts so future work cannot hide several analytic payments behind one
-- opaque "renormalisation" flag.
------------------------------------------------------------------------

record PhysicalModeIdentification
    (kernel : Kernel.CasimirScalarModel) : Set₁ where
  field
    spectrum : Cutset.ParallelPlateSpectralModel kernel

    conductingBoundaryConditions : Set
    TEPPolarisationCounting : Set
    longitudinalSpectrumIdentification : Set
    transverseMomentumSemantics : Set

    physicalSpectrumClosed : Set
    reading : String

open PhysicalModeIdentification public

record RegulatedReferenceSubtraction
    (kernel : Kernel.CasimirScalarModel)
    (physical : PhysicalModeIdentification kernel) : Set₁ where
  field
    regulator : Cutset.ParallelPlateRegulator (spectrum physical)

    sameCutoffComparison : Set
    plateReferenceCancellation : Set
    cutoffRemovalExists : Set
    cutoffRemovalIndependentOfPresentation : Set

    reading : String

open RegulatedReferenceSubtraction public

record TransverseContinuumEvaluation
    (kernel : Kernel.CasimirScalarModel)
    (physical : PhysicalModeIdentification kernel) : Set₁ where
  field
    continuumTransverseMeasure : Set
    finiteToContinuumPassage : Set
    integrabilityAfterSubtraction : Set
    transverseIntegralEvaluation : Set
    reading : String

open TransverseContinuumEvaluation public

record LongitudinalSumEvaluation
    (kernel : Kernel.CasimirScalarModel)
    (physical : PhysicalModeIdentification kernel) : Set₁ where
  field
    summationTransformation : Set
    boundaryDependentFinitePart : Set
    coefficient720Produced : Set
    reading : String

open LongitudinalSumEvaluation public

record PressureDifferentiationReceipt
    (kernel : Kernel.CasimirScalarModel) : Set₁ where
  field
    derivativeSemantics : Set
    differentiateEnergyPerArea : Set
    coefficient240Produced : Set
    pressureSameObject : Set
    reading : String

open PressureDifferentiationReceipt public

------------------------------------------------------------------------
-- Completion bundle.  Supplying this bundle is exactly the remaining physics /
-- analysis needed to instantiate the cutset's renormalised-evaluation owner.
------------------------------------------------------------------------

record ParallelPlateAnalyticCompletion
    (kernel : Kernel.CasimirScalarModel) : Set₁ where
  field
    physicalModes : PhysicalModeIdentification kernel
    subtraction : RegulatedReferenceSubtraction kernel physicalModes
    transverseContinuum : TransverseContinuumEvaluation kernel physicalModes
    longitudinalEvaluation : LongitudinalSumEvaluation kernel physicalModes
    pressureDifferentiation : PressureDifferentiationReceipt kernel

    EvaluationCarrier : Set
    evaluationCarrier : EvaluationCarrier

    energyCoefficientWeld :
      (d : Q.Length) → Set

    pressureCoefficientWeld :
      (d : Q.Length) → Set

    completionReading : String

open ParallelPlateAnalyticCompletion public

------------------------------------------------------------------------
-- No individual finite or representation-theoretic theorem currently in the
-- lane manufactures these analytic receipts.  This is the exact wall rather
-- than a generic "more analysis needed" marker.
------------------------------------------------------------------------

record AnalyticWallStatus : Set where
  field
    finiteOscillatorAlgebraClosed : Bool
    rationalHalfScaleClosed : Bool
    finiteBoundaryNonfactorabilityClosed : Bool
    physicalSpectrumInterfaceClosed : Bool

    conductingModeIdentificationClosed : Bool
    regulatedReferenceSubtractionClosed : Bool
    transverseContinuumEvaluationClosed : Bool
    longitudinalFinitePartEvaluationClosed : Bool
    pressureDifferentiationSameObjectClosed : Bool

    finiteOscillatorAlgebraClosedIsTrue : finiteOscillatorAlgebraClosed ≡ true
    rationalHalfScaleClosedIsTrue : rationalHalfScaleClosed ≡ true
    finiteBoundaryNonfactorabilityClosedIsTrue : finiteBoundaryNonfactorabilityClosed ≡ true
    physicalSpectrumInterfaceClosedIsTrue : physicalSpectrumInterfaceClosed ≡ true

    conductingModeIdentificationClosedIsFalse : conductingModeIdentificationClosed ≡ false
    regulatedReferenceSubtractionClosedIsFalse : regulatedReferenceSubtractionClosed ≡ false
    transverseContinuumEvaluationClosedIsFalse : transverseContinuumEvaluationClosed ≡ false
    longitudinalFinitePartEvaluationClosedIsFalse : longitudinalFinitePartEvaluationClosed ≡ false
    pressureDifferentiationSameObjectClosedIsFalse : pressureDifferentiationSameObjectClosed ≡ false

open AnalyticWallStatus public

canonicalAnalyticWallStatus : AnalyticWallStatus
canonicalAnalyticWallStatus =
  record
    { finiteOscillatorAlgebraClosed = true
    ; rationalHalfScaleClosed = true
    ; finiteBoundaryNonfactorabilityClosed = true
    ; physicalSpectrumInterfaceClosed = true
    ; conductingModeIdentificationClosed = false
    ; regulatedReferenceSubtractionClosed = false
    ; transverseContinuumEvaluationClosed = false
    ; longitudinalFinitePartEvaluationClosed = false
    ; pressureDifferentiationSameObjectClosed = false
    ; finiteOscillatorAlgebraClosedIsTrue = refl
    ; rationalHalfScaleClosedIsTrue = refl
    ; finiteBoundaryNonfactorabilityClosedIsTrue = refl
    ; physicalSpectrumInterfaceClosedIsTrue = refl
    ; conductingModeIdentificationClosedIsFalse = refl
    ; regulatedReferenceSubtractionClosedIsFalse = refl
    ; transverseContinuumEvaluationClosedIsFalse = refl
    ; longitudinalFinitePartEvaluationClosedIsFalse = refl
    ; pressureDifferentiationSameObjectClosedIsFalse = refl
    }
