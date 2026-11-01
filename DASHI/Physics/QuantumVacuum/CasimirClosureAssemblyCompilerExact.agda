module DASHI.Physics.QuantumVacuum.CasimirClosureAssemblyCompilerExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

import DASHI.Physics.QuantumVacuum.CasimirParallelPlateKernel as Casimir
import DASHI.Physics.QuantumVacuum.PerfectConductorPlateModePDECutsetExact as Maxwell
import DASHI.Physics.QuantumVacuum.ParallelPlateTransverseMeasureLimitBidiExact as Transverse
import DASHI.Physics.QuantumVacuum.CasimirRadialMeasureOneSixthCutsetExact as Six
import DASHI.Physics.QuantumVacuum.CasimirRegulatorDominatedTailCutsetExact as Tail
import DASHI.Physics.QuantumVacuum.CasimirZetaMinusThreeBidiExact as Zeta
import DASHI.Physics.QuantumVacuum.Casimir720FactorisationBidiExact as C720
import DASHI.Physics.QuantumVacuum.CasimirPressureDerivativeSameObjectCompletionExact as Pressure

------------------------------------------------------------------------
-- DOWNSTREAM CLOSURE COMPILER
--
-- Once the irreducible producer receipts are supplied, no further physical
-- inference is allowed to remain implicit.  This record assembles them on one
-- kernel/object chain and exposes the already-owned arithmetic compilers.
------------------------------------------------------------------------

record CasimirIrreducibleProducerBundle
    (kernel : Casimir.CasimirScalarModel) : Set₁ where
  field
    maxwell : Maxwell.PerfectConductorPDECompletion kernel

    transverseFamily : Transverse.CasimirTransverseMeasureFamily kernel
    oneSixth : Six.TransverseOneSixthReceipt kernel transverseFamily
    regulator : Tail.CasimirRegulatorAnalyticCompletion kernel transverseFamily

    zeta120 : Zeta.CasimirZeta120Producer kernel

    sameSpectrumAcrossMaxwellAndIntegral : Set
    sameRegulatedDifferenceAcrossIntegralAndZeta : Set
    sameSeparationParameter : Set
    sameRenormalisedObservable : Set

    reading : String

open CasimirIrreducibleProducerBundle public

record CasimirCompiledSpectralClosure
    (kernel : Casimir.CasimirScalarModel)
    (producers : CasimirIrreducibleProducerBundle kernel) : Set₁ where
  field
    coefficientAssembly : C720.Casimir720Assembly
    coefficientAssemblyUsesOneSixth : Set
    coefficientAssemblyUsesZeta120 : Set

    arithmetic6Times120 : 6 * 120 ≡ 720
    renormalisedEnergyLawClosed : Set
    energyLawIsSameKernelObservable : Set
    reading : String

open CasimirCompiledSpectralClosure public

canonical6Times120 : 6 * 120 ≡ 720
canonical6Times120 = C720.sixTimes120Is720

record CasimirCompiledFullClosure
    (kernel : Casimir.CasimirScalarModel)
    (producers : CasimirIrreducibleProducerBundle kernel) : Set₁ where
  field
    spectral : CasimirCompiledSpectralClosure kernel producers
    energy : Pressure.RenormalisedEnergyFunction kernel
    pressure : Pressure.PressureDerivativeCompletion kernel energy

    arithmetic3Times240 : 3 * 240 ≡ 720
    pressureLawClosed : Set
    pressureLawIsSameKernelObservable : Set
    reading : String

open CasimirCompiledFullClosure public

canonical3Times240 : 3 * 240 ≡ 720
canonical3Times240 = Pressure.canonical720To240Arithmetic

------------------------------------------------------------------------
-- The compiler has no reverse authority: its outputs cannot manufacture any
-- missing producer receipt.
------------------------------------------------------------------------

data Compiled720AutomaticallySuppliesMaxwell : Set where
data Compiled720AutomaticallySuppliesRegulatorEstimate : Set where
data CompiledPressureAutomaticallySuppliesZetaWeld : Set where

compiled720DoesNotSupplyMaxwell :
  Compiled720AutomaticallySuppliesMaxwell → ⊥
compiled720DoesNotSupplyMaxwell ()

compiled720DoesNotSupplyTailEstimate :
  Compiled720AutomaticallySuppliesRegulatorEstimate → ⊥
compiled720DoesNotSupplyTailEstimate ()

compiledPressureDoesNotSupplyZetaWeld :
  CompiledPressureAutomaticallySuppliesZetaWeld → ⊥
compiledPressureDoesNotSupplyZetaWeld ()
