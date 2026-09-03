module DASHI.Physics.QuantumVacuum.CasimirPressureDerivativeSameObjectCompletionExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

import DASHI.Analysis.InversePowerDerivativeCompilerExact as Derivative
import DASHI.Physics.QuantumVacuum.CasimirParallelPlateKernel as Casimir
import DASHI.Physics.QuantumVacuum.CasimirCoefficient720To240CompilerExact as Coeff

------------------------------------------------------------------------
-- SAME-OBJECT CASIMIR PRESSURE DERIVATIVE COMPLETION
------------------------------------------------------------------------

record RenormalisedEnergyFunction
    (kernel : Casimir.CasimirScalarModel) : Set₁ where
  field
    SeparationParameter : Set
    energyFunction : SeparationParameter → Casimir.Scalar kernel
    separationToLength : SeparationParameter → DASHI.Physics.QuantumVacuum.PhysicalQuantities.Length

    isLiteralRenormalisedSpectralObservable : Set
    agreesWithKernelEnergyPerArea : Set
    reading : String

open RenormalisedEnergyFunction public

record PressureDerivativeCompletion
    (kernel : Casimir.CasimirScalarModel)
    (energy : RenormalisedEnergyFunction kernel) : Set₁ where
  field
    derivativeProblem : Derivative.InversePowerDerivativeProblem
    inverseCubeReceipt : Derivative.InversePowerDerivativeReceipt derivativeProblem

    derivativeActsOnLiteralEnergyFunction : Set
    minusBoundaryDerivativeConvention : Set
    coefficientThreeTransport : Set
    coefficient720To240Compiler : Coeff.ThreeTimes240Is720Receipt
    pressureSameObject : Set
    agreesWithKernelPressure : Set
    reading : String

open PressureDerivativeCompletion public

data ClosedEnergyFormulaAutomaticallySuppliesDerivative : Set where

energyFormulaNeedsSameObjectCalculus :
  ClosedEnergyFormulaAutomaticallySuppliesDerivative → ⊥
energyFormulaNeedsSameObjectCalculus ()
