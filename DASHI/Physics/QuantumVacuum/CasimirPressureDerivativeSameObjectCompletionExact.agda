module DASHI.Physics.QuantumVacuum.CasimirPressureDerivativeSameObjectCompletionExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

import DASHI.Analysis.InversePowerDerivativeCompilerExact as Derivative
import DASHI.Physics.QuantumVacuum.CasimirParallelPlateKernel as Casimir
import DASHI.Physics.QuantumVacuum.CasimirCoefficient720To240CompilerExact as Coeff
import DASHI.Physics.QuantumVacuum.PhysicalQuantities as Q

------------------------------------------------------------------------
-- SAME-OBJECT CASIMIR PRESSURE DERIVATIVE COMPLETION
------------------------------------------------------------------------

record RenormalisedEnergyFunction
    (kernel : Casimir.CasimirScalarModel) : Set₁ where
  field
    SeparationParameter : Set
    energyFunction : SeparationParameter → Casimir.Scalar kernel
    separationToLength : SeparationParameter → Q.Length

    isLiteralRenormalisedSpectralObservable : Set
    agreesWithKernelEnergyPerArea : Set
    reading : String

open RenormalisedEnergyFunction public

record PressureDerivativeCompletion
    (kernel : Casimir.CasimirScalarModel)
    (energy : RenormalisedEnergyFunction kernel) : Set₁ where
  field
    derivativeStructure : Derivative.DerivativeStructure
    inversePowerFamily : Derivative.InversePowerFamily derivativeStructure
    inverseCubeReceipt :
      Derivative.InverseCubeDerivativeReceipt
        derivativeStructure inversePowerFamily

    derivativeActsOnLiteralEnergyFunction : Set
    minusBoundaryDerivativeConvention : Set
    coefficientThreeTransport : Set
    coefficient720To240Compiler : 3 * 240 ≡ 720
    pressureSameObject : Set
    agreesWithKernelPressure : Set
    reading : String

open PressureDerivativeCompletion public

canonical720To240Arithmetic : 3 * 240 ≡ 720
canonical720To240Arithmetic = Coeff.threeTimes240Is720

data ClosedEnergyFormulaAutomaticallySuppliesDerivative : Set where

energyFormulaNeedsSameObjectCalculus :
  ClosedEnergyFormulaAutomaticallySuppliesDerivative → ⊥
energyFormulaNeedsSameObjectCalculus ()
