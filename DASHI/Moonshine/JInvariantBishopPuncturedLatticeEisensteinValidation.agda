module DASHI.Moonshine.JInvariantBishopPuncturedLatticeEisensteinValidation where

open import Agda.Builtin.Bool using (false; true)
open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Analysis.BishopComplexReciprocalExact as Reciprocal
import DASHI.Moonshine.JInvariantBishopLatticeEisensteinKernelExact as Kernel
import DASHI.Moonshine.JInvariantBishopUpperHalfPlaneLatticeDenominatorExact as Upper
import DASHI.Moonshine.JInvariantPuncturedLatticeReindexExact as Punctured
import DASHI.Moonshine.JInvariantBishopPuncturedLatticeEisensteinCompilerExact as Preferred
import DASHI.Physics.Closure.TriadicEisensteinTransformationTheorem as Lattice

upperHalfPlaneDenominatorRegression :
  (parameter : Upper.BishopUpperHalfPlanePoint) →
  (index : Kernel.NonzeroLatticePoint) →
  Reciprocal.BishopComplexNonzero
    (Kernel.latticeDenominator
      (Kernel.point index)
      (Upper.tau parameter))
upperHalfPlaneDenominatorRegression =
  Upper.upperHalfPlaneDenominatorNonzero

puncturedForwardRegression :
  (g : Lattice.SL2Z) →
  (index : Kernel.NonzeroLatticePoint) →
  Kernel.point
    (Punctured.inversePunctured g
      (Punctured.forwardPunctured g index))
  ≡ Kernel.point index
puncturedForwardRegression =
  Punctured.inverseForwardPoint

puncturedBackwardRegression :
  (g : Lattice.SL2Z) →
  (index : Kernel.NonzeroLatticePoint) →
  Kernel.point
    (Punctured.forwardPunctured g
      (Punctured.inversePunctured g index))
  ≡ Kernel.point index
puncturedBackwardRegression =
  Punctured.forwardInversePoint

puncturedModularityCompilerPaid :
  Preferred.rawPuncturedModularityCompilerExact
    Preferred.canonicalPreferredPuncturedEisensteinFrontier
  ≡ true
puncturedModularityCompilerPaid = refl

normalizationExplicitRegression :
  Preferred.normalizationExplicit
    Preferred.canonicalPreferredPuncturedEisensteinFrontier
  ≡ true
normalizationExplicitRegression = refl

absoluteSumStillOpenRegression :
  Preferred.concretePuncturedAbsoluteSumPaidHere
    Preferred.canonicalPreferredPuncturedEisensteinFrontier
  ≡ false
absoluteSumStillOpenRegression = refl

normalizationConstantsStillOpenRegression :
  Preferred.concreteG4G6NormalizationConstantsPaidHere
    Preferred.canonicalPreferredPuncturedEisensteinFrontier
  ≡ false
normalizationConstantsStillOpenRegression = refl
