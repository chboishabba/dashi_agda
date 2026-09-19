module DASHI.Analysis.BishopArchimedeanLinearAbsorptionValidation where

open import Agda.Builtin.Nat using (Nat)
import Real as BishopReal

import DASHI.Analysis.BishopArchimedeanLinearAbsorptionExact as A
import DASHI.Foundations.BishopFiniteDegreeOneGeometricIdentityExact as NatReal

cutoffAbsorbsConstantTimesRatio :
  ∀ {ratio largerRatio : BishopReal.ℝ}
    (inputs : A.BishopStrictRatioPair ratio largerRatio)
    (coefficient : Nat) →
  ∀ n →
  A.absorptionCutoff inputs coefficient A.≤ℕ n →
  BishopReal._≤_
    (BishopReal._*_
      (NatReal.natReal coefficient)
      ratio)
    (BishopReal._*_
      (NatReal.natReal n)
      (A.ratioGap inputs))
cutoffAbsorbsConstantTimesRatio =
  A.eventualLinearGapAbsorption
