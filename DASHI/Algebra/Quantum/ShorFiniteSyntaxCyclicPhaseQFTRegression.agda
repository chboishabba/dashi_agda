module DASHI.Algebra.Quantum.ShorFiniteSyntaxCyclicPhaseQFTRegression where

open import DASHI.Core.Prelude

import DASHI.Foundations.Base369Nat as B369
import DASHI.Algebra.Quantum.FiniteQuantumRegister as Finite
import DASHI.Algebra.Quantum.QuantumFourierTransformFinite as QFT
import DASHI.Algebra.Quantum.ShorFiniteIndependentTargetAmplitudeOracleExact as Target
import DASHI.Algebra.Quantum.ShorCyclicPhaseAmplitudeQFTExact as Phase
import DASHI.Algebra.Quantum.ShorFiniteSyntaxCyclicPhaseQFTExact as SyntaxQFT

------------------------------------------------------------------------
-- RED regression: the same finite syntax register that owns the exact powMod
-- amplitude oracle must also admit a literal cyclic-character QFT action.
------------------------------------------------------------------------

sameRegisterPhaseQFTExists :
  ∀ {Q N Coefficient}
    (qNonZero : B369.NonZero Q)
    (nNonZero : B369.NonZero N)
    (A : Phase.CyclicPhaseCoefficientAuthority Coefficient Q) →
  SyntaxQFT.SyntaxCyclicPhaseInversionAuthority qNonZero nNonZero A →
  QFT.FiniteFourierTransform
    (Target.finiteIndependentTargetAmplitudeRegister
      Coefficient
      (SyntaxQFT.cyclicBasis qNonZero)
      0 N nNonZero)
sameRegisterPhaseQFTExists = SyntaxQFT.syntaxCyclicPhaseFiniteFourierTransform
