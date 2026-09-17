module DASHI.Algebra.Quantum.ShorFiniteSyntaxExecutionPrefixRegression where

open import DASHI.Core.Prelude

import DASHI.Foundations.Base369Nat as B369
import DASHI.Algebra.Quantum.ShorCyclicPhaseAmplitudeQFTExact as Phase
import DASHI.Algebra.Quantum.ShorFiniteSyntaxCyclicPhaseQFTExact as SyntaxQFT
import DASHI.Algebra.Quantum.ShorFiniteSyntaxExecutionPrefixExact as Prefix

------------------------------------------------------------------------
-- RED regression: once literal character-sum inversion is supplied, the same
-- finite syntax register must compile all the way to the existing oracle+QFT
-- execution prefix.  No extra carrier weld may remain.
------------------------------------------------------------------------

sameRegisterExecutionPrefixCompiles :
  ∀ {Q N Coefficient base}
    (qNonZero : B369.NonZero Q)
    (nNonZero : B369.NonZero N)
    (A : Phase.CyclicPhaseCoefficientAuthority Coefficient Q) →
  SyntaxQFT.SyntaxCyclicPhaseInversionAuthority qNonZero nNonZero A →
  Set
sameRegisterExecutionPrefixCompiles {base = base} qNonZero nNonZero A I =
  Prefix.CompiledSyntaxPrefix qNonZero nNonZero base A I
