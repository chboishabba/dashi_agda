module DASHI.Algebra.Quantum.ShorCyclicPhaseAmplitudeQFTRegression where

open import DASHI.Core.Prelude
open import Data.Fin.Base using (Fin)

import DASHI.Foundations.Base369Nat as B369
import DASHI.Algebra.Quantum.QuantumFourierTransformFinite as QFT
import DASHI.Algebra.Quantum.ShorFiniteIndependentTargetAmplitudeOracleExact as Target
import DASHI.Algebra.Quantum.ShorCyclicPhaseAmplitudeQFTExact as PhaseQFT

------------------------------------------------------------------------
-- RED regression: a preferred Shor QFT must expose the literal cyclic
-- character-sum action on the finite exponent x target basis, not merely an
-- arbitrary invertible endomap.
------------------------------------------------------------------------

phaseQFTCompiles :
  ∀ {Q modulus : Nat}
    (qNonZero : B369.NonZero Q)
    (modulusNonZero : B369.NonZero modulus)
    {Coefficient : Set} →
  (A : PhaseQFT.CyclicPhaseCoefficientAuthority Coefficient Q) →
  (I : PhaseQFT.CyclicPhaseInversionAuthority A) →
  QFT.FiniteFourierTransform
    (PhaseQFT.cyclicPhaseAmplitudeRegister
      qNonZero modulusNonZero A)
phaseQFTCompiles = PhaseQFT.cyclicPhaseFiniteFourierTransform

basisForwardPinnedToCharacterSum :
  ∀ {Q modulus : Nat}
    (qNonZero : B369.NonZero Q)
    (modulusNonZero : B369.NonZero modulus)
    {Coefficient : Set} →
  (A : PhaseQFT.CyclicPhaseCoefficientAuthority Coefficient Q) →
  (I : PhaseQFT.CyclicPhaseInversionAuthority A) →
  (x : Fin Q) →
  (y : Fin modulus) →
  PhaseQFT.cyclicPhaseForward A
    (PhaseQFT.basisAmplitude qNonZero modulusNonZero A x y)
  ≡ PhaseQFT.forwardBasisCharacterSum
      qNonZero modulusNonZero A x y
basisForwardPinnedToCharacterSum qNonZero modulusNonZero A I x y = refl
