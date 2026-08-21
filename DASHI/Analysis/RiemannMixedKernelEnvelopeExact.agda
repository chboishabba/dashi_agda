module DASHI.Analysis.RiemannMixedKernelEnvelopeExact where

------------------------------------------------------------------------
-- PURPOSE
--
-- Factor G2 through the smallest analytic object left after the exact
-- S/H-kernel reduction:
--
--   2 N_{rho,sigma}
--      = (Im S_{rho,sigma})^2 + (Im H_{rho,sigma})^2.
--
-- An analytic argument need not estimate the original a.d / b.c channels
-- separately.  It may provide a nonnegative envelope for the two complex
-- difference/sum kernels and then sum that envelope over off-diagonal pairs.
-- This module proves the bookkeeping from such an envelope to the exact
-- PairAlmostOrthogonality object consumed by the top-down assembly.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_)

open import DASHI.Analysis.RiemannMixedChannelAlmostOrthogonalityExact
  using
    ( MixedChannelGlobalLedger
    ; PairInsideDiagonalLedger
    ; mixedInterferenceBudget
    ; otherDiagonalEnergy
    ; PairAlmostOrthogonality
    ; pairAlmostOrthogonality
    )

sym : {A : Set} {x y : A} → x ≡ y → y ≡ x
sym refl = refl

trans : {A : Set} {x y z : A} → x ≡ y → y ≡ z → x ≡ z
trans refl yz = yz

congPlusRight : {a b : Nat} → a ≡ b → (c : Nat) → a + c ≡ b + c
congPlusRight refl c = refl

+-assoc : (a b c : Nat) → (a + b) + c ≡ a + (b + c)
+-assoc zero b c = refl
+-assoc (suc a) b c rewrite +-assoc a b c = refl

record MixedKernelEnvelopeLedger
  (g : MixedChannelGlobalLedger)
  (p : PairInsideDiagonalLedger g) : Set where
  constructor mixedKernelEnvelopeLedger
  field
    kernelEnvelope : Nat
    envelopeSlack : Nat
    nonTargetMargin : Nat

    mixedInsideEnvelope :
      mixedInterferenceBudget g + envelopeSlack ≡ kernelEnvelope

    envelopeBelowOtherDiagonal :
      kernelEnvelope + nonTargetMargin ≡ otherDiagonalEnergy p

open MixedKernelEnvelopeLedger public

kernelEnvelopeImpliesPairAlmostOrthogonality :
  (g : MixedChannelGlobalLedger) →
  (p : PairInsideDiagonalLedger g) →
  MixedKernelEnvelopeLedger g p →
  PairAlmostOrthogonality g p
kernelEnvelopeImpliesPairAlmostOrthogonality g p e =
  pairAlmostOrthogonality
    (envelopeSlack e + nonTargetMargin e)
    chain
  where
  chain :
    mixedInterferenceBudget g
      + (envelopeSlack e + nonTargetMargin e)
      ≡ otherDiagonalEnergy p
  chain =
    trans
      (sym
        (+-assoc
          (mixedInterferenceBudget g)
          (envelopeSlack e)
          (nonTargetMargin e)))
      (trans
        (congPlusRight
          (mixedInsideEnvelope e)
          (nonTargetMargin e))
        (envelopeBelowOtherDiagonal e))

------------------------------------------------------------------------
-- Pairwise-to-aggregate producer socket.
--
-- The analytic producer carries numeric channel/envelope values plus evidence
-- types asserting the two pairwise envelope inequalities and the final
-- aggregate summation theorem.  Existing local zero counts and Montgomery--
-- Vaughan may discharge the aggregate theorem only after a suitable kernel
-- representation lemma has been proved.
------------------------------------------------------------------------

record ComplexPhiKernelEnvelopeProducer : Set₁ where
  field
    PairIndex : Set

    differencePhiImaginaryEnergy : PairIndex → Nat
    sumPhiImaginaryEnergy : PairIndex → Nat
    envelope : PairIndex → Nat

    DifferenceKernelInsideEnvelope : PairIndex → Set
    SumKernelInsideEnvelope : PairIndex → Set

    differenceKernelInsideEnvelope :
      (i : PairIndex) → DifferenceKernelInsideEnvelope i
    sumKernelInsideEnvelope :
      (i : PairIndex) → SumKernelInsideEnvelope i

    AggregateEnvelopeBound : Set
    aggregateEnvelopeBound : AggregateEnvelopeBound

record MixedKernelEnvelopeBoundary : Set where
  field
    mixedToKernelEnvelopeFactorConstructed : Bool
    kernelEnvelopeToAlmostOrthogonalityClosed : Bool
    complexSHToPhiIdentificationProvedHere : Bool
    pairwiseComplexPhiDecayProvedHere : Bool
    zeroPairEnvelopeSummedHere : Bool
    montgomeryVaughanApplicabilityProvedHere : Bool

mixedKernelEnvelopeBoundary : MixedKernelEnvelopeBoundary
mixedKernelEnvelopeBoundary = record
  { mixedToKernelEnvelopeFactorConstructed = true
  ; kernelEnvelopeToAlmostOrthogonalityClosed = true
  ; complexSHToPhiIdentificationProvedHere = false
  ; pairwiseComplexPhiDecayProvedHere = false
  ; zeroPairEnvelopeSummedHere = false
  ; montgomeryVaughanApplicabilityProvedHere = false
  }
