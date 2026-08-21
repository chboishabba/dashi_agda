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

------------------------------------------------------------------------
-- Aggregate kernel envelope.
--
-- `kernelEnvelope` is intended to be the sum of bounds for
--   (Im Phi(z_rho-z_sigma))^2 +
--   (Im Phi(z_rho-conj z_sigma))^2
-- after the complex-Poisson S/H identification.
------------------------------------------------------------------------

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

------------------------------------------------------------------------
-- CONNECTION: pairwise kernel decay/summability is enough for the exact
-- almost-orthogonality certificate.
------------------------------------------------------------------------

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
-- This spelling makes the new analytic tasks explicit.  The first two fields
-- are source-facing complex-Poisson identifications; the third is the actual
-- summation theorem.  Existing local zero counts and Montgomery--Vaughan may
-- be used to build `aggregateEnvelopeBound`, but are not asserted to do so
-- without a representation lemma.
------------------------------------------------------------------------

record ComplexPhiKernelEnvelopeProducer : Set₁ where
  field
    ZeroPair : Set
    PairIndex : Set

    DifferencePhiImaginaryEnergy : PairIndex → Nat
    SumPhiImaginaryEnergy : PairIndex → Nat
    Envelope : PairIndex → Nat

    differenceKernelEnvelope :
      (i : PairIndex) →
      DifferencePhiImaginaryEnergy i → Set

    sumKernelEnvelope :
      (i : PairIndex) →
      SumPhiImaginaryEnergy i → Set

    AggregateEnvelopeBound : Set
    aggregateEnvelopeBound : AggregateEnvelopeBound

record MixedKernelEnvelopeBoundary : Set where
  field
    mixedToKernelEnvelopeFactorConstructed : Agda.Builtin.Bool.Bool
    kernelEnvelopeToAlmostOrthogonalityClosed : Agda.Builtin.Bool.Bool
    complexSHToPhiIdentificationProvedHere : Agda.Builtin.Bool.Bool
    pairwiseComplexPhiDecayProvedHere : Agda.Builtin.Bool.Bool
    zeroPairEnvelopeSummedHere : Agda.Builtin.Bool.Bool
    montgomeryVaughanApplicabilityProvedHere : Agda.Builtin.Bool.Bool

open import Agda.Builtin.Bool using (Bool; true; false)

mixedKernelEnvelopeBoundary : MixedKernelEnvelopeBoundary
mixedKernelEnvelopeBoundary = record
  { mixedToKernelEnvelopeFactorConstructed = true
  ; kernelEnvelopeToAlmostOrthogonalityClosed = true
  ; complexSHToPhiIdentificationProvedHere = false
  ; pairwiseComplexPhiDecayProvedHere = false
  ; zeroPairEnvelopeSummedHere = false
  ; montgomeryVaughanApplicabilityProvedHere = false
  }
