module DASHI.Mathematics.Complexity.PNotEqualsNPExactResidualSummaryBitLowerBoundExact where

------------------------------------------------------------------------
-- EXACT RAW-RESIDUAL SUMMARY BIT LOWER BOUND
--
-- PNotEqualsNPGenericGateResidualCubeExact proves that the ordinary local
-- residual family of every concrete circuit is the full Boolean cube Bool^g.
--
-- This owner pays the corresponding information-theoretic theorem:
--
--   an exact summary Bool^n -> Bool^m with a left-inverse cannot have m < n.
--
-- The proof is finite and constructive:
--
--   Bool^n  <->  Fin (2^n)
--
-- by recursive Fin.splitAt/join, followed by the stdlib finite pigeonhole
-- theorem.  No entropy/probability assumption is used.
--
-- IMPORTANT BOUNDARY:
--
-- This rules out LOSSLESS compression of the raw residual vector.  It does
-- not rule out a short semantic theorem/certificate which proves correctness
-- without reconstructing every residual coordinate.  That semantic route is
-- exactly the surviving P11 programme.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Data.Empty using (⊥)
open import Data.Fin.Base as Fin using (Fin; zero; splitAt; join)
import Data.Fin.Properties as FinP
open import Data.Nat.Base using (_^_; _≤_; _<_; z≤n; s≤s)
import Data.Nat.Properties as NatP
open import Data.Sum.Base using (inj₁; inj₂)
open import Data.Vec.Base using (Vec; []; _∷_)
open import Relation.Binary.PropositionalEquality using (cong; sym; trans)

------------------------------------------------------------------------
-- Cardinality carrier: 2^n.
------------------------------------------------------------------------

bitCardinality : Nat → Nat
bitCardinality n =
  2 ^ n

oneLessThanTwo : 1 < 2
oneLessThanTwo =
  s≤s (s≤s z≤n)

bitCardinalityStrict :
  ∀ {smaller larger : Nat} →
  smaller < larger →
  bitCardinality smaller < bitCardinality larger
bitCardinalityStrict =
  NatP.^-monoʳ-< 2 oneLessThanTwo

------------------------------------------------------------------------
-- Recursive Bool^n <-> Fin(2^n) codec.
------------------------------------------------------------------------

bitsToFin :
  ∀ {width : Nat} →
  Vec Bool width →
  Fin (bitCardinality width)
bitsToFin {zero} [] =
  Fin.zero
bitsToFin {suc width} (false ∷ bits) =
  Fin.join
    (bitCardinality width)
    (bitCardinality width)
    (inj₁ (bitsToFin bits))
bitsToFin {suc width} (true ∷ bits) =
  Fin.join
    (bitCardinality width)
    (bitCardinality width)
    (inj₂ (bitsToFin bits))

finToBits :
  ∀ {width : Nat} →
  Fin (bitCardinality width) →
  Vec Bool width
finToBits {zero} index =
  []
finToBits {suc width} index
    with
      Fin.splitAt
        (bitCardinality width)
        index
... | inj₁ lower =
  false ∷ finToBits lower
... | inj₂ upper =
  true ∷ finToBits upper

finToBitsAfterBitsToFin :
  ∀ {width : Nat}
    (bits : Vec Bool width) →
  finToBits (bitsToFin bits)
  ≡ bits
finToBitsAfterBitsToFin {zero} [] =
  refl
finToBitsAfterBitsToFin {suc width} (false ∷ bits)
    rewrite
      FinP.splitAt-join
        (bitCardinality width)
        (bitCardinality width)
        (inj₁ (bitsToFin bits))
      |
      finToBitsAfterBitsToFin bits =
  refl
finToBitsAfterBitsToFin {suc width} (true ∷ bits)
    rewrite
      FinP.splitAt-join
        (bitCardinality width)
        (bitCardinality width)
        (inj₂ (bitsToFin bits))
      |
      finToBitsAfterBitsToFin bits =
  refl

bitsToFinAfterFinToBits :
  ∀ {width : Nat}
    (index : Fin (bitCardinality width)) →
  bitsToFin (finToBits index)
  ≡ index
bitsToFinAfterFinToBits {zero} Fin.zero =
  refl
bitsToFinAfterFinToBits {suc width} index
    with
      Fin.splitAt
        (bitCardinality width)
        index
      |
      FinP.join-splitAt
        (bitCardinality width)
        (bitCardinality width)
        index
... | inj₁ lower | joined
    rewrite bitsToFinAfterFinToBits lower =
  joined
... | inj₂ upper | joined
    rewrite bitsToFinAfterFinToBits upper =
  joined

bitsToFinInjective :
  ∀ {width : Nat}
    {left right : Vec Bool width} →
  bitsToFin left ≡ bitsToFin right →
  left ≡ right
bitsToFinInjective {left = left} {right = right} same =
  trans
    (sym (finToBitsAfterBitsToFin left))
    (trans
      (cong finToBits same)
      (finToBitsAfterBitsToFin right))

finToBitsInjective :
  ∀ {width : Nat}
    {left right : Fin (bitCardinality width)} →
  finToBits left ≡ finToBits right →
  left ≡ right
finToBitsInjective {left = left} {right = right} same =
  trans
    (sym (bitsToFinAfterFinToBits left))
    (trans
      (cong bitsToFin same)
      (bitsToFinAfterFinToBits right))

------------------------------------------------------------------------
-- Exact summary = summary bits plus a left-inverse reopening map.
------------------------------------------------------------------------

record ExactBitSummary
    (sourceBits summaryBits : Nat) : Set₁ where
  constructor exact-bit-summary
  field
    summarize :
      Vec Bool sourceBits →
      Vec Bool summaryBits

    reopen :
      Vec Bool summaryBits →
      Vec Bool sourceBits

    reopenExact :
      (source : Vec Bool sourceBits) →
      reopen (summarize source)
      ≡ source

open ExactBitSummary public

summaryInjective :
  ∀ {sourceBits summaryBits : Nat}
    (summary : ExactBitSummary sourceBits summaryBits)
    {left right : Vec Bool sourceBits} →
  summarize summary left
  ≡ summarize summary right →
  left ≡ right
summaryInjective summary {left} {right} same =
  trans
    (sym (reopenExact summary left))
    (trans
      (cong (reopen summary) same)
      (reopenExact summary right))

------------------------------------------------------------------------
-- Induced injection on canonical finite indices.
------------------------------------------------------------------------

summaryOnFin :
  ∀ {sourceBits summaryBits : Nat} →
  ExactBitSummary sourceBits summaryBits →
  Fin (bitCardinality sourceBits) →
  Fin (bitCardinality summaryBits)
summaryOnFin summary sourceIndex =
  bitsToFin
    (summarize summary
      (finToBits sourceIndex))

summaryOnFinInjective :
  ∀ {sourceBits summaryBits : Nat}
    (summary : ExactBitSummary sourceBits summaryBits)
    {left right : Fin (bitCardinality sourceBits)} →
  summaryOnFin summary left
  ≡ summaryOnFin summary right →
  left ≡ right
summaryOnFinInjective summary {left} {right} same =
  finToBitsInjective
    (summaryInjective summary
      (bitsToFinInjective same))

------------------------------------------------------------------------
-- Main lower bound.
------------------------------------------------------------------------

exactSummaryCannotUseFewerBits :
  ∀ {sourceBits summaryBits : Nat} →
  summaryBits < sourceBits →
  ExactBitSummary sourceBits summaryBits →
  ⊥
exactSummaryCannotUseFewerBits
    summarySmaller summary =
  FinP.<⇒notInjective
    (bitCardinalityStrict summarySmaller)
    (summaryOnFinInjective summary)

exactSummaryNeedsAtLeastSourceWidth :
  ∀ {sourceBits summaryBits : Nat} →
  ExactBitSummary sourceBits summaryBits →
  sourceBits ≤ summaryBits
exactSummaryNeedsAtLeastSourceWidth summary =
  NatP.≮⇒≥
    (λ summarySmaller →
      exactSummaryCannotUseFewerBits
        summarySmaller
        summary)

------------------------------------------------------------------------
-- Research consequence.
--
-- Since ordinary gate residuals range over all Bool^g, a deterministic exact
-- code which intends to reopen that raw residual vector needs at least g bits.
--
-- Therefore any sub-gate-count P11 authority must be NON-RECONSTRUCTIVE with
-- respect to raw residuals: it must prove the desired semantic fact directly,
-- using global structure, rather than losslessly encode every possible local
-- error pattern.
------------------------------------------------------------------------
