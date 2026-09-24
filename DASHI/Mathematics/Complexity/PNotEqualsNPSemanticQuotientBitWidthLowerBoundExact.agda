module DASHI.Mathematics.Complexity.PNotEqualsNPSemanticQuotientBitWidthLowerBoundExact where

------------------------------------------------------------------------
-- SEMANTIC QUOTIENT BIT-WIDTH LOWER BOUND
--
-- Companion:
--   PNotEqualsNPSemanticQuotientExponentialNoGoExact
--   PNotEqualsNPSemanticQuotientClassLowerBoundExact
--
-- P9 proposes a cheap invariant Q(a) of a restricted instance such that
--
--   Q(a) = Q(b)
--      =>
--   the restricted problems have the same semantics.
--
-- For equality residual functions on n-bit prefixes, even this weaker
-- semantic-preservation requirement already forces an n-bit quotient code.
--
-- IMPORTANT:
--
-- This is stronger than the raw-residual exact-summary theorem in a different
-- direction.  We do NOT ask to reconstruct the residual function's prefix or
-- any local residual vector.  We ask only that equal quotient codes imply
-- equal residual Boolean functions.
--
-- Since equality has 2^n pairwise distinct residual functions, an m-bit code
-- with m<n cannot be sound.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool)
open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Nat using (Nat)
open import Data.Empty using (⊥)
open import Data.Fin.Base using (Fin)
import Data.Fin.Properties as FinP
open import Data.Nat.Base using (_≤_; _<_)
import Data.Nat.Properties as NatP
open import Data.Vec.Base using (Vec)

import DASHI.Mathematics.Complexity.PNotEqualsNPExactResidualSummaryBitLowerBoundExact as Bits
import DASHI.Mathematics.Complexity.PNotEqualsNPSemanticQuotientExponentialNoGoExact as Semantic

------------------------------------------------------------------------
-- Bit-coded semantic invariant.
------------------------------------------------------------------------

record EqualityResidualBitInvariant
    (prefixBits invariantBits : Nat) : Set₁ where
  constructor equality-residual-bit-invariant
  field
    invariant :
      Fin (Bits.bitCardinality prefixBits) →
      Vec Bool invariantBits

    sameInvariantImpliesSameResidualFunction :
      ∀ {left right :
          Fin (Bits.bitCardinality prefixBits)} →
      invariant left ≡ invariant right →
      (input : Vec Bool prefixBits) →
      Semantic.indexedResidualFunction left input
      ≡
      Semantic.indexedResidualFunction right input

open EqualityResidualBitInvariant public

------------------------------------------------------------------------
-- Convert the m-bit invariant to its canonical Fin(2^m) class index.
------------------------------------------------------------------------

invariantClass :
  ∀ {prefixBits invariantBits : Nat} →
  EqualityResidualBitInvariant
    prefixBits
    invariantBits →
  Fin (Bits.bitCardinality prefixBits) →
  Fin (Bits.bitCardinality invariantBits)
invariantClass quotient prefix =
  Bits.bitsToFin
    (invariant quotient prefix)

invariantClassInjective :
  ∀ {prefixBits invariantBits : Nat}
    (quotient :
      EqualityResidualBitInvariant
        prefixBits
        invariantBits)
    {left right :
      Fin (Bits.bitCardinality prefixBits)} →
  invariantClass quotient left
  ≡ invariantClass quotient right →
  left ≡ right
invariantClassInjective quotient sameClass =
  Semantic.indexedResidualFunctionInjective
    (sameInvariantImpliesSameResidualFunction
      quotient
      (Bits.bitsToFinInjective sameClass))

------------------------------------------------------------------------
-- Main width lower bound.
------------------------------------------------------------------------

semanticInvariantCannotUseFewerBits :
  ∀ {prefixBits invariantBits : Nat}
    (quotient :
      EqualityResidualBitInvariant
        prefixBits
        invariantBits) →
  invariantBits < prefixBits →
  ⊥
semanticInvariantCannotUseFewerBits
    quotient invariantSmaller =
  FinP.<⇒notInjective
    (Bits.bitCardinalityStrict invariantSmaller)
    (invariantClassInjective quotient)

semanticInvariantNeedsAtLeastPrefixWidth :
  ∀ {prefixBits invariantBits : Nat}
    (quotient :
      EqualityResidualBitInvariant
        prefixBits
        invariantBits) →
  prefixBits ≤ invariantBits
semanticInvariantNeedsAtLeastPrefixWidth quotient =
  NatP.≮⇒≥
    (λ invariantSmaller →
      semanticInvariantCannotUseFewerBits
        quotient
        invariantSmaller)

------------------------------------------------------------------------
-- Research consequence.
--
-- Generic block-order Shannon quotienting cannot even encode its semantic
-- classes in fewer than n Boolean bits on the equality family.
--
-- The positive interleaved-order theorem shows this lower bound is
-- decomposition-sensitive rather than intrinsic to equality itself.
--
-- Therefore a successful P9 theorem for the SAT self-diagonal family must
-- jointly derive:
--
--   * a special decomposition/restriction order; and
--   * a small semantic state invariant under that order.
------------------------------------------------------------------------
