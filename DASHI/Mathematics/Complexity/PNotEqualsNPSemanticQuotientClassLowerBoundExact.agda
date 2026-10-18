module DASHI.Mathematics.Complexity.PNotEqualsNPSemanticQuotientClassLowerBoundExact where

------------------------------------------------------------------------
-- SOUND SEMANTIC QUOTIENTS OF EQUALITY NEED 2^n CLASSES
--
-- Companion:
--   PNotEqualsNPSemanticQuotientExponentialNoGoExact
--
-- Equality on two n-bit blocks has one distinct residual Boolean function for
-- each fixed first-block assignment.
--
-- P9 is not merely about distinct functions; it asks for a quotient Q such
-- that:
--
--   Q(a) = Q(b)
--      =>
--   residualFunction(a) = residualFunction(b).
--
-- This owner proves the exact class-count lower bound:
--
--   every such sound quotient needs at least 2^n classes.
--
-- The proof is independent of how Q is computed or represented.  Soundness
-- forces Q to be injective on the 2^n equality residual functions, and finite
-- pigeonhole then forbids fewer than 2^n classes.
--
-- CONSEQUENCE:
--
-- Shannon semantic quotienting is exponentially wide in the generic case.
-- Any small quotient for the SAT self-diagonal family must exploit structure
-- special to that family, not Shannon decomposition or semantic equivalence
-- alone.
------------------------------------------------------------------------

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
-- A sound quotient of the indexed equality residual family.
------------------------------------------------------------------------

record EqualityResidualSemanticQuotient
    (width : Nat) : Set₁ where
  constructor equality-residual-semantic-quotient
  field
    classCount : Nat

    classify :
      Fin (Bits.bitCardinality width) →
      Fin classCount

    sameClassImpliesSameResidualFunction :
      ∀ {left right :
          Fin (Bits.bitCardinality width)} →
      classify left ≡ classify right →
      (input : Vec Bool width) →
      Semantic.indexedResidualFunction left input
      ≡
      Semantic.indexedResidualFunction right input

open EqualityResidualSemanticQuotient public

------------------------------------------------------------------------
-- Soundness forces the classifier to be injective.
------------------------------------------------------------------------

classifyInjective :
  ∀ {width : Nat}
    (quotient : EqualityResidualSemanticQuotient width)
    {left right :
      Fin (Bits.bitCardinality width)} →
  classify quotient left
  ≡ classify quotient right →
  left ≡ right
classifyInjective quotient sameClass =
  Semantic.indexedResidualFunctionInjective
    (sameClassImpliesSameResidualFunction
      quotient
      sameClass)

------------------------------------------------------------------------
-- Main class-count lower bound.
------------------------------------------------------------------------

semanticQuotientCannotUseFewerThanTwoPowerNClasses :
  ∀ {width : Nat}
    (quotient : EqualityResidualSemanticQuotient width) →
  classCount quotient
    < Bits.bitCardinality width →
  ⊥
semanticQuotientCannotUseFewerThanTwoPowerNClasses
    quotient tooFewClasses =
  FinP.<⇒notInjective
    tooFewClasses
    (classifyInjective quotient)

semanticQuotientNeedsAtLeastTwoPowerNClasses :
  ∀ {width : Nat}
    (quotient : EqualityResidualSemanticQuotient width) →
  Bits.bitCardinality width
    ≤ classCount quotient
semanticQuotientNeedsAtLeastTwoPowerNClasses quotient =
  NatP.≮⇒≥
    (λ tooFewClasses →
      semanticQuotientCannotUseFewerThanTwoPowerNClasses
        quotient
        tooFewClasses)

------------------------------------------------------------------------
-- Research consequence.
--
-- The generic P9 quotient problem has an exact exponential lower bound:
--
--   #classes >= 2^n
--
-- already for equality residual subfunctions.
--
-- Therefore a useful quotient on the SAT self-diagonal restriction tree must
-- prove a SPECIAL collapse theorem for that family.  "Merge semantically
-- equivalent Shannon nodes" is not, by itself, a resource closure mechanism.
------------------------------------------------------------------------
