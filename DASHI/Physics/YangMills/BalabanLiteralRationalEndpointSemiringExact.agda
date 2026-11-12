module DASHI.Physics.YangMills.BalabanLiteralRationalEndpointSemiringExact where

-- ORIGINAL selected rational interval backend, not an abstract or
-- arbitrary imaginary interval evaluator:
-- BalabanClayT4TypedRationalExpressionIntervalExact.addInterval
-- is defined by sum of rational lower/upper endpoints.
--
-- This module proves exact endpoint-wise add commutativity/associativity
-- without assuming proof irrelevance of the ordering fields. Thus these
-- are observational interval equalities, not automatic _≡_ between
-- proof-containing Eval.RationalInterval values.
--
-- The four-corner multiply operation requires separate corner-hull
-- associativity/commutativity proof; nothing below assumes them.

open import Agda.Builtin.Equality using (_≡_; refl)
import Data.Rational.Properties as ℚP
open import Relation.Binary.PropositionalEquality using (cong₂; sym; trans)
open import Data.Rational.Base as ℚ using (_+_)
import DASHI.Physics.YangMills.BalabanClayT4LiteralOneLoopBoxEvaluatorExact as Eval
import DASHI.Physics.YangMills.BalabanClayT4TypedRationalExpressionIntervalExact as Typed

record SameEndpoints (a b : Eval.RationalInterval) : Set where
  constructor sameEndpoints
  field
    lowerEqual : Eval.lower a ≡ Eval.lower b
    upperEqual : Eval.upper a ≡ Eval.upper b
open SameEndpoints public

endpointsRefl : ∀ a → SameEndpoints a a
endpointsRefl a = sameEndpoints refl refl

endpointsSym : ∀ {a b} → SameEndpoints a b → SameEndpoints b a
endpointsSym same = sameEndpoints
  (sym (lowerEqual same)) (sym (upperEqual same))

endpointsTrans : ∀ {a b c} →
  SameEndpoints a b → SameEndpoints b c → SameEndpoints a c
endpointsTrans ab bc = sameEndpoints
  (trans (lowerEqual ab) (lowerEqual bc))
  (trans (upperEqual ab) (upperEqual bc))

typedAddLowerExact : ∀ a b →
  Eval.lower (Typed.addInterval a b)
    ≡ Eval.lower a ℚ._+_ Eval.lower b
typedAddLowerExact a b = refl

typedAddUpperExact : ∀ a b →
  Eval.upper (Typed.addInterval a b)
    ≡ Eval.upper a ℚ._+_ Eval.upper b
typedAddUpperExact a b = refl

-- Explicit concrete rational interval laws.
typedAddCommutative : ∀ a b →
  SameEndpoints (Typed.addInterval a b) (Typed.addInterval b a)
typedAddCommutative a b = sameEndpoints
  (ℚP.+-comm (Eval.lower a) (Eval.lower b))
  (ℚP.+-comm (Eval.upper a) (Eval.upper b))

typedAddAssociative : ∀ a b c →
  SameEndpoints
    (Typed.addInterval (Typed.addInterval a b) c)
    (Typed.addInterval a (Typed.addInterval b c))
typedAddAssociative a b c = sameEndpoints
  (ℚP.+-assoc (Eval.lower a) (Eval.lower b) (Eval.lower c))
  (ℚP.+-assoc (Eval.upper a) (Eval.upper b) (Eval.upper c))

-- Endpoint congruence for the exact original backend.
-- Necessary when nesting a local commutation into a larger diagram sum.
addCongruence : ∀ {a b c d} →
  SameEndpoints a b → SameEndpoints c d →
  SameEndpoints (Typed.addInterval a c) (Typed.addInterval b d)
addCongruence ab cd = sameEndpoints
  (cong₂ ℚ._+_
    (lowerEqual ab) (lowerEqual cd))
  (cong₂ ℚ._+_
    (upperEqual ab) (upperEqual cd))


-- The endpoints of one swapped right-associated sum agree exactly.
typedHeadSwapEndpointExact : ∀ a b tail →
  SameEndpoints
    (Typed.addInterval a (Typed.addInterval b tail))
    (Typed.addInterval b (Typed.addInterval a tail))
typedHeadSwapEndpointExact a b tail =
  endpointsTrans
    (endpointsSym (typedAddAssociative a b tail))
    (endpointsTrans
      (addCongruence (typedAddCommutative a b) (endpointsRefl tail))
      (typedAddAssociative b a tail))

-- This precise concrete backend theorem is stronger than merely
-- postulating IntervalAdditionLaws as an arbitrary input; but it yields
-- endpoint observational equality, NOT arbitrary record identity.
-- To discharge the current full-record semantic evaluator equality,
-- prove a constructor proof-irrelevance/canonical-order-witness lemma
-- or refactor the evaluator into an endpoint-quotiented semantics.
