module DASHI.Analysis.ConcreteComplexConjugationProductExact where

------------------------------------------------------------------------
-- CONCRETE COMPLEX CONJUGATION IS MULTIPLICATIVE
--
-- Cross-pollination:
--
--   DASHI.Analysis.RiemannConstructedRealPhaseCoherenceExact
--
-- already isolates the one ordinary real-ring leaf
--
--   -(x*y) = (-x)*y.
--
-- Together with commutativity, negation involutivity, and the existing
-- ring-normalisation law -(x+y)=(-x)+(-y), that leaf is sufficient to prove
--
--   conjugate(z*w) = conjugate(z) * conjugate(w)
--
-- for the literal ConcreteComplex pair representation.  No complex-specific
-- axiom is needed.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Relation.Binary.PropositionalEquality using (cong; cong₂; sym; trans)

open import DASHI.Analysis.ConstructiveRealSpine
open import DASHI.Analysis.ConcreteComplex
import DASHI.Analysis.MarxConstructiveRealRingNormalisation as Ring
import DASHI.Analysis.RiemannConstructedRealPhaseCoherenceExact as Phase

------------------------------------------------------------------------
-- Derived right-coordinate negation law x*(-y)=-(x*y).
------------------------------------------------------------------------

mulNegRightDerived :
  ∀ {R : ConstructedOrderedCompleteReal} →
  Phase.ConstructedRealNegationMultiplicationLaw R →
  (x y : Real R) →
  _*_ R x (neg R y) ≡ neg R (_*_ R x y)
mulNegRightDerived {R} M x y =
  trans
    (mulComm R x (neg R y))
    (trans
      (sym (Phase.negMulRight M y x))
      (cong (neg R) (mulComm R y x)))

------------------------------------------------------------------------
-- Two negatives cancel in a product.
------------------------------------------------------------------------

mulNegNeg :
  ∀ {R : ConstructedOrderedCompleteReal} →
  (C : ComplexAlgebraLaws R) →
  Phase.ConstructedRealNegationMultiplicationLaw R →
  (x y : Real R) →
  _*_ R (neg R x) (neg R y) ≡ _*_ R x y
mulNegNeg {R} C M x y =
  trans
    (mulNegRightDerived M (neg R x) y)
    (trans
      (cong (neg R) (sym (Phase.negMulRight M x y)))
      (negInvolutive C (_*_ R x y)))

------------------------------------------------------------------------
-- Main concrete-complex theorem.
------------------------------------------------------------------------

conjugateProduct :
  ∀ {R : ConstructedOrderedCompleteReal} →
  (C : ComplexAlgebraLaws R) →
  (N : Ring.ConstructedRealRingNormalisationLaws R) →
  (M : Phase.ConstructedRealNegationMultiplicationLaw R) →
  (z w : ComplexPair R) →
  conjugateC (_*C_ z w)
  ≡ _*C_ (conjugateC z) (conjugateC w)
conjugateProduct {R} C N M
  (complex a b) (complex c d) =
  cong₂ (complex {R})
    (cong (λ x → _-_ R (_*_ R a c) x)
      (sym (mulNegNeg C M b d)))
    (trans
      (Ring.negAdd N (_*_ R a d) (_*_ R b c))
      (cong₂ (_+_ R)
        (sym (mulNegRightDerived M a d))
        (sym (Phase.negMulRight M b c))))

------------------------------------------------------------------------
-- Boundary: this discharges a complex-algebra seam, not the analytic Delta
-- conjugation theorem or the underlying real negation-multiplication leaf.
------------------------------------------------------------------------

record ConcreteComplexConjugationProductBoundary : Set where
  constructor concrete-complex-conjugation-product-boundary
  field
    complexConjugationMultiplicativityDerived : Bool
    noComplexSpecificMultiplicativityAxiomNeeded : Bool
    realNegationMultiplicationLeafStillRequired : Bool
    deltaConjugationFollowsFromThisAlone : Bool

open import Agda.Builtin.Bool using (Bool; true; false)
open ConcreteComplexConjugationProductBoundary public

canonicalConcreteComplexConjugationProductBoundary :
  ConcreteComplexConjugationProductBoundary
canonicalConcreteComplexConjugationProductBoundary =
  concrete-complex-conjugation-product-boundary
    true true true false
