module DASHI.Foundations.C3O2SignedWindingCompositionExact where

-- Fully paid semidirect-product associativity, conditional on additive
-- monoid associativity and the involutive distributive reversal.
open import Agda.Builtin.Equality using (_≡_; refl)
open import Relation.Binary.PropositionalEquality using (cong; trans; sym)
import DASHI.Foundations.C3O2SignedWindingTransportExact as W

record AssociativeSignedWinding : Set₁ where
  field
    base : W.SignedWindingAction
    assoc : ∀ a b c →
      W.add base (W.add base a b) c
        ≡ W.add base a (W.add base b c)
open AssociativeSignedWinding public

module Prove (S : AssociativeSignedWinding) where
  A = base S
  open W.Transport A

  actionDistributes : ∀ p a b →
    action p (W.add A a b) ≡ W.add A (action p a) (action p b)
  actionDistributes W.preserve a b = refl
  actionDistributes W.reverse a b = W.invertAdd A a b

  actionProduct : ∀ p q w →
    action (W.multiply p q) w ≡ action p (action q w)
  actionProduct = actionComposition

  composeAssociative : ∀ x y z →
    compose (compose x y) z ≡ compose x (compose y z)
  composeAssociative (pair a p) (pair b q) (pair c r)
    rewrite W.parityAssociative p q r
          | actionProduct p q c
          | assoc S a (action p b) (action p (action q c))
          | actionDistributes p b (action q c)
    = refl
