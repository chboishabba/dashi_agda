module DASHI.Physics.YangMills.BalabanWeightedGreenKernelDecay where

open import Agda.Builtin.Equality using (_≡_)
open import Relation.Binary.PropositionalEquality using (cong; subst; sym; trans)

------------------------------------------------------------------------
-- The order-theoretic unweighting step
--
--   exp(mu d) |G(x,y)| <= C
--       implies
--   |G(x,y)| <= C exp(-mu d).
--
-- The exponential identity itself is supplied by the scalar implementation;
-- the passage from the weighted column estimate to pointwise decay is proved.
------------------------------------------------------------------------

record OrderedCommutativeMonoid (Bound : Set) : Set₁ where
  field
    one : Bound
    multiply : Bound → Bound → Bound
    LessEqual : Bound → Bound → Set

    lessEqualRefl : ∀ value → LessEqual value value
    lessEqualTrans : ∀ {a b c} → LessEqual a b → LessEqual b c → LessEqual a c
    monotoneLeft : ∀ prefix {a b} →
      LessEqual a b → LessEqual (multiply prefix a) (multiply prefix b)

    associative : ∀ a b c →
      multiply (multiply a b) c ≡ multiply a (multiply b c)
    identityLeft : ∀ a → multiply one a ≡ a
    commutative : ∀ a b → multiply a b ≡ multiply b a

open OrderedCommutativeMonoid public

record WeightedKernelData (Site Bound : Set)
    (order : OrderedCommutativeMonoid Bound) : Set₁ where
  field
    distance : Site → Site → Bound
    absoluteKernel : Site → Site → Bound
    weight decay : Bound → Bound → Bound

    weightDecayInverse : ∀ mu d →
      multiply order (decay mu d) (weight mu d) ≡ one order

open WeightedKernelData public

unweightProduct :
  ∀ {Bound : Set} →
  (order : OrderedCommutativeMonoid Bound) →
  ∀ decayFactor weightFactor value →
  multiply order decayFactor weightFactor ≡ one order →
  multiply order decayFactor (multiply order weightFactor value) ≡ value
unweightProduct order decayFactor weightFactor value inverseLaw =
  trans
    (sym (associative order decayFactor weightFactor value))
    (trans
      (cong (λ factor → multiply order factor value) inverseLaw)
      (identityLeft order value))

weightedColumnToPointwiseDecay :
  ∀ {Site Bound : Set} →
  (order : OrderedCommutativeMonoid Bound) →
  (kernel : WeightedKernelData Site Bound order) →
  (mu constant : Bound) →
  (∀ x y →
    LessEqual order
      (multiply order
        (weight kernel mu (distance kernel x y))
        (absoluteKernel kernel x y))
      constant) →
  ∀ x y →
  LessEqual order
    (absoluteKernel kernel x y)
    (multiply order constant (decay kernel mu (distance kernel x y)))
weightedColumnToPointwiseDecay order kernel mu constant weighted x y =
  let d = distance kernel x y
      w = weight kernel mu d
      e = decay kernel mu d
      value = absoluteKernel kernel x y
      multiplied = monotoneLeft order e (weighted x y)
      unweighted = unweightProduct order e w value
        (weightDecayInverse kernel mu d)
      leftRewritten = subst
        (λ left → LessEqual order left (multiply order e constant))
        unweighted
        multiplied
  in
  subst
    (λ right → LessEqual order value right)
    (commutative order e constant)
    leftRewritten
