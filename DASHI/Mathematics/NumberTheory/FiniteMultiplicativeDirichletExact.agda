module DASHI.Mathematics.NumberTheory.FiniteMultiplicativeDirichletExact where

------------------------------------------------------------------------
-- PRIMARY SOURCES / CONTEXT
--
-- Jean-Pierre Serre,
-- "A Course in Arithmetic".
-- DOI: 10.1007/978-1-4684-9884-4.
--
-- Toshitsune Miyake,
-- "Modular Forms".
-- DOI: 10.1007/3-540-29593-3.
--
-- DASHI CONTRIBUTION
--
-- Add the finite Dirichlet-monomial layer beneath Euler products.  A formal
-- prime-power factor carries a natural prime label, a natural exponent, a
-- local coefficient and a local analytic weight.  Coefficients, weights and
-- their Dirichlet monomial are products over a factorisation list.
-- Concatenating disjoint prime supports multiplies all three quantities
-- exactly.
--
-- This is the finite algebraic content of
--
--   a_mn = a_m a_n  and  (mn)^(-s)=m^(-s)n^(-s)
--
-- for coprime factorisations.  Unique factorisation, actual powers n^(-s),
-- convergence and infinite Dirichlet series remain separate realizations.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat)

import DASHI.Mathematics.NumberTheory.FiniteEulerProductExact as Euler

record FormalPrimePower
    (semiring : Euler.CommutativeSemiring) : Set where
  constructor primePowerFactor
  field
    prime : Nat
    exponent : Nat
    localCoefficient : Euler.Carrier semiring
    localWeight : Euler.Carrier semiring

open FormalPrimePower public

Factorisation : Euler.CommutativeSemiring → Set
Factorisation semiring = List (FormalPrimePower semiring)

mapList : ∀ {A B : Set} → (A → B) → List A → List B
mapList f [] = []
mapList f (x ∷ xs) = f x ∷ mapList f xs

coefficientOf : ∀ semiring → Factorisation semiring → Euler.Carrier semiring
coefficientOf semiring factorisation =
  Euler.productList semiring
    (mapList localCoefficient factorisation)

weightOf : ∀ semiring → Factorisation semiring → Euler.Carrier semiring
weightOf semiring factorisation =
  Euler.productList semiring
    (mapList localWeight factorisation)

dirichletMonomial :
  ∀ semiring → Factorisation semiring → Euler.Carrier semiring
dirichletMonomial semiring factorisation =
  Euler.multiply semiring
    (coefficientOf semiring factorisation)
    (weightOf semiring factorisation)

mapAppend : ∀ {A B : Set} (f : A → B) xs ys →
  mapList f (Euler.append xs ys)
  ≡ Euler.append (mapList f xs) (mapList f ys)
mapAppend f [] ys = refl
mapAppend f (x ∷ xs) ys
    with mapAppend f xs ys
... | refl = refl

coefficientOfAppend : ∀ semiring left right →
  coefficientOf semiring (Euler.append left right)
  ≡ Euler.multiply semiring
      (coefficientOf semiring left)
      (coefficientOf semiring right)
coefficientOfAppend semiring left right =
  transitivity
    (congruence (Euler.productList semiring)
      (mapAppend localCoefficient left right))
    (Euler.productAppend semiring
      (mapList localCoefficient left)
      (mapList localCoefficient right))
  where
    transitivity : ∀ {A : Set} {x y z : A} →
      x ≡ y → y ≡ z → x ≡ z
    transitivity refl second = second

    congruence : ∀ {A B : Set} (f : A → B) {x y} →
      x ≡ y → f x ≡ f y
    congruence f refl = refl

weightOfAppend : ∀ semiring left right →
  weightOf semiring (Euler.append left right)
  ≡ Euler.multiply semiring
      (weightOf semiring left)
      (weightOf semiring right)
weightOfAppend semiring left right =
  transitivity
    (congruence (Euler.productList semiring)
      (mapAppend localWeight left right))
    (Euler.productAppend semiring
      (mapList localWeight left)
      (mapList localWeight right))
  where
    transitivity : ∀ {A : Set} {x y z : A} →
      x ≡ y → y ≡ z → x ≡ z
    transitivity refl second = second

    congruence : ∀ {A B : Set} (f : A → B) {x y} →
      x ≡ y → f x ≡ f y
    congruence f refl = refl

monomialOfAppend : ∀ semiring left right →
  dirichletMonomial semiring (Euler.append left right)
  ≡ Euler.multiply semiring
      (dirichletMonomial semiring left)
      (dirichletMonomial semiring right)
monomialOfAppend semiring left right =
  transitivity
    (congruence₂ (Euler.multiply semiring)
      (coefficientOfAppend semiring left right)
      (weightOfAppend semiring left right))
    (reassociateAndCommute
      (coefficientOf semiring left)
      (coefficientOf semiring right)
      (weightOf semiring left)
      (weightOf semiring right))
  where
    transitivity : ∀ {A : Set} {x y z : A} →
      x ≡ y → y ≡ z → x ≡ z
    transitivity refl second = second

    symmetry : ∀ {A : Set} {x y : A} → x ≡ y → y ≡ x
    symmetry refl = refl

    congruence : ∀ {A B : Set} (f : A → B) {x y} →
      x ≡ y → f x ≡ f y
    congruence f refl = refl

    congruence₂ : ∀ {A B C : Set} (f : A → B → C)
      {x x' : A} {y y' : B} →
      x ≡ x' → y ≡ y' → f x y ≡ f x' y'
    congruence₂ f refl refl = refl

    middleExchange : ∀ b c d →
      Euler.multiply semiring b (Euler.multiply semiring c d)
      ≡ Euler.multiply semiring c (Euler.multiply semiring b d)
    middleExchange b c d =
      transitivity
        (symmetry (Euler.multiplyAssociative semiring b c d))
        (transitivity
          (congruence
            (λ middle → Euler.multiply semiring middle d)
            (Euler.multiplyCommutative semiring b c))
          (Euler.multiplyAssociative semiring c b d))

    reassociateAndCommute : ∀ a b c d →
      Euler.multiply semiring
        (Euler.multiply semiring a b)
        (Euler.multiply semiring c d)
      ≡ Euler.multiply semiring
          (Euler.multiply semiring a c)
          (Euler.multiply semiring b d)
    reassociateAndCommute a b c d =
      transitivity
        (Euler.multiplyAssociative semiring a b
          (Euler.multiply semiring c d))
        (transitivity
          (congruence
            (Euler.multiply semiring a)
            (middleExchange b c d))
          (symmetry
            (Euler.multiplyAssociative semiring a c
              (Euler.multiply semiring b d))))

record CoprimeFactorisationPair
    (semiring : Euler.CommutativeSemiring)
    (left right : Factorisation semiring) : Set where
  field
    supportsDisjoint : Set

coprimeCoefficientMultiplicativity :
  ∀ semiring left right →
  CoprimeFactorisationPair semiring left right →
  coefficientOf semiring (Euler.append left right)
  ≡ Euler.multiply semiring
      (coefficientOf semiring left)
      (coefficientOf semiring right)
coprimeCoefficientMultiplicativity semiring left right disjoint =
  coefficientOfAppend semiring left right

coprimeDirichletMultiplicativity :
  ∀ semiring left right →
  CoprimeFactorisationPair semiring left right →
  dirichletMonomial semiring (Euler.append left right)
  ≡ Euler.multiply semiring
      (dirichletMonomial semiring left)
      (dirichletMonomial semiring right)
coprimeDirichletMultiplicativity semiring left right disjoint =
  monomialOfAppend semiring left right

finiteDirichletPolynomial :
  ∀ semiring → List (Factorisation semiring) → Euler.Carrier semiring
finiteDirichletPolynomial semiring factorisations =
  Euler.sumList semiring
    (mapList (dirichletMonomial semiring) factorisations)
