module DASHI.Moonshine.ClassicalHeckeWeightKSmallWordExact where

------------------------------------------------------------------------
-- PRIMARY SOURCES / CONTEXT
--
-- Toshitsune Miyake,
-- "Modular Forms", Springer Monographs in Mathematics, Springer, 2006.
-- DOI: 10.1007/3-540-29593-3.
--
-- Jean-Pierre Serre,
-- "A Course in Arithmetic", Graduate Texts in Mathematics 7,
-- Springer, 1973.
-- DOI: 10.1007/978-1-4684-9884-4.
--
-- DASHI CONTRIBUTION
--
-- Implement the classical normalized Hecke divisor-sum product as an
-- executable formal-expression normalizer:
--
--   T_m T_n = sum_{d | gcd(m,n)} d^(k-1) T_(mn/d^2).
--
-- Common divisors are computed, not supplied as a certificate.  The small
-- words used by the Aristotle development therefore normalize by reduction:
--
--   T2 T3      = T6
--   T2^2       = T4 + 2^(k-1) T1
--   T3^2       = T9 + 3^(k-1) T1
--   T2 T3 T2   = T12 + 2^(k-1) T3
--
-- and at weight 12
--
--   T3^3       = T27 + 2*3^11 T3.
--
-- This is a formal Hecke-expression algebra.  Identifying an existing DASHI
-- correspondence representation with these operators remains an intertwiner
-- theorem, not a naming convention.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_; _*_)
open import Data.List.Base using (List; []; _∷_; _++_; filter; map)
open import Data.Nat using (_/_)
open import Data.Nat.Divisibility using (_∣?_) 
open import Data.Nat.Properties renaming (_≟_ to nat≟)
open import Relation.Nullary.Decidable.Core using (_×?_; yes; no)

powNat : Nat → Nat → Nat
powNat base zero = 1
powNat base (suc exponent) = base * powNat base exponent

oneTo : Nat → List Nat
oneTo zero = []
oneTo (suc n) = oneTo n ++ (suc n ∷ [])

commonDivisors : Nat → Nat → List Nat
commonDivisors m n =
  filter
    (λ d → (d ∣? m) ×? (d ∣? n))
    (oneTo m)

record HeckeTerm : Set where
  constructor heckeTerm
  field
    coefficient : Nat
    index : Nat

open HeckeTerm public

HeckeExpression : Set
HeckeExpression = List HeckeTerm

termForDivisor :
  Nat → Nat → Nat → Nat → HeckeTerm
termForDivisor weightMinusOne m n d =
  heckeTerm
    (powNat d weightMinusOne)
    ((m * n) / (d * d))

heckeProductExpression :
  Nat → Nat → Nat → HeckeExpression
heckeProductExpression weightMinusOne m n =
  map
    (termForDivisor weightMinusOne m n)
    (commonDivisors m n)

------------------------------------------------------------------------
-- Closed divisor-sum computations.
------------------------------------------------------------------------

hecke23AnyWeight :
  (weightMinusOne : Nat) →
  heckeProductExpression weightMinusOne 2 3
  ≡ heckeTerm 1 6 ∷ []
hecke23AnyWeight weightMinusOne = refl

hecke22AnyWeight :
  (weightMinusOne : Nat) →
  heckeProductExpression weightMinusOne 2 2
  ≡ heckeTerm 1 4
      ∷ heckeTerm (powNat 2 weightMinusOne) 1
      ∷ []
hecke22AnyWeight weightMinusOne = refl

hecke33AnyWeight :
  (weightMinusOne : Nat) →
  heckeProductExpression weightMinusOne 3 3
  ≡ heckeTerm 1 9
      ∷ heckeTerm (powNat 3 weightMinusOne) 1
      ∷ []
hecke33AnyWeight weightMinusOne = refl

hecke62AnyWeight :
  (weightMinusOne : Nat) →
  heckeProductExpression weightMinusOne 6 2
  ≡ heckeTerm 1 12
      ∷ heckeTerm (powNat 2 weightMinusOne) 3
      ∷ []
hecke62AnyWeight weightMinusOne = refl

hecke93AnyWeight :
  (weightMinusOne : Nat) →
  heckeProductExpression weightMinusOne 9 3
  ≡ heckeTerm 1 27
      ∷ heckeTerm (powNat 3 weightMinusOne) 3
      ∷ []
hecke93AnyWeight weightMinusOne = refl

------------------------------------------------------------------------
-- Linear extension and adjacent-like-term normalization.
------------------------------------------------------------------------

scaleTerm : Nat → HeckeTerm → HeckeTerm
scaleTerm scalar (heckeTerm c i) = heckeTerm (scalar * c) i

scaleExpression : Nat → HeckeExpression → HeckeExpression
scaleExpression scalar expression = map (scaleTerm scalar) expression

multiplyBasisByExpression :
  Nat → Nat → HeckeExpression → HeckeExpression
multiplyBasisByExpression weightMinusOne m [] = []
multiplyBasisByExpression weightMinusOne m (heckeTerm c n ∷ rest) =
  scaleExpression c (heckeProductExpression weightMinusOne m n)
  ++ multiplyBasisByExpression weightMinusOne m rest

combineAdjacentLikeTerms : HeckeExpression → HeckeExpression
combineAdjacentLikeTerms [] = []
combineAdjacentLikeTerms (term ∷ []) = term ∷ []
combineAdjacentLikeTerms
  (heckeTerm c i ∷ heckeTerm d j ∷ rest)
  with nat≟ i j
... | yes refl =
  combineAdjacentLikeTerms (heckeTerm (c + d) i ∷ rest)
... | no _ =
  heckeTerm c i
    ∷ combineAdjacentLikeTerms (heckeTerm d j ∷ rest)

------------------------------------------------------------------------
-- Word normal forms.
------------------------------------------------------------------------

hecke232 : Nat → HeckeExpression
hecke232 weightMinusOne =
  combineAdjacentLikeTerms
    (multiplyBasisByExpression
      weightMinusOne 2
      (heckeProductExpression weightMinusOne 3 2))

hecke232NormalForm :
  (weightMinusOne : Nat) →
  hecke232 weightMinusOne
  ≡ heckeTerm 1 12
      ∷ heckeTerm (powNat 2 weightMinusOne) 3
      ∷ []
hecke232NormalForm weightMinusOne = refl

hecke333Weight12 : HeckeExpression
hecke333Weight12 =
  combineAdjacentLikeTerms
    (multiplyBasisByExpression
      11 3
      (heckeProductExpression 11 3 3))

hecke333Weight12NormalForm :
  hecke333Weight12
  ≡ heckeTerm 1 27
      ∷ heckeTerm 354294 3
      ∷ []
hecke333Weight12NormalForm = refl

weight12TwoCorrection : powNat 2 11 ≡ 2048
weight12TwoCorrection = refl

weight12ThreeCorrection : powNat 3 11 ≡ 177147
weight12ThreeCorrection = refl
