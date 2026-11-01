module DASHI.Crypto.MLKEMNTTLocalPriorCouplingExact where

------------------------------------------------------------------------
-- ML-KEM NTT: LOCAL MULTIPLICATION != INDEPENDENT SECRET SEARCH
--
-- National Institute of Standards and Technology,
-- "Module-Lattice-Based Key-Encapsulation Mechanism Standard",
-- FIPS 203, 2024. DOI: 10.6028/NIST.FIPS.203.
--
-- FIPS 203 factors X^256+1 into 128 quadratic factors over Z_q. Multiplication
-- in T_q is independent across those 128 degree-one residue coordinates.
-- However K-PKE samples s,e from a small-coefficient distribution in R_q
-- before applying the NTT. Therefore local NTT algebra does not by itself
-- prove that the prior/smallness predicate factors into independent NTT lanes.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; _*_)
open import Data.Empty using (⊥)
open import Data.Product using (_×_; _,_)

nttQuadraticCoordinateCount : Nat
nttQuadraticCoordinateCount = 128

coefficientsPerNTTCoordinate : Nat
coefficientsPerNTTCoordinate = 2

nttArrayCoefficientCount : Nat
nttArrayCoefficientCount =
  nttQuadraticCoordinateCount * coefficientsPerNTTCoordinate

nttArrayCoefficientCountIs256 : nttArrayCoefficientCount ≡ 256
nttArrayCoefficientCountIs256 = refl

record ExactPriorTransform : Set₁ where
  constructor exactPriorTransform
  field
    Source Target : Set
    encode : Source → Target
    decode : Target → Source
    decodeEncode : ∀ source → decode (encode source) ≡ source
    encodeDecode : ∀ target → encode (decode target) ≡ target
    SourcePrior : Source → Set

open ExactPriorTransform public

TargetPrior : (transform : ExactPriorTransform) → Target transform → Set
TargetPrior transform target = SourcePrior transform (decode transform target)

sourcePriorTransportedExactly :
  ∀ (transform : ExactPriorTransform) source →
  SourcePrior transform source →
  TargetPrior transform (encode transform source)
sourcePriorTransportedExactly transform source prior
  rewrite decodeEncode transform source = prior

record TwoTargetLocalPriorFactorisation
    (transform : ExactPriorTransform) : Set₁ where
  constructor twoTargetLocalPriorFactorisation
  field
    Local₀ Local₁ : Set
    local₀ : Target transform → Local₀
    local₁ : Target transform → Local₁
    Prior₀ : Local₀ → Set
    Prior₁ : Local₁ → Set
    Reconcile : Local₀ → Local₁ → Set
    factors : ∀ target →
      TargetPrior transform target →
      Prior₀ (local₀ target) ×
      (Prior₁ (local₁ target) × Reconcile (local₀ target) (local₁ target))

open TwoTargetLocalPriorFactorisation public

record BitPair : Set where
  constructor bitPair
  field
    left right : Bool
open BitPair public

data EqualBits : Bool → Bool → Set where
  eqFalse : EqualBits false false
  eqTrue : EqualBits true true

bitPrior : BitPair → Set
bitPrior pair = EqualBits (left pair) (right pair)

identityPriorTransform : ExactPriorTransform
identityPriorTransform =
  exactPriorTransform BitPair BitPair
    (λ x → x) (λ x → x) (λ x → refl) (λ x → refl) bitPrior

Always : Bool → Set
Always b = b ≡ b

bitTargetFactorisation : TwoTargetLocalPriorFactorisation identityPriorTransform
bitTargetFactorisation =
  twoTargetLocalPriorFactorisation
    Bool Bool left right Always Always EqualBits proof
  where
  proof : ∀ target →
    TargetPrior identityPriorTransform target →
    Always (left target) ×
    (Always (right target) × EqualBits (left target) (right target))
  proof target prior = refl , (refl , prior)

crossedLocalsEachPass : Always false × Always true
crossedLocalsEachPass = refl , refl

crossedLocalsFailReconciliation : EqualBits false true → ⊥
crossedLocalsFailReconciliation ()

record NTTSearchBoundary : Set where
  constructor nttSearchBoundary
  field
    multiplicationLocalAcross128Coordinates : Bool
    multiplicationLocalAcross128CoordinatesIsTrue :
      multiplicationLocalAcross128Coordinates ≡ true
    nttIsInvertibleRepresentationChange : Bool
    nttIsInvertibleRepresentationChangeIsTrue :
      nttIsInvertibleRepresentationChange ≡ true
    cbdPriorProvedIndependentAcrossNTTCoordinates : Bool
    cbdPriorProvedIndependentAcrossNTTCoordinatesIsFalse :
      cbdPriorProvedIndependentAcrossNTTCoordinates ≡ false
    localAlgebraAloneCollapsesSearch : Bool
    localAlgebraAloneCollapsesSearchIsFalse :
      localAlgebraAloneCollapsesSearch ≡ false

open NTTSearchBoundary public

canonicalNTTSearchBoundary : NTTSearchBoundary
canonicalNTTSearchBoundary =
  nttSearchBoundary true refl true refl false refl false refl
