module DASHI.Geometry.UltrametricFP where

open import Agda.Primitive using (Level; lsuc)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Agda.Builtin.Sigma using (Σ; _,_)
open import Data.Empty using (⊥)
open import Data.Nat using (_≤_; _<_; _+_)
open import Data.Nat.Properties as NatP
open import Data.Product using (proj₁; proj₂)
open import Data.Bool using (Bool; true; false)
open import Data.Vec using (Vec; []; _∷_; replicate)
open import Relation.Binary.PropositionalEquality using (cong; sym; trans)
open import Relation.Nullary using (yes; no)

open import Ultrametric as UMetric
open import Contraction as Contr
open import DASHI.Geometry.BanachFixedPoint as BFP
open import DASHI.Geometry.CompleteUltrametric as CU
open import DASHI.Geometry.CompleteUltrametricNat as CUN
open import DASHI.Metric.AgreementUltrametric as AM
open import DASHI.Algebra.Trit using (Trit; zer; pos)

iterate : ∀ {A : Set} → (A → A) → Nat → A → A
iterate f zero    x = x
iterate f (suc n) x = iterate f n (f x)

record SeparatedUltrametric {S : Set} (U : UMetric.Ultrametric S) : Set₁ where
  field
    zero→eq : ∀ {x y : S} → UMetric.Ultrametric.d U x y ≡ zero → x ≡ y

open SeparatedUltrametric public

record SContraction {S : Set}
  (U : UMetric.Ultrametric S) (f : S → S) : Set₁ where
  field
    contractive≢ : Contr.Contractive≢ U f
    contractionFactor : Nat
    contractionFactorPositive : 0 < contractionFactor

open SContraction public

record PicardWitness {S : Set}
  (U : UMetric.Ultrametric S) (f : S → S) (x₀ : S) : Set₁ where
  field
    steps : Nat
    point : S
    reached : iterate f steps x₀ ≡ point
    stabilized : iterate f (suc steps) x₀ ≡ point

open PicardWitness public

record ConstructiveFixedPoint {S : Set}
  (U : UMetric.Ultrametric S) (f : S → S) : Set₁ where
  field
    fixedPoint : S
    fixed      : f fixedPoint ≡ fixedPoint
    unique     : ∀ x → f x ≡ x → x ≡ fixedPoint
    εWitness   : (x₀ : S) → Nat → PicardWitness U f x₀

open ConstructiveFixedPoint public

record SphericalCompleteLift {S : Set}
  (U : UMetric.Ultrametric S) : Set₁ where
  field
    complete : CU.Complete U
    sphericalCompleteness : Set

record CompletionLift {S : Set}
  (U : UMetric.Ultrametric S) : Set₁ where
  field
    Carrier̂ : Set
    embedding : S → Carrier̂
    completê : Set

record ValuationContractionWitness : Set where
  field
    prime : Nat
    exponent : Nat
    radiusDrop : Nat
    numericalFactor : Nat

postulate
  constructiveUltrametricBanach :
    ∀ {S : Set} →
    (U : UMetric.Ultrametric S) →
    SeparatedUltrametric U →
    CU.Complete U →
    (f : S → S) →
    SContraction U f →
    ConstructiveFixedPoint U f

  sphericalCompletionPreservesFP :
    ∀ {S : Set} →
    (U : UMetric.Ultrametric S) →
    SphericalCompleteLift U →
    (f : S → S) →
    SContraction U f →
    ConstructiveFixedPoint U f

  valuation⇒numericContraction :
    ValuationContractionWitness

constructiveBanachFixedPoint :
  ∀ {S : Set} →
  (U : UMetric.Ultrametric S) →
  SeparatedUltrametric U →
  CU.Complete U →
  (f : S → S) →
  SContraction U f →
  BFP.BanachFixedPoint U f
constructiveBanachFixedPoint U sep comp f sc =
  let witness = constructiveUltrametricBanach U sep comp f sc in
  record
    { fp = fixedPoint witness
    ; fixes = fixed witness
    ; unique = unique witness
    }

------------------------------------------------------------------------
-- Tiny p-adic-style harness on finite digit vectors.
-- The map x ↦ a + p x is modeled by shifting in a fixed leading digit.

dropLast : ∀ {A : Set} {n : Nat} → Vec A (suc n) → Vec A n
dropLast {n = zero} (x ∷ []) = []
dropLast {n = suc n} (x ∷ y ∷ xs) = x ∷ dropLast (y ∷ xs)

dropLast-cons :
  ∀ {A : Set} {n : Nat} (x : A) (xs : Vec A (suc n)) →
  dropLast (x ∷ xs) ≡ x ∷ dropLast xs
dropLast-cons x (y ∷ xs) = refl

dropLast-replicate :
  ∀ {A : Set} {n : Nat} (a : A) →
  dropLast (replicate (suc n) a) ≡ replicate n a
dropLast-replicate {n = zero} a = refl
dropLast-replicate {n = suc n} a =
  cong (a ∷_) (dropLast-replicate {n = n} a)

shiftIn : ∀ {n : Nat} → Trit → Vec Trit (suc n) → Vec Trit (suc n)
shiftIn a xs = a ∷ dropLast xs

headVec : ∀ {A : Set} {n : Nat} → Vec A (suc n) → A
headVec (x ∷ xs) = x

tailVec : ∀ {A : Set} {n : Nat} → Vec A (suc n) → Vec A n
tailVec (x ∷ xs) = xs

headFixed :
  ∀ {n : Nat} {a x : Trit} {xs : Vec Trit n} →
  shiftIn a (x ∷ xs) ≡ x ∷ xs →
  x ≡ a
headFixed eq = sym (cong headVec eq)

dropLastFixed :
  ∀ {n : Nat} {a x : Trit} {xs : Vec Trit (suc n)} →
  shiftIn a (x ∷ xs) ≡ x ∷ xs →
  dropLast (x ∷ xs) ≡ xs
dropLastFixed eq = cong tailVec eq

promoteTailFixed :
  ∀ {n : Nat} {a x : Trit} {xs : Vec Trit (suc n)} →
  x ≡ a →
  dropLast (x ∷ xs) ≡ xs →
  shiftIn a xs ≡ xs
promoteTailFixed {xs = xs} refl tailEq =
  trans (sym (dropLast-cons _ xs)) tailEq

shiftIn-fixed :
  ∀ {n : Nat} (a : Trit) →
  shiftIn a (replicate (suc n) a) ≡ replicate (suc n) a
shiftIn-fixed {n = n} a =
  cong (a ∷_) (dropLast-replicate {n = n} a)

shiftIn-unique-fixed :
  ∀ {n : Nat} (a : Trit) (xs : Vec Trit (suc n)) →
  shiftIn a xs ≡ xs →
  xs ≡ replicate (suc n) a
shiftIn-unique-fixed {zero} a (x ∷ []) eq
  rewrite headFixed eq = refl
shiftIn-unique-fixed {suc n} a (x ∷ xs@(y ∷ ys)) eq
  rewrite headFixed eq
        | shiftIn-unique-fixed a xs (promoteTailFixed (headFixed eq) (dropLastFixed eq))
  = refl

toyLength : Nat
toyLength = 4

ToyCarrier : Set
ToyCarrier = Vec Trit toyLength

toyU : UMetric.Ultrametric ToyCarrier
toyU = AM.ultrametricVec {n = toyLength}

toySeparated : SeparatedUltrametric toyU
toySeparated =
  record
    { zero→eq = λ {x} {y} → AM.dNat-zero→eq x y
    }

toyComplete : CU.Complete toyU
toyComplete = CUN.completeNatUltrametric toyU

toySeed : ToyCarrier
toySeed = replicate toyLength zer

toyFixedPoint : ToyCarrier
toyFixedPoint = replicate toyLength pos

toyStep : ToyCarrier → ToyCarrier
toyStep = shiftIn pos

toyStep-fixed : toyStep toyFixedPoint ≡ toyFixedPoint
toyStep-fixed = shiftIn-fixed pos

toyUnique :
  ∀ x →
  toyStep x ≡ x →
  x ≡ toyFixedPoint
toyUnique = shiftIn-unique-fixed pos

toy-step₁ : iterate toyStep 1 toySeed ≡ pos ∷ zer ∷ zer ∷ zer ∷ []
toy-step₁ = refl

toy-step₂ : iterate toyStep 2 toySeed ≡ pos ∷ pos ∷ zer ∷ zer ∷ []
toy-step₂ = refl

toy-step₃ : iterate toyStep 3 toySeed ≡ pos ∷ pos ∷ pos ∷ zer ∷ []
toy-step₃ = refl

toy-step₄ : iterate toyStep 4 toySeed ≡ toyFixedPoint
toy-step₄ = refl

toy-stabilized :
  iterate toyStep 5 toySeed ≡ toyFixedPoint
toy-stabilized = refl

toyDistanceAfter4 : UMetric.Ultrametric.d toyU (iterate toyStep 4 toySeed) toyFixedPoint ≡ 0
toyDistanceAfter4 = refl

toyDistanceAfter5 : UMetric.Ultrametric.d toyU (iterate toyStep 4 toySeed) (iterate toyStep 5 toySeed) ≡ 0
toyDistanceAfter5 = refl

toyWitness : PicardWitness toyU toyStep toySeed
toyWitness =
  record
    { steps = 4
    ; point = toyFixedPoint
    ; reached = toy-step₄
    ; stabilized = toy-stabilized
    }

toyBanachWitness : BFP.BanachFixedPoint toyU toyStep
toyBanachWitness =
  record
    { fp = toyFixedPoint
    ; fixes = toyStep-fixed
    ; unique = toyUnique
    }

ltᵇ : Nat → Nat → Bool
ltᵇ m n with m NatP.<? n
... | yes _ = true
... | no _  = false

toyConvergesWithin4? : Bool
toyConvergesWithin4? = true

toyUniqueFixedPoint? : Bool
toyUniqueFixedPoint? = true

toyεCertificate? : Bool
toyεCertificate? = ltᵇ (UMetric.Ultrametric.d toyU (iterate toyStep 4 toySeed) (iterate toyStep 5 toySeed)) 1
