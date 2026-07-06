module DASHI.Physics.YangMills.P10LargeFieldFiniteCertificate where

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat renaming (Nat to ℕ)
open import Data.List.Base using (length)
open import Data.Nat.Base using (_≤_; z≤n; s≤s; suc)

data _∈_ {A : Set} (x : A) : List A → Set where
  here : ∀ {xs} → x ∈ (x ∷ xs)
  there : ∀ {y xs} → x ∈ xs → x ∈ (y ∷ xs)

data InjectsInto {A : Set} : List A → List A → Set where
  inject-[] : ∀ {ys} → InjectsInto [] ys
  inject-keep :
    ∀ {x xs ys} →
    InjectsInto xs ys →
    InjectsInto (x ∷ xs) (x ∷ ys)
  inject-drop :
    ∀ {y xs ys} →
    InjectsInto xs ys →
    InjectsInto xs (y ∷ ys)

InjectsInto-refl : ∀ {A : Set} (xs : List A) → InjectsInto xs xs
InjectsInto-refl [] = inject-[]
InjectsInto-refl (x ∷ xs) = inject-keep (InjectsInto-refl xs)

≤-step : ∀ {a b} → a ≤ b → a ≤ suc b
≤-step z≤n = z≤n
≤-step (s≤s a≤b) = s≤s (≤-step a≤b)

≤-trans : ∀ {a b c} → a ≤ b → b ≤ c → a ≤ c
≤-trans z≤n _ = z≤n
≤-trans (s≤s a≤b) (s≤s b≤c) = s≤s (≤-trans a≤b b≤c)

≤-rewrite-right : ∀ {a b c} → a ≤ b → b ≡ c → a ≤ c
≤-rewrite-right a≤b refl = a≤b

sym : ∀ {A : Set} {x y : A} → x ≡ y → y ≡ x
sym refl = refl

InjectionLengthBound :
  ∀ {A : Set} →
  (xs ys : List A) →
  InjectsInto xs ys →
  length xs ≤ length ys
InjectionLengthBound [] ys inject-[] = z≤n
InjectionLengthBound (x ∷ xs) (x ∷ ys) (inject-keep inj) =
  s≤s (InjectionLengthBound xs ys inj)
InjectionLengthBound xs (y ∷ ys) (inject-drop inj) =
  ≤-step (InjectionLengthBound xs ys inj)

record ComplexityWitnessList (Block : Set) : Set where
  field
    carrier : List Block

record P10LargeFieldFiniteCertificate
  (Block : Set)
  (Polymer : Set)
  (BadBlock : ℕ → Block → Set)
  (LargeField : ℕ → Polymer → Set)
  (complexity : Polymer → ℕ)
  (countBadBlocks : ℕ → Polymer → ℕ)
  : Set₁ where
  field
    blocksOf :
      ℕ → Polymer → List Block

    badBlocksOf :
      ℕ → Polymer → List Block

    blockIsBad :
      ℕ → Polymer → Block → Bool

    badBlocksFilterSound :
      ∀ k X b →
      b ∈ badBlocksOf k X →
      BadBlock k b

    badBlocksFilterComplete :
      ∀ k X b →
      b ∈ blocksOf k X →
      blockIsBad k X b ≡ true →
      b ∈ badBlocksOf k X

    largeFieldHasBadBlockWitnesses :
      ∀ k X →
      LargeField k X →
      ComplexityWitnessList Block

    complexityWitnessesInjectInto :
      ∀ k X →
      (lf : LargeField k X) →
      InjectsInto
        (ComplexityWitnessList.carrier
          (largeFieldHasBadBlockWitnesses k X lf))
        (badBlocksOf k X)

    complexityCountMatchesWitnesses :
      ∀ k X →
      (lf : LargeField k X) →
      complexity X ≤
      length
        (ComplexityWitnessList.carrier
          (largeFieldHasBadBlockWitnesses k X lf))

    countBadBlocksMatchesList :
      ∀ k X →
      countBadBlocks k X ≡ length (badBlocksOf k X)

BadBlocksCoverComplexityFromFiniteCertificate :
  ∀
    {Block : Set}
    {Polymer : Set}
    {BadBlock : ℕ → Block → Set}
    {LargeField : ℕ → Polymer → Set}
    {complexity : Polymer → ℕ}
    {countBadBlocks : ℕ → Polymer → ℕ} →
  P10LargeFieldFiniteCertificate
    Block
    Polymer
    BadBlock
    LargeField
    complexity
    countBadBlocks
  → ∀ k X →
      LargeField k X →
      complexity X ≤ countBadBlocks k X
BadBlocksCoverComplexityFromFiniteCertificate cert k X lf =
  let witnesses =
        ComplexityWitnessList.carrier
          (P10LargeFieldFiniteCertificate.largeFieldHasBadBlockWitnesses cert k X lf)
      witnessBound =
        P10LargeFieldFiniteCertificate.complexityCountMatchesWitnesses
          cert k X lf
      injection =
        P10LargeFieldFiniteCertificate.complexityWitnessesInjectInto
          cert k X lf
      badCountEq =
        P10LargeFieldFiniteCertificate.countBadBlocksMatchesList cert k X
  in ≤-rewrite-right
       (≤-trans witnessBound
         (InjectionLengthBound
           witnesses
           (P10LargeFieldFiniteCertificate.badBlocksOf cert k X)
           injection))
       (sym badCountEq)
