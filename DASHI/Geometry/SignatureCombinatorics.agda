module DASHI.Geometry.SignatureCombinatorics where

open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Agda.Builtin.Equality using (_≡_)
open import Data.Empty using (⊥)
open import Data.Product using (_×_; _,_)

record Signature : Set where
  constructor sig
  field
    p : Nat
    q : Nat
    z : Nat

open Signature public

Nondegenerate : Signature → Set
Nondegenerate s = z s ≡ zero

Mixed : Signature → Set
Mixed s = (p s ≡ zero → ⊥) × (q s ≡ zero → ⊥)

UniqueNegative : Signature → Set
UniqueNegative s = q s ≡ suc zero

LorentzLike : Signature → Set
LorentzLike s = UniqueNegative s × Nondegenerate s

lorentzFromUniqueNegative :
  ∀ s → UniqueNegative s → Nondegenerate s → LorentzLike s
lorentzFromUniqueNegative s uq nz = uq , nz
