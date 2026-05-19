module DASHI.Arithmetic.NormalizeAddState where

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Nat using (Nat; zero)
open import Data.Nat using (_≤_)
open import Data.Product using (_×_; _,_)
open import Ontology.GodelLattice using (Vec15)

record NormalizeAddState : Set where
  constructor mkNormalizeAddState
  field
    prime : Nat
    lhs : Nat
    rhs : Nat
    residueDepth : Nat
    carryDepth : Nat
    padicDepth : Nat
    carryBudget : Nat
    carryTrace : Nat
    primeProfile : Vec15 Nat

open NormalizeAddState public

-- p-adic agreement surface for the first landing.
padicAgreement :
  NormalizeAddState →
  NormalizeAddState →
  Nat →
  Set
padicAgreement x y k =
  (prime x ≡ prime y) ×
  (padicDepth x ≡ padicDepth y) ×
  (k ≤ padicDepth x) ×
  (k ≤ padicDepth y)

carryResolved : NormalizeAddState → Set
carryResolved s = (carryDepth s ≡ zero) × (carryTrace s ≡ zero)

normalizeAddCanonical : NormalizeAddState → Set
normalizeAddCanonical s =
  (residueDepth s ≡ padicDepth s) ×
  (carryDepth s ≡ zero) ×
  (carryBudget s ≡ zero) ×
  (carryTrace s ≡ zero)
