module DASHI.Physics.SignedPerm4 where

open import Data.Vec using (Vec; []; _∷_)
open import Data.Bool using (Bool)
open import Data.List using (List; _∷_; [])

data Perm3 : Set where
  p012 : Perm3
  p021 : Perm3
  p102 : Perm3
  p120 : Perm3
  p201 : Perm3
  p210 : Perm3

permute3 : ∀ {A : Set} → Perm3 → Vec A 3 → Vec A 3
permute3 p (a ∷ b ∷ c ∷ []) with p
... | p012 = a ∷ b ∷ c ∷ []
... | p021 = a ∷ c ∷ b ∷ []
... | p102 = b ∷ a ∷ c ∷ []
... | p120 = b ∷ c ∷ a ∷ []
... | p201 = c ∷ a ∷ b ∷ []
... | p210 = c ∷ b ∷ a ∷ []

allPerm3 : List Perm3
allPerm3 = p012 ∷ p021 ∷ p102 ∷ p120 ∷ p201 ∷ p210 ∷ []

record SignedPerm4 : Set where
  field
    perm  : Perm3
    flipT : Bool
    flipS : Vec Bool 3
