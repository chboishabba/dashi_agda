module DASHI.PDA_MDL.PDA where

open import DASHI.PDA_MDL.Prelude

record PDA (World Obs : Set) : Set₁ where
  field
    observe : World → Obs
    admissible : World → Set   -- witness/guard: which worlds are in scope
    costPDA : CodeLength       -- price the lens/witness (anti-cheat)

-- Apply PDA to a dataset (list of worlds)
WorldDataset : Set → Set
WorldDataset W = List W

ObsDataset : Set → Set
ObsDataset O = List O

map : ∀ {A B} → (A → B) → List A → List B
map f []       = []
map f (x ∷ xs) = f x ∷ map f xs

observeAll : ∀ {W O} → PDA W O → WorldDataset W → ObsDataset O
observeAll P D = map (PDA.observe P) D
