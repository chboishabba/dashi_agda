-- Agda: 10-Fold Way Bridges
module TenfoldBridges where

open import Data.Nat using (ℕ)
open import Data.Nat.DivMod using (_%_)
open import Data.Bool
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; _≢_)

-- Topological class
topoClass : ℕ → ℕ
topoClass n = n % 10

-- Bridge record
record Bridge : Set where
  field
    nodeA : ℕ
    nodeB : ℕ
    different : topoClass nodeA ≢ topoClass nodeB

-- Symmetry
bridge-sym : (b : Bridge) → Bridge
bridge-sym record { nodeA = a ; nodeB = b ; different = d } =
  record { nodeA = b ; nodeB = a ; different = λ eq → d (sym eq) }

-- Example: 232 ↔ 323
bridge-232-323 : Bridge
bridge-232-323 = record
  { nodeA = 232
  ; nodeB = 323
  ; different = λ ()
  }

-- Theorem: Symmetry preserves bridges
bridge-symmetry : (b : Bridge) → 
  Bridge.nodeA (bridge-sym b) ≡ Bridge.nodeB b
bridge-symmetry b = refl
