module DASHI.Physics.Holography.AreaLaw where

open import Data.Nat using (Nat; _≤_; _*_; _^_)

-- Minimal area/volume/entropy interface.
record RegionCounts : Set₁ where
  field
    Region : Set
    area   : Region → Nat
    volume : Region → Nat
    admCount : Region → Nat

open RegionCounts public

-- Area-law style bound: admissible count grows at most exponentially in boundary area.
AreaLaw : RegionCounts → Nat → Set
AreaLaw R K = ∀ r → admCount R r ≤ (K ^ area R r)

-- A simple UV finiteness predicate: bounded growth by an area-law constant.
record UVFinite (R : RegionCounts) : Set where
  field
    K : Nat
    areaLaw : AreaLaw R K

open UVFinite public
