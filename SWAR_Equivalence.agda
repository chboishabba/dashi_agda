module SWAR_Equivalence where

open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Relation.Binary.PropositionalEquality as Eq using (cong; sym; trans)
open import Data.Vec using (Vec; []; _∷_; map; zipWith)
open import Data.Nat.Properties as NatP using ()
open import UFTC_Lattice using (Code; C_XOR)

------------------------------------------------------------------------
-- Lane-wise reference operation:
laneXOR : ∀ {n} → Vec Code n → Vec Code n → Vec Code n
laneXOR = zipWith C_XOR

------------------------------------------------------------------------
-- Abstract packed SWAR representation + pack/unpack:
postulate
  Packed : Nat → Set
  pack   : ∀ {n} → Vec Code n → Packed n
  unpack : ∀ {n} → Packed n → Vec Code n

-- Packed operation (your SWAR fast-path):
postulate
  swarXOR : ∀ {n} → Packed n → Packed n → Packed n

------------------------------------------------------------------------
-- The *only* thing you need to trust SWAR: a bisimulation/refinement law.

record SWARCorrect : Set₁ where
  field
    -- pack/unpack are section/retraction on the domain you care about
    unpack-pack : ∀ {n} (v : Vec Code n) → unpack (pack v) ≡ v

    -- swarXOR refines laneXOR through unpack
    swar-sound :
      ∀ {n} (x y : Packed n) →
        unpack (swarXOR x y) ≡ laneXOR (unpack x) (unpack y)

-- Derived: swarXOR correct on packed values built from vectors
swar-correct-on-packed :
  (C : SWARCorrect) →
  ∀ {n} (vx vy : Vec Code n) →
    unpack (swarXOR (pack vx) (pack vy)) ≡ laneXOR vx vy
swar-correct-on-packed C vx vy =
  let open SWARCorrect C in
  trans (swar-sound (pack vx) (pack vy))
        (cong (λ a → laneXOR a vy) (unpack-pack vx))
  -- note: second rewrite for vy is not needed because vy is not under unpack
