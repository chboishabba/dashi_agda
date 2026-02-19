module DASHI.Combinatorics.PDA_MDL.CICADA71 where

open import DASHI.Combinatorics.PDA_MDL.Prelude
open import DASHI.Combinatorics.PDA_MDL.ExponentVector

open import Data.Fin using (Fin; toℕ; fromℕ<)
open import Data.Nat.DivMod using (m%n<n)
open import Data.Vec using (Vec; zipWith; foldr′)

mod71 : Nat → Nat
mod71 n = n % 71

-- Interpret a Fin 71 as Nat in [0..70]
fin71→Nat : Fin 71 → Nat
fin71→Nat = toℕ

-- A fixed weight vector in Fin 71 (choose anything deterministic).
-- You can later pick these as (prime mod 71) or derived from the 15 primes.
postulate w : Vec (Fin 71) 15

dotNat : EV → Vec (Fin 71) 15 → Nat
dotNat ev ws =
  foldr′ _+_ zero (zipWith (λ e wi → e * fin71→Nat wi) ev ws)

bucket71-ev : EV → Fin 71
bucket71-ev ev =
  -- convert (dot mod 71) into Fin 71
  fromℕ< (m%n<n (dotNat ev w) 71)
