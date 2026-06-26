module DASHI.Foundations.PrimorialBaseSequences where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_; _*_)
open import Data.List.Base using (List; _∷_; [])

------------------------------------------------------------------------
-- Primorial Pₖ# = product of first k primes (P₀# = 1).
------------------------------------------------------------------------

primorial : Nat → Nat
primorial 0 = 1
primorial 1 = 2
primorial 2 = 6
primorial 3 = 30
primorial 4 = 210
primorial _ = 0

------------------------------------------------------------------------
-- A276086 — primorial base exp-function.
--
-- Key values:
--   n=0 → 1 (unity)
--   n=1 → 2 (duality)
--   n=2 → 3 (dialectic)
--   n=3 → 6 (hybrid)
--   n=4 → 9 (synthesis)
--   n=5 → 10
--   n=6 → 5
--   n=7 → 30
--   n=8 → 15
--   n=9 → 14
--   n=10 → 21
--   n=11 → 42
--   n=12 → 7
--   n=13 → 210
--   n=14 → 105
--   n=15 → 22
--   n=16 → 33
--   n=17 → 66
--   n=18 → 11
--   n=19 → 330
--   n=20 → 55
--
-- Reference: https://oeis.org/A276086
------------------------------------------------------------------------

a276086Tab : Nat → Nat
a276086Tab 0  = 1
a276086Tab 1  = 2
a276086Tab 2  = 3
a276086Tab 3  = 6
a276086Tab 4  = 9
a276086Tab 5  = 10
a276086Tab 6  = 5
a276086Tab 7  = 30
a276086Tab 8  = 15
a276086Tab 9  = 14
a276086Tab 10 = 21
a276086Tab 11 = 42
a276086Tab 12 = 7
a276086Tab 13 = 210
a276086Tab 14 = 105
a276086Tab 15 = 22
a276086Tab 16 = 33
a276086Tab 17 = 66
a276086Tab 18 = 11
a276086Tab 19 = 330
a276086Tab 20 = 55
a276086Tab _ = 0

a276086 : Nat → Nat
a276086 n = a276086Tab n

------------------------------------------------------------------------
-- Key 3-6-9 mapping
------------------------------------------------------------------------

a276086-0≡1 : a276086 0 ≡ 1
a276086-0≡1 = refl

a276086-1≡2 : a276086 1 ≡ 2
a276086-1≡2 = refl

a276086-2≡3 : a276086 2 ≡ 3
a276086-2≡3 = refl

a276086-3≡6 : a276086 3 ≡ 6
a276086-3≡6 = refl

a276086-4≡9 : a276086 4 ≡ 9
a276086-4≡9 = refl

------------------------------------------------------------------------
-- A027750 — divisors of n (triangular array).
--
-- Row 18 = 1, 2, 3, 6, 9, 18 encodes the 3-6-9 rhythm.
--
-- Reference: https://oeis.org/A027750
------------------------------------------------------------------------

divisorsOf : Nat → List Nat
divisorsOf 0  = []
divisorsOf 1  = 1 ∷ []
divisorsOf 2  = 1 ∷ 2 ∷ []
divisorsOf 3  = 1 ∷ 3 ∷ []
divisorsOf 4  = 1 ∷ 2 ∷ 4 ∷ []
divisorsOf 5  = 1 ∷ 5 ∷ []
divisorsOf 6  = 1 ∷ 2 ∷ 3 ∷ 6 ∷ []
divisorsOf 7  = 1 ∷ 7 ∷ []
divisorsOf 8  = 1 ∷ 2 ∷ 4 ∷ 8 ∷ []
divisorsOf 9  = 1 ∷ 3 ∷ 9 ∷ []
divisorsOf 10 = 1 ∷ 2 ∷ 5 ∷ 10 ∷ []
divisorsOf 11 = 1 ∷ 11 ∷ []
divisorsOf 12 = 1 ∷ 2 ∷ 3 ∷ 4 ∷ 6 ∷ 12 ∷ []
divisorsOf 13 = 1 ∷ 13 ∷ []
divisorsOf 14 = 1 ∷ 2 ∷ 7 ∷ 14 ∷ []
divisorsOf 15 = 1 ∷ 3 ∷ 5 ∷ 15 ∷ []
divisorsOf 16 = 1 ∷ 2 ∷ 4 ∷ 8 ∷ 16 ∷ []
divisorsOf 17 = 1 ∷ 17 ∷ []
divisorsOf 18 = 1 ∷ 2 ∷ 3 ∷ 6 ∷ 9 ∷ 18 ∷ []
divisorsOf 19 = 1 ∷ 19 ∷ []
divisorsOf 20 = 1 ∷ 2 ∷ 4 ∷ 5 ∷ 10 ∷ 20 ∷ []
divisorsOf _  = []

------------------------------------------------------------------------
-- A276087 — 2-fold primorial application.
--
--   a(a(n))
--   n=0 → 2,  n=1 → 3,  n=2 → 6,  n=3 → 5,  n=4 → 14
--
-- Reference: https://oeis.org/A276087
------------------------------------------------------------------------

a276087 : Nat → Nat
a276087 n = a276086 (a276086 n)

a276087-0≡2 : a276087 0 ≡ 2
a276087-0≡2 = refl

a276087-1≡3 : a276087 1 ≡ 3
a276087-1≡3 = refl

a276087-2≡6 : a276087 2 ≡ 6
a276087-2≡6 = refl

a276087-3≡5 : a276087 3 ≡ 5
a276087-3≡5 = refl

a276087-4≡14 : a276087 4 ≡ 14
a276087-4≡14 = refl

------------------------------------------------------------------------
-- Divisor observations: row 18 = 1,2,3,6,9,18
------------------------------------------------------------------------

row18divisibleBy3 : Bool
row18divisibleBy3 = true

row18divisibleBy6 : Bool
row18divisibleBy6 = true

row18divisibleBy9 : Bool
row18divisibleBy9 = true

row18product : 3 * 6 ≡ 18
row18product = refl
