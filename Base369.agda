module Base369 where

open import Agda.Builtin.Equality
open import Agda.Builtin.Nat
open import DASHI.Foundations.Base369Nat using (_%_; NonZero; nonZero)

------------------------------------------------------------------------
-- Utility: repeated rotation
------------------------------------------------------------------------

spin : {A : Set} → Nat → (A → A) → A → A
spin 0       rot x = x
spin (suc n) rot x = rot (spin n rot x)

------------------------------------------------------------------------
-- Truth values
------------------------------------------------------------------------

data TriTruth : Set where
  tri-low  : TriTruth
  tri-mid  : TriTruth
  tri-high : TriTruth

tri-index : TriTruth → Nat
tri-index tri-low  = 0
tri-index tri-mid  = 1
tri-index tri-high = 2

fromTriIndex : Nat → TriTruth
fromTriIndex n with n % 3
... | 0 = tri-low
... | 1 = tri-mid
... | _ = tri-high

rotateTri : TriTruth → TriTruth
rotateTri tri-low  = tri-mid
rotateTri tri-mid  = tri-high
rotateTri tri-high = tri-low

triXor-spin : TriTruth → TriTruth → TriTruth
triXor-spin carrier target = spin (tri-index carrier) rotateTri target

triXor-closed : TriTruth → TriTruth → TriTruth
triXor-closed carrier target = fromTriIndex (tri-index carrier + tri-index target)

triXor : TriTruth → TriTruth → TriTruth
triXor = triXor-closed

triXor-spin-correct : ∀ a b → triXor-spin a b ≡ triXor a b
triXor-spin-correct tri-low  tri-low  = refl
triXor-spin-correct tri-low  tri-mid  = refl
triXor-spin-correct tri-low  tri-high = refl
triXor-spin-correct tri-mid  tri-low  = refl
triXor-spin-correct tri-mid  tri-mid  = refl
triXor-spin-correct tri-mid  tri-high = refl
triXor-spin-correct tri-high tri-low  = refl
triXor-spin-correct tri-high tri-mid  = refl
triXor-spin-correct tri-high tri-high = refl

rotateTri³ : ∀ t → rotateTri (rotateTri (rotateTri t)) ≡ t
rotateTri³ tri-low  = refl
rotateTri³ tri-mid  = refl
rotateTri³ tri-high = refl

triXor-identityˡ : ∀ t → triXor tri-low t ≡ t
triXor-identityˡ tri-low  = refl
triXor-identityˡ tri-mid  = refl
triXor-identityˡ tri-high = refl

triXor-assoc : ∀ a b c → triXor a (triXor b c) ≡ triXor (triXor a b) c
triXor-assoc tri-low  tri-low  tri-low  = refl
triXor-assoc tri-low  tri-low  tri-mid  = refl
triXor-assoc tri-low  tri-low  tri-high = refl
triXor-assoc tri-low  tri-mid  tri-low  = refl
triXor-assoc tri-low  tri-mid  tri-mid  = refl
triXor-assoc tri-low  tri-mid  tri-high = refl
triXor-assoc tri-low  tri-high tri-low  = refl
triXor-assoc tri-low  tri-high tri-mid  = refl
triXor-assoc tri-low  tri-high tri-high = refl
triXor-assoc tri-mid  tri-low  tri-low  = refl
triXor-assoc tri-mid  tri-low  tri-mid  = refl
triXor-assoc tri-mid  tri-low  tri-high = refl
triXor-assoc tri-mid  tri-mid  tri-low  = refl
triXor-assoc tri-mid  tri-mid  tri-mid  = refl
triXor-assoc tri-mid  tri-mid  tri-high = refl
triXor-assoc tri-mid  tri-high tri-low  = refl
triXor-assoc tri-mid  tri-high tri-mid  = refl
triXor-assoc tri-mid  tri-high tri-high = refl
triXor-assoc tri-high tri-low  tri-low  = refl
triXor-assoc tri-high tri-low  tri-mid  = refl
triXor-assoc tri-high tri-low  tri-high = refl
triXor-assoc tri-high tri-mid  tri-low  = refl
triXor-assoc tri-high tri-mid  tri-mid  = refl
triXor-assoc tri-high tri-mid  tri-high = refl
triXor-assoc tri-high tri-high tri-low  = refl
triXor-assoc tri-high tri-high tri-mid  = refl
triXor-assoc tri-high tri-high tri-high = refl

------------------------------------------------------------------------

-- A hexadic universe: six “beats” that wrap around.

data HexTruth : Set where
  hex-0 hex-1 hex-2 hex-3 hex-4 hex-5 : HexTruth

hex-index : HexTruth → Nat
hex-index hex-0 = 0
hex-index hex-1 = 1
hex-index hex-2 = 2
hex-index hex-3 = 3
hex-index hex-4 = 4
hex-index hex-5 = 5

fromHexIndex : Nat → HexTruth
fromHexIndex n with n % 6
... | 0 = hex-0
... | 1 = hex-1
... | 2 = hex-2
... | 3 = hex-3
... | 4 = hex-4
... | _ = hex-5

rotateHex : HexTruth → HexTruth
rotateHex hex-0 = hex-1
rotateHex hex-1 = hex-2
rotateHex hex-2 = hex-3
rotateHex hex-3 = hex-4
rotateHex hex-4 = hex-5
rotateHex hex-5 = hex-0

hexXor-spin : HexTruth → HexTruth → HexTruth
hexXor-spin carrier target = spin (hex-index carrier) rotateHex target

hexXor-closed : HexTruth → HexTruth → HexTruth
hexXor-closed carrier target = fromHexIndex (hex-index carrier + hex-index target)

hexXor : HexTruth → HexTruth → HexTruth
hexXor = hexXor-closed

hexXor-spin-correct : ∀ a b → hexXor-spin a b ≡ hexXor a b
hexXor-spin-correct hex-0 hex-0 = refl
hexXor-spin-correct hex-0 hex-1 = refl
hexXor-spin-correct hex-0 hex-2 = refl
hexXor-spin-correct hex-0 hex-3 = refl
hexXor-spin-correct hex-0 hex-4 = refl
hexXor-spin-correct hex-0 hex-5 = refl
hexXor-spin-correct hex-1 hex-0 = refl
hexXor-spin-correct hex-1 hex-1 = refl
hexXor-spin-correct hex-1 hex-2 = refl
hexXor-spin-correct hex-1 hex-3 = refl
hexXor-spin-correct hex-1 hex-4 = refl
hexXor-spin-correct hex-1 hex-5 = refl
hexXor-spin-correct hex-2 hex-0 = refl
hexXor-spin-correct hex-2 hex-1 = refl
hexXor-spin-correct hex-2 hex-2 = refl
hexXor-spin-correct hex-2 hex-3 = refl
hexXor-spin-correct hex-2 hex-4 = refl
hexXor-spin-correct hex-2 hex-5 = refl
hexXor-spin-correct hex-3 hex-0 = refl
hexXor-spin-correct hex-3 hex-1 = refl
hexXor-spin-correct hex-3 hex-2 = refl
hexXor-spin-correct hex-3 hex-3 = refl
hexXor-spin-correct hex-3 hex-4 = refl
hexXor-spin-correct hex-3 hex-5 = refl
hexXor-spin-correct hex-4 hex-0 = refl
hexXor-spin-correct hex-4 hex-1 = refl
hexXor-spin-correct hex-4 hex-2 = refl
hexXor-spin-correct hex-4 hex-3 = refl
hexXor-spin-correct hex-4 hex-4 = refl
hexXor-spin-correct hex-4 hex-5 = refl
hexXor-spin-correct hex-5 hex-0 = refl
hexXor-spin-correct hex-5 hex-1 = refl
hexXor-spin-correct hex-5 hex-2 = refl
hexXor-spin-correct hex-5 hex-3 = refl
hexXor-spin-correct hex-5 hex-4 = refl
hexXor-spin-correct hex-5 hex-5 = refl

rotateHex⁶ : ∀ h → spin 6 rotateHex h ≡ h
rotateHex⁶ hex-0 = refl
rotateHex⁶ hex-1 = refl
rotateHex⁶ hex-2 = refl
rotateHex⁶ hex-3 = refl
rotateHex⁶ hex-4 = refl
rotateHex⁶ hex-5 = refl

hexXor-identityˡ : ∀ h → hexXor hex-0 h ≡ h
hexXor-identityˡ hex-0 = refl
hexXor-identityˡ hex-1 = refl
hexXor-identityˡ hex-2 = refl
hexXor-identityˡ hex-3 = refl
hexXor-identityˡ hex-4 = refl
hexXor-identityˡ hex-5 = refl

------------------------------------------------------------------------

-- A nonary universe: nine “voxels” in a ring.

data NonaryTruth : Set where
  non-0 non-1 non-2 non-3 non-4 non-5 non-6 non-7 non-8 : NonaryTruth

nonary-index : NonaryTruth → Nat
nonary-index non-0 = 0
nonary-index non-1 = 1
nonary-index non-2 = 2
nonary-index non-3 = 3
nonary-index non-4 = 4
nonary-index non-5 = 5
nonary-index non-6 = 6
nonary-index non-7 = 7
nonary-index non-8 = 8

fromNonaryIndex : Nat → NonaryTruth
fromNonaryIndex n with n % 9
... | 0 = non-0
... | 1 = non-1
... | 2 = non-2
... | 3 = non-3
... | 4 = non-4
... | 5 = non-5
... | 6 = non-6
... | 7 = non-7
... | _ = non-8

rotateNonary : NonaryTruth → NonaryTruth
rotateNonary non-0 = non-1
rotateNonary non-1 = non-2
rotateNonary non-2 = non-3
rotateNonary non-3 = non-4
rotateNonary non-4 = non-5
rotateNonary non-5 = non-6
rotateNonary non-6 = non-7
rotateNonary non-7 = non-8
rotateNonary non-8 = non-0

nonaryXor-spin : NonaryTruth → NonaryTruth → NonaryTruth
nonaryXor-spin carrier target = spin (nonary-index carrier) rotateNonary target

nonaryXor-closed : NonaryTruth → NonaryTruth → NonaryTruth
nonaryXor-closed carrier target = fromNonaryIndex (nonary-index carrier + nonary-index target)

nonaryXor : NonaryTruth → NonaryTruth → NonaryTruth
nonaryXor = nonaryXor-closed

nonaryXor-spin-correct : ∀ a b → nonaryXor-spin a b ≡ nonaryXor a b
nonaryXor-spin-correct non-0 non-0 = refl
nonaryXor-spin-correct non-0 non-1 = refl
nonaryXor-spin-correct non-0 non-2 = refl
nonaryXor-spin-correct non-0 non-3 = refl
nonaryXor-spin-correct non-0 non-4 = refl
nonaryXor-spin-correct non-0 non-5 = refl
nonaryXor-spin-correct non-0 non-6 = refl
nonaryXor-spin-correct non-0 non-7 = refl
nonaryXor-spin-correct non-0 non-8 = refl
nonaryXor-spin-correct non-1 non-0 = refl
nonaryXor-spin-correct non-1 non-1 = refl
nonaryXor-spin-correct non-1 non-2 = refl
nonaryXor-spin-correct non-1 non-3 = refl
nonaryXor-spin-correct non-1 non-4 = refl
nonaryXor-spin-correct non-1 non-5 = refl
nonaryXor-spin-correct non-1 non-6 = refl
nonaryXor-spin-correct non-1 non-7 = refl
nonaryXor-spin-correct non-1 non-8 = refl
nonaryXor-spin-correct non-2 non-0 = refl
nonaryXor-spin-correct non-2 non-1 = refl
nonaryXor-spin-correct non-2 non-2 = refl
nonaryXor-spin-correct non-2 non-3 = refl
nonaryXor-spin-correct non-2 non-4 = refl
nonaryXor-spin-correct non-2 non-5 = refl
nonaryXor-spin-correct non-2 non-6 = refl
nonaryXor-spin-correct non-2 non-7 = refl
nonaryXor-spin-correct non-2 non-8 = refl
nonaryXor-spin-correct non-3 non-0 = refl
nonaryXor-spin-correct non-3 non-1 = refl
nonaryXor-spin-correct non-3 non-2 = refl
nonaryXor-spin-correct non-3 non-3 = refl
nonaryXor-spin-correct non-3 non-4 = refl
nonaryXor-spin-correct non-3 non-5 = refl
nonaryXor-spin-correct non-3 non-6 = refl
nonaryXor-spin-correct non-3 non-7 = refl
nonaryXor-spin-correct non-3 non-8 = refl
nonaryXor-spin-correct non-4 non-0 = refl
nonaryXor-spin-correct non-4 non-1 = refl
nonaryXor-spin-correct non-4 non-2 = refl
nonaryXor-spin-correct non-4 non-3 = refl
nonaryXor-spin-correct non-4 non-4 = refl
nonaryXor-spin-correct non-4 non-5 = refl
nonaryXor-spin-correct non-4 non-6 = refl
nonaryXor-spin-correct non-4 non-7 = refl
nonaryXor-spin-correct non-4 non-8 = refl
nonaryXor-spin-correct non-5 non-0 = refl
nonaryXor-spin-correct non-5 non-1 = refl
nonaryXor-spin-correct non-5 non-2 = refl
nonaryXor-spin-correct non-5 non-3 = refl
nonaryXor-spin-correct non-5 non-4 = refl
nonaryXor-spin-correct non-5 non-5 = refl
nonaryXor-spin-correct non-5 non-6 = refl
nonaryXor-spin-correct non-5 non-7 = refl
nonaryXor-spin-correct non-5 non-8 = refl
nonaryXor-spin-correct non-6 non-0 = refl
nonaryXor-spin-correct non-6 non-1 = refl
nonaryXor-spin-correct non-6 non-2 = refl
nonaryXor-spin-correct non-6 non-3 = refl
nonaryXor-spin-correct non-6 non-4 = refl
nonaryXor-spin-correct non-6 non-5 = refl
nonaryXor-spin-correct non-6 non-6 = refl
nonaryXor-spin-correct non-6 non-7 = refl
nonaryXor-spin-correct non-6 non-8 = refl
nonaryXor-spin-correct non-7 non-0 = refl
nonaryXor-spin-correct non-7 non-1 = refl
nonaryXor-spin-correct non-7 non-2 = refl
nonaryXor-spin-correct non-7 non-3 = refl
nonaryXor-spin-correct non-7 non-4 = refl
nonaryXor-spin-correct non-7 non-5 = refl
nonaryXor-spin-correct non-7 non-6 = refl
nonaryXor-spin-correct non-7 non-7 = refl
nonaryXor-spin-correct non-7 non-8 = refl
nonaryXor-spin-correct non-8 non-0 = refl
nonaryXor-spin-correct non-8 non-1 = refl
nonaryXor-spin-correct non-8 non-2 = refl
nonaryXor-spin-correct non-8 non-3 = refl
nonaryXor-spin-correct non-8 non-4 = refl
nonaryXor-spin-correct non-8 non-5 = refl
nonaryXor-spin-correct non-8 non-6 = refl
nonaryXor-spin-correct non-8 non-7 = refl
nonaryXor-spin-correct non-8 non-8 = refl

rotateNonary⁹ : ∀ n → spin 9 rotateNonary n ≡ n
rotateNonary⁹ non-0 = refl
rotateNonary⁹ non-1 = refl
rotateNonary⁹ non-2 = refl
rotateNonary⁹ non-3 = refl
rotateNonary⁹ non-4 = refl
rotateNonary⁹ non-5 = refl
rotateNonary⁹ non-6 = refl
rotateNonary⁹ non-7 = refl
rotateNonary⁹ non-8 = refl

nonaryXor-identityˡ : ∀ n → nonaryXor non-0 n ≡ n
nonaryXor-identityˡ non-0 = refl
nonaryXor-identityˡ non-1 = refl
nonaryXor-identityˡ non-2 = refl
nonaryXor-identityˡ non-3 = refl
nonaryXor-identityˡ non-4 = refl
nonaryXor-identityˡ non-5 = refl
nonaryXor-identityˡ non-6 = refl
nonaryXor-identityˡ non-7 = refl
nonaryXor-identityˡ non-8 = refl
