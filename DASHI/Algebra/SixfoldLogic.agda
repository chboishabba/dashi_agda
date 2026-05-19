module DASHI.Algebra.SixfoldLogic where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.List.Base using (List; _∷_; [])
open import Agda.Builtin.String using (String)

open import Base369 using
  ( HexTruth
  ; hex-0 ; hex-1 ; hex-2 ; hex-3 ; hex-4 ; hex-5
  ; rotateHex
  ; spin
  )

------------------------------------------------------------------------
-- Sixfold logic carrier over Base369.HexTruth.
--
-- This is the six-position extension suggested by the current design notes:
-- four tetralemma-like positions plus two bounded unknowable/scope positions.
-- It is a formal carrier bridge only, not a claim about external traditions.

data Stage6 : Set where
  affirmed : Stage6
  denied : Stage6
  affirmedAndDenied : Stage6
  inexpressible : Stage6
  affirmedInexpressible : Stage6
  deniedInexpressible : Stage6

underdetermined : Stage6
underdetermined = affirmedInexpressible

scopeExceeded : Stage6
scopeExceeded = deniedInexpressible

next6 : Stage6 → Stage6
next6 affirmed = denied
next6 denied = affirmedAndDenied
next6 affirmedAndDenied = inexpressible
next6 inexpressible = affirmedInexpressible
next6 affirmedInexpressible = deniedInexpressible
next6 deniedInexpressible = affirmed

hexTone : Stage6 → HexTruth
hexTone affirmed = hex-0
hexTone denied = hex-1
hexTone affirmedAndDenied = hex-2
hexTone inexpressible = hex-3
hexTone affirmedInexpressible = hex-4
hexTone deniedInexpressible = hex-5

hexTone-next :
  ∀ s →
  hexTone (next6 s) ≡ rotateHex (hexTone s)
hexTone-next affirmed = refl
hexTone-next denied = refl
hexTone-next affirmedAndDenied = refl
hexTone-next inexpressible = refl
hexTone-next affirmedInexpressible = refl
hexTone-next deniedInexpressible = refl

next6⁶ :
  ∀ s →
  spin 6 next6 s ≡ s
next6⁶ affirmed = refl
next6⁶ denied = refl
next6⁶ affirmedAndDenied = refl
next6⁶ inexpressible = refl
next6⁶ affirmedInexpressible = refl
next6⁶ deniedInexpressible = refl

hexTone-cycle :
  ∀ s →
  spin 6 rotateHex (hexTone s) ≡ hexTone s
hexTone-cycle affirmed = refl
hexTone-cycle denied = refl
hexTone-cycle affirmedAndDenied = refl
hexTone-cycle inexpressible = refl
hexTone-cycle affirmedInexpressible = refl
hexTone-cycle deniedInexpressible = refl

record SixfoldHexBridgeSurface : Set₁ where
  field
    sixfoldCarrier : Set
    hexCarrier : Set
    tone : Stage6 → HexTruth
    transport :
      ∀ s →
      tone (next6 s) ≡ rotateHex (tone s)
    period :
      ∀ s →
      spin 6 next6 s ≡ s
    nonClaimBoundary : List String

sixfoldHexBridgeSurface : SixfoldHexBridgeSurface
sixfoldHexBridgeSurface =
  record
    { sixfoldCarrier = Stage6
    ; hexCarrier = HexTruth
    ; tone = hexTone
    ; transport = hexTone-next
    ; period = next6⁶
    ; nonClaimBoundary =
        "Stage6 is a formal six-position carrier over Base369.HexTruth"
        ∷ "It does not alter CLOCKPhaseInstance or claim dihedral/reversal structure"
        ∷ "Underdetermined and scope-exceeded positions are named carrier states, not runtime parser outcomes"
        ∷ []
    }
