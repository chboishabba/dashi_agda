module DASHI.Arithmetic.GlobalPressure where

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero)
open import Relation.Binary.PropositionalEquality using (cong; sym)

open import MonsterOntos using
  ( SSP
  ; p2 ; p3 ; p5 ; p7 ; p11 ; p13 ; p17 ; p19 ; p23 ; p29 ; p31 ; p41 ; p47 ; p59 ; p71
  )
open import Ontology.GodelLattice renaming (v15 to mkVec15)

open import DASHI.Arithmetic.ArithmeticIntegerEmbedding using
  ( Int
  ; deltaAt
  ; delta15
  )
open import DASHI.Arithmetic.ArithmeticPrimeProfileBridge using
  ( wallBitBridge
  ; offWallZero
  )
open import DASHI.Arithmetic.PrimeIndexedPressure using
  ( sum15 )

------------------------------------------------------------------------
-- Wall-filtered local pressure.

wallDeltaAt : SSP → Int → Int → Nat
wallDeltaAt p x y with wallBitBridge p x y
... | true  = deltaAt p x y
... | false = zero

------------------------------------------------------------------------
-- Total and wall-filtered global pressure over the tracked 15-prime carrier.

totalPressure : Int → Int → Nat
totalPressure x y = sum15 (delta15 x y)

wallDelta15 : Int → Int → Ontology.GodelLattice.Vec15 Nat
wallDelta15 x y =
  mkVec15
    (wallDeltaAt p2 x y) (wallDeltaAt p3 x y) (wallDeltaAt p5 x y) (wallDeltaAt p7 x y)
    (wallDeltaAt p11 x y) (wallDeltaAt p13 x y) (wallDeltaAt p17 x y) (wallDeltaAt p19 x y)
    (wallDeltaAt p23 x y) (wallDeltaAt p29 x y) (wallDeltaAt p31 x y) (wallDeltaAt p41 x y)
    (wallDeltaAt p47 x y) (wallDeltaAt p59 x y) (wallDeltaAt p71 x y)

wallPressure : Int → Int → Nat
wallPressure x y = sum15 (wallDelta15 x y)

------------------------------------------------------------------------
-- Local wall-filtering preserves the tracked delta exactly.

wallDeltaAt≡deltaAt :
  ∀ p x y →
  wallDeltaAt p x y ≡ deltaAt p x y
wallDeltaAt≡deltaAt p x y with wallBitBridge p x y in wallEq
... | true = refl
... | false rewrite offWallZero p x y wallEq = refl

wallDelta15≡delta15 :
  ∀ x y →
  wallDelta15 x y ≡ delta15 x y
wallDelta15≡delta15 x y
  rewrite wallDeltaAt≡deltaAt p2 x y
        | wallDeltaAt≡deltaAt p3 x y
        | wallDeltaAt≡deltaAt p5 x y
        | wallDeltaAt≡deltaAt p7 x y
        | wallDeltaAt≡deltaAt p11 x y
        | wallDeltaAt≡deltaAt p13 x y
        | wallDeltaAt≡deltaAt p17 x y
        | wallDeltaAt≡deltaAt p19 x y
        | wallDeltaAt≡deltaAt p23 x y
        | wallDeltaAt≡deltaAt p29 x y
        | wallDeltaAt≡deltaAt p31 x y
        | wallDeltaAt≡deltaAt p41 x y
        | wallDeltaAt≡deltaAt p47 x y
        | wallDeltaAt≡deltaAt p59 x y
        | wallDeltaAt≡deltaAt p71 x y
  = refl

------------------------------------------------------------------------
-- First global structural theorem:
-- total tracked pressure lives entirely on wall primes.

totalPressure≡wallPressure :
  ∀ x y →
  totalPressure x y ≡ wallPressure x y
totalPressure≡wallPressure x y =
  sym (cong sum15 (wallDelta15≡delta15 x y))

record GlobalPressureStructure : Set₁ where
  field
    total : Int → Int → Nat
    wall : Int → Int → Nat
    total≡wall :
      ∀ x y →
      total x y ≡ wall x y

open GlobalPressureStructure public

globalPressureStructure : GlobalPressureStructure
globalPressureStructure = record
  { total = totalPressure
  ; wall = wallPressure
  ; total≡wall = totalPressure≡wallPressure
  }
