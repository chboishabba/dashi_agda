module DASHI.Physics.Base369PhaseBridge where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Empty using (⊥)

open import Base369 using
  ( HexTruth
  ; NonaryTruth
  ; TriTruth
  ; hex-0
  ; hex-1
  ; hex-2
  ; hex-3
  ; hex-4
  ; hex-5
  ; non-0
  ; non-1
  ; non-2
  ; non-3
  ; non-4
  ; non-5
  ; non-6
  ; non-7
  ; non-8
  ; tri-high
  ; tri-low
  ; tri-mid
  ; hexXor
  ; nonaryXor
  ; rotateHex
  ; rotateNonary
  ; rotateTri
  ; spin
  ; triXor
  )
open import DASHI.Physics.CLOCKPhaseBridge using
  ( coarseHex
  ; coarseHex-rotateHex
  )

infix 4 _≢_

_≢_ : {A : Set} → A → A → Set
x ≢ y = x ≡ y → ⊥

coarseHexMod3 : HexTruth → TriTruth
coarseHexMod3 = coarseHex

q6 : HexTruth → TriTruth
q6 = coarseHexMod3

q6-rotate : ∀ h → q6 (rotateHex h) ≡ rotateTri (q6 h)
q6-rotate = coarseHex-rotateHex

coarseNonaryMod3 : NonaryTruth → TriTruth
coarseNonaryMod3 non-0 = tri-low
coarseNonaryMod3 non-1 = tri-mid
coarseNonaryMod3 non-2 = tri-high
coarseNonaryMod3 non-3 = tri-low
coarseNonaryMod3 non-4 = tri-mid
coarseNonaryMod3 non-5 = tri-high
coarseNonaryMod3 non-6 = tri-low
coarseNonaryMod3 non-7 = tri-mid
coarseNonaryMod3 non-8 = tri-high

q9 : NonaryTruth → TriTruth
q9 = coarseNonaryMod3

q9-rotate : ∀ n → q9 (rotateNonary n) ≡ rotateTri (q9 n)
q9-rotate non-0 = refl
q9-rotate non-1 = refl
q9-rotate non-2 = refl
q9-rotate non-3 = refl
q9-rotate non-4 = refl
q9-rotate non-5 = refl
q9-rotate non-6 = refl
q9-rotate non-7 = refl
q9-rotate non-8 = refl

coarseNonaryBlock : NonaryTruth → TriTruth
coarseNonaryBlock non-0 = tri-low
coarseNonaryBlock non-1 = tri-low
coarseNonaryBlock non-2 = tri-low
coarseNonaryBlock non-3 = tri-mid
coarseNonaryBlock non-4 = tri-mid
coarseNonaryBlock non-5 = tri-mid
coarseNonaryBlock non-6 = tri-high
coarseNonaryBlock non-7 = tri-high
coarseNonaryBlock non-8 = tri-high

coarseNonaryBlock-rotate-obstruction :
  coarseNonaryBlock (rotateNonary non-0) ≢ rotateTri (coarseNonaryBlock non-0)
coarseNonaryBlock-rotate-obstruction ()

e6 : TriTruth → HexTruth
e6 tri-low  = hex-0
e6 tri-mid  = hex-4
e6 tri-high = hex-2

e6-section : ∀ t → q6 (e6 t) ≡ t
e6-section tri-low  = refl
e6-section tri-mid  = refl
e6-section tri-high = refl

e6-rotate4 : ∀ t → q6 (spin 4 rotateHex (e6 t)) ≡ rotateTri (q6 (e6 t))
e6-rotate4 tri-low  = refl
e6-rotate4 tri-mid  = refl
e6-rotate4 tri-high = refl

e6-spin4-commute : ∀ t → spin 4 rotateHex (e6 t) ≡ e6 (rotateTri t)
e6-spin4-commute tri-low  = refl
e6-spin4-commute tri-mid  = refl
e6-spin4-commute tri-high = refl

e9 : TriTruth → NonaryTruth
e9 tri-low  = non-0
e9 tri-mid  = non-3
e9 tri-high = non-6

e9-spin3-commute : ∀ t → spin 3 rotateNonary (e9 t) ≡ e9 (rotateTri t)
e9-spin3-commute tri-low  = refl
e9-spin3-commute tri-mid  = refl
e9-spin3-commute tri-high = refl

e9-not-section : ∀ t → q9 (e9 t) ≡ tri-low
e9-not-section tri-low  = refl
e9-not-section tri-mid  = refl
e9-not-section tri-high = refl

q6-xor-hom : ∀ a b → q6 (hexXor a b) ≡ triXor (q6 a) (q6 b)
q6-xor-hom hex-0 hex-0 = refl
q6-xor-hom hex-0 hex-1 = refl
q6-xor-hom hex-0 hex-2 = refl
q6-xor-hom hex-0 hex-3 = refl
q6-xor-hom hex-0 hex-4 = refl
q6-xor-hom hex-0 hex-5 = refl
q6-xor-hom hex-1 hex-0 = refl
q6-xor-hom hex-1 hex-1 = refl
q6-xor-hom hex-1 hex-2 = refl
q6-xor-hom hex-1 hex-3 = refl
q6-xor-hom hex-1 hex-4 = refl
q6-xor-hom hex-1 hex-5 = refl
q6-xor-hom hex-2 hex-0 = refl
q6-xor-hom hex-2 hex-1 = refl
q6-xor-hom hex-2 hex-2 = refl
q6-xor-hom hex-2 hex-3 = refl
q6-xor-hom hex-2 hex-4 = refl
q6-xor-hom hex-2 hex-5 = refl
q6-xor-hom hex-3 hex-0 = refl
q6-xor-hom hex-3 hex-1 = refl
q6-xor-hom hex-3 hex-2 = refl
q6-xor-hom hex-3 hex-3 = refl
q6-xor-hom hex-3 hex-4 = refl
q6-xor-hom hex-3 hex-5 = refl
q6-xor-hom hex-4 hex-0 = refl
q6-xor-hom hex-4 hex-1 = refl
q6-xor-hom hex-4 hex-2 = refl
q6-xor-hom hex-4 hex-3 = refl
q6-xor-hom hex-4 hex-4 = refl
q6-xor-hom hex-4 hex-5 = refl
q6-xor-hom hex-5 hex-0 = refl
q6-xor-hom hex-5 hex-1 = refl
q6-xor-hom hex-5 hex-2 = refl
q6-xor-hom hex-5 hex-3 = refl
q6-xor-hom hex-5 hex-4 = refl
q6-xor-hom hex-5 hex-5 = refl

q9-xor-hom : ∀ a b → q9 (nonaryXor a b) ≡ triXor (q9 a) (q9 b)
q9-xor-hom non-0 non-0 = refl
q9-xor-hom non-0 non-1 = refl
q9-xor-hom non-0 non-2 = refl
q9-xor-hom non-0 non-3 = refl
q9-xor-hom non-0 non-4 = refl
q9-xor-hom non-0 non-5 = refl
q9-xor-hom non-0 non-6 = refl
q9-xor-hom non-0 non-7 = refl
q9-xor-hom non-0 non-8 = refl
q9-xor-hom non-1 non-0 = refl
q9-xor-hom non-1 non-1 = refl
q9-xor-hom non-1 non-2 = refl
q9-xor-hom non-1 non-3 = refl
q9-xor-hom non-1 non-4 = refl
q9-xor-hom non-1 non-5 = refl
q9-xor-hom non-1 non-6 = refl
q9-xor-hom non-1 non-7 = refl
q9-xor-hom non-1 non-8 = refl
q9-xor-hom non-2 non-0 = refl
q9-xor-hom non-2 non-1 = refl
q9-xor-hom non-2 non-2 = refl
q9-xor-hom non-2 non-3 = refl
q9-xor-hom non-2 non-4 = refl
q9-xor-hom non-2 non-5 = refl
q9-xor-hom non-2 non-6 = refl
q9-xor-hom non-2 non-7 = refl
q9-xor-hom non-2 non-8 = refl
q9-xor-hom non-3 non-0 = refl
q9-xor-hom non-3 non-1 = refl
q9-xor-hom non-3 non-2 = refl
q9-xor-hom non-3 non-3 = refl
q9-xor-hom non-3 non-4 = refl
q9-xor-hom non-3 non-5 = refl
q9-xor-hom non-3 non-6 = refl
q9-xor-hom non-3 non-7 = refl
q9-xor-hom non-3 non-8 = refl
q9-xor-hom non-4 non-0 = refl
q9-xor-hom non-4 non-1 = refl
q9-xor-hom non-4 non-2 = refl
q9-xor-hom non-4 non-3 = refl
q9-xor-hom non-4 non-4 = refl
q9-xor-hom non-4 non-5 = refl
q9-xor-hom non-4 non-6 = refl
q9-xor-hom non-4 non-7 = refl
q9-xor-hom non-4 non-8 = refl
q9-xor-hom non-5 non-0 = refl
q9-xor-hom non-5 non-1 = refl
q9-xor-hom non-5 non-2 = refl
q9-xor-hom non-5 non-3 = refl
q9-xor-hom non-5 non-4 = refl
q9-xor-hom non-5 non-5 = refl
q9-xor-hom non-5 non-6 = refl
q9-xor-hom non-5 non-7 = refl
q9-xor-hom non-5 non-8 = refl
q9-xor-hom non-6 non-0 = refl
q9-xor-hom non-6 non-1 = refl
q9-xor-hom non-6 non-2 = refl
q9-xor-hom non-6 non-3 = refl
q9-xor-hom non-6 non-4 = refl
q9-xor-hom non-6 non-5 = refl
q9-xor-hom non-6 non-6 = refl
q9-xor-hom non-6 non-7 = refl
q9-xor-hom non-6 non-8 = refl
q9-xor-hom non-7 non-0 = refl
q9-xor-hom non-7 non-1 = refl
q9-xor-hom non-7 non-2 = refl
q9-xor-hom non-7 non-3 = refl
q9-xor-hom non-7 non-4 = refl
q9-xor-hom non-7 non-5 = refl
q9-xor-hom non-7 non-6 = refl
q9-xor-hom non-7 non-7 = refl
q9-xor-hom non-7 non-8 = refl
q9-xor-hom non-8 non-0 = refl
q9-xor-hom non-8 non-1 = refl
q9-xor-hom non-8 non-2 = refl
q9-xor-hom non-8 non-3 = refl
q9-xor-hom non-8 non-4 = refl
q9-xor-hom non-8 non-5 = refl
q9-xor-hom non-8 non-6 = refl
q9-xor-hom non-8 non-7 = refl
q9-xor-hom non-8 non-8 = refl

e6-xor-hom : ∀ a b → e6 (triXor a b) ≡ hexXor (e6 a) (e6 b)
e6-xor-hom tri-low tri-low = refl
e6-xor-hom tri-low tri-mid = refl
e6-xor-hom tri-low tri-high = refl
e6-xor-hom tri-mid tri-low = refl
e6-xor-hom tri-mid tri-mid = refl
e6-xor-hom tri-mid tri-high = refl
e6-xor-hom tri-high tri-low = refl
e6-xor-hom tri-high tri-mid = refl
e6-xor-hom tri-high tri-high = refl

e9-xor-hom : ∀ a b → e9 (triXor a b) ≡ nonaryXor (e9 a) (e9 b)
e9-xor-hom tri-low tri-low = refl
e9-xor-hom tri-low tri-mid = refl
e9-xor-hom tri-low tri-high = refl
e9-xor-hom tri-mid tri-low = refl
e9-xor-hom tri-mid tri-mid = refl
e9-xor-hom tri-mid tri-high = refl
e9-xor-hom tri-high tri-low = refl
e9-xor-hom tri-high tri-mid = refl
e9-xor-hom tri-high tri-high = refl

record QuotientLawTable : Set where
  field
    hex-rotate-law    : ∀ h → q6 (rotateHex h) ≡ rotateTri (q6 h)
    hex-xor-law       : ∀ a b → q6 (hexXor a b) ≡ triXor (q6 a) (q6 b)
    nonary-rotate-law : ∀ n → q9 (rotateNonary n) ≡ rotateTri (q9 n)
    nonary-xor-law    : ∀ a b → q9 (nonaryXor a b) ≡ triXor (q9 a) (q9 b)

quotientLawTable : QuotientLawTable
quotientLawTable = record
  { hex-rotate-law = q6-rotate
  ; hex-xor-law = q6-xor-hom
  ; nonary-rotate-law = q9-rotate
  ; nonary-xor-law = q9-xor-hom
  }

record LiftLawTable : Set where
  field
    hex-section-law       : ∀ t → q6 (e6 t) ≡ t
    hex-spin4-law         : ∀ t → spin 4 rotateHex (e6 t) ≡ e6 (rotateTri t)
    hex-xor-lift-law      : ∀ a b → e6 (triXor a b) ≡ hexXor (e6 a) (e6 b)
    nonary-spin3-law      : ∀ t → spin 3 rotateNonary (e9 t) ≡ e9 (rotateTri t)
    nonary-collapse-law   : ∀ t → q9 (e9 t) ≡ tri-low
    nonary-xor-lift-law   : ∀ a b → e9 (triXor a b) ≡ nonaryXor (e9 a) (e9 b)

liftLawTable : LiftLawTable
liftLawTable = record
  { hex-section-law = e6-section
  ; hex-spin4-law = e6-spin4-commute
  ; hex-xor-lift-law = e6-xor-hom
  ; nonary-spin3-law = e9-spin3-commute
  ; nonary-collapse-law = e9-not-section
  ; nonary-xor-lift-law = e9-xor-hom
  }
