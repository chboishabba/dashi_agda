module DASHI.Foundations.Base369CirclePhase where

open import Agda.Builtin.Bool using (Bool; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; _+_; _*_)
open import Agda.Builtin.String using (String)
open import Base369 using
  ( TriTruth
  ; HexTruth
  ; NonaryTruth
  ; tri-low
  ; tri-mid
  ; tri-high
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
  )
open import DASHI.Foundations.Base369Nat using (_%_)
open import DASHI.Foundations.NumberRoleBoundary using
  ( NumberRoleReading
  ; algebraCarrierRole
  ; phaseTopologicalRole
  ; numeral3
  ; numeral6
  ; numeral9
  ; mkNumberRoleReading
  )

------------------------------------------------------------------------
-- A generated 3/6/9 expression language.
--
-- This is deliberately a generating syntax, not a claim that 3, 6, 9
-- form a linearly independent basis.  Every denotation is stored in
-- units of three, so membership in the non-unital subsemiring 3ℕ is
-- constructionally visible.

infixl 6 _⊕_
infixl 7 _⊗_

data Expr369 : Set where
  atom3 : Expr369
  atom6 : Expr369
  atom9 : Expr369
  _⊕_ : Expr369 → Expr369 → Expr369
  _⊗_ : Expr369 → Expr369 → Expr369

unitValue : Expr369 → Nat
unitValue atom3 = 1
unitValue atom6 = 2
unitValue atom9 = 3
unitValue (x ⊕ y) = unitValue x + unitValue y
unitValue (x ⊗ y) = 3 * (unitValue x * unitValue y)

eval369 : Expr369 → Nat
eval369 e = 3 * unitValue e

atom3-value : eval369 atom3 ≡ 3
atom3-value = refl

atom6-value : eval369 atom6 ≡ 6
atom6-value = refl

atom9-value : eval369 atom9 ≡ 9
atom9-value = refl

fortyFiveExpr : Expr369
fortyFiveExpr = atom3 ⊗ (atom6 ⊕ atom9)

fortyFiveExpr-value : eval369 fortyFiveExpr ≡ 45
fortyFiveExpr-value = refl

record MultipleOfThree (n : Nat) : Set where
  constructor threeTimes
  field
    quotient : Nat
    factorisation : n ≡ 3 * quotient

open MultipleOfThree public

eval369-is-multiple-of-three :
  (e : Expr369) →
  MultipleOfThree (eval369 e)
eval369-is-multiple-of-three e =
  threeTimes (unitValue e) refl

------------------------------------------------------------------------
-- Circle phase carriers.
--
-- TriTruth, HexTruth, and NonaryTruth already realise C3, C6, and C9.
-- The common refinement of the six- and nine-sector grids is C18.

data Phase18 : Set where
  p18-0 p18-1 p18-2 p18-3 p18-4 p18-5 : Phase18
  p18-6 p18-7 p18-8 p18-9 p18-10 p18-11 : Phase18
  p18-12 p18-13 p18-14 p18-15 p18-16 p18-17 : Phase18

phase18-index : Phase18 → Nat
phase18-index p18-0 = 0
phase18-index p18-1 = 1
phase18-index p18-2 = 2
phase18-index p18-3 = 3
phase18-index p18-4 = 4
phase18-index p18-5 = 5
phase18-index p18-6 = 6
phase18-index p18-7 = 7
phase18-index p18-8 = 8
phase18-index p18-9 = 9
phase18-index p18-10 = 10
phase18-index p18-11 = 11
phase18-index p18-12 = 12
phase18-index p18-13 = 13
phase18-index p18-14 = 14
phase18-index p18-15 = 15
phase18-index p18-16 = 16
phase18-index p18-17 = 17

fromPhase18Index : Nat → Phase18
fromPhase18Index n with n % 18
... | 0 = p18-0
... | 1 = p18-1
... | 2 = p18-2
... | 3 = p18-3
... | 4 = p18-4
... | 5 = p18-5
... | 6 = p18-6
... | 7 = p18-7
... | 8 = p18-8
... | 9 = p18-9
... | 10 = p18-10
... | 11 = p18-11
... | 12 = p18-12
... | 13 = p18-13
... | 14 = p18-14
... | 15 = p18-15
... | 16 = p18-16
... | _ = p18-17

triToHex : TriTruth → HexTruth
triToHex tri-low = hex-0
triToHex tri-mid = hex-2
triToHex tri-high = hex-4

triToNonary : TriTruth → NonaryTruth
triToNonary tri-low = non-0
triToNonary tri-mid = non-3
triToNonary tri-high = non-6

hexTo18 : HexTruth → Phase18
hexTo18 hex-0 = p18-0
hexTo18 hex-1 = p18-3
hexTo18 hex-2 = p18-6
hexTo18 hex-3 = p18-9
hexTo18 hex-4 = p18-12
hexTo18 hex-5 = p18-15

nonaryTo18 : NonaryTruth → Phase18
nonaryTo18 non-0 = p18-0
nonaryTo18 non-1 = p18-2
nonaryTo18 non-2 = p18-4
nonaryTo18 non-3 = p18-6
nonaryTo18 non-4 = p18-8
nonaryTo18 non-5 = p18-10
nonaryTo18 non-6 = p18-12
nonaryTo18 non-7 = p18-14
nonaryTo18 non-8 = p18-16

tri-common-refinement-commutes :
  (t : TriTruth) →
  hexTo18 (triToHex t) ≡ nonaryTo18 (triToNonary t)
tri-common-refinement-commutes tri-low = refl
tri-common-refinement-commutes tri-mid = refl
tri-common-refinement-commutes tri-high = refl

------------------------------------------------------------------------
-- Role-separated readings.
--
-- The same numerals may be used as algebra carriers or as phase-grid
-- sizes, but NumberRoleBoundary prevents silently identifying those uses.

circleThreePhaseReading : NumberRoleReading
circleThreePhaseReading =
  mkNumberRoleReading
    numeral3
    phaseTopologicalRole
    "3 as the C3 circle-phase grid"
    false
    refl

circleSixPhaseReading : NumberRoleReading
circleSixPhaseReading =
  mkNumberRoleReading
    numeral6
    phaseTopologicalRole
    "6 as the C6 circle-phase grid"
    false
    refl

circleNinePhaseReading : NumberRoleReading
circleNinePhaseReading =
  mkNumberRoleReading
    numeral9
    phaseTopologicalRole
    "9 as the C9 circle-phase grid"
    false
    refl

expression369AlgebraReading : NumberRoleReading
expression369AlgebraReading =
  mkNumberRoleReading
    numeral3
    algebraCarrierRole
    "3/6/9 generated-expression carrier in units of three"
    false
    refl

------------------------------------------------------------------------
-- Analytic boundary for the concentric-ring unrolling argument.
--
-- The finite phase/refinement claims above are checked here.  The sector
-- area identity belongs to an analytic bridge: for angle θ and radius r,
-- straightening infinitesimal concentric arcs gives a triangular profile
-- with base θr and height r, hence area 1/2 θr².  This module records that
-- interpretation without pretending the present Nat carrier proves real
-- integration.

record SectorUnrollingBoundary : Set where
  constructor mkSectorUnrollingBoundary
  field
    interpretation : String
    analyticDerivationPromoted : Bool
    analyticDerivationPromotedIsFalse :
      analyticDerivationPromoted ≡ false

sectorUnrollingBoundary : SectorUnrollingBoundary
sectorUnrollingBoundary =
  mkSectorUnrollingBoundary
    "concentric arc length grows linearly with radius; real-analysis bridge required for area"
    false
    refl
