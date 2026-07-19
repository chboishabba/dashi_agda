module DASHI.Core.GovernedDiagramCore where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)

------------------------------------------------------------------------
-- Category-shaped governed diagram surface.
--
-- This does not assert a full category implementation.  It isolates the common
-- square used throughout DASHI: two paths into a shared codomain, a typed
-- commutation witness, and a residual/obstruction when commutation is absent.
------------------------------------------------------------------------

record GovernedSquare : Set₁ where
  constructor governedSquare
  field
    A B C D : Set
    top    : A → B
    left   : A → C
    right  : B → D
    bottom : C → D

    Commutes : A → Set
    Residual : A → Set

    comparisonNeverMeansTruth : Bool
    residualPromotesTruth     : Bool

open GovernedSquare public

TopRight : (square : GovernedSquare) → A square → D square
TopRight square a = right square (top square a)

LeftBottom : (square : GovernedSquare) → A square → D square
LeftBottom square a = bottom square (left square a)

record CommutingSquareWitness (square : GovernedSquare) : Set where
  constructor commutingSquareWitness
  field
    commutes : (a : A square) → TopRight square a ≡ LeftBottom square a

open CommutingSquareWitness public

record ResidualSquareWitness (square : GovernedSquare) : Set where
  constructor residualSquareWitness
  field
    residual : (a : A square) → Residual square a

open ResidualSquareWitness public

record CanonicalGovernanceBoundary (square : GovernedSquare) : Set where
  constructor canonicalGovernanceBoundary
  field
    comparisonNonAuthoritative :
      comparisonNeverMeansTruth square ≡ true
    residualNonPromoting :
      residualPromotesTruth square ≡ false

open CanonicalGovernanceBoundary public
