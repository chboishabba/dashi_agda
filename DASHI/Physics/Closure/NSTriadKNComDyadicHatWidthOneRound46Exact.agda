module DASHI.Physics.Closure.NSTriadKNComDyadicHatWidthOneRound46Exact where

------------------------------------------------------------------------
-- PRIMARY SOURCES / CONTEXT
--
-- Author: Jean-Michel Bony.
-- Title: "Calcul symbolique et propagation des singularites pour les
-- equations aux derivees partielles non lineaires".
-- DOI: 10.24033/asens.1404.
--
-- Authors: Hajer Bahouri; Jean-Yves Chemin; Raphael Danchin.
-- Title: "Fourier Analysis and Nonlinear Partial Differential Equations".
-- DOI: 10.1007/978-3-642-16830-7.
--
-- DASHI CONTRIBUTION
--
-- The repository's concrete rational dyadic-hat support has zero, one, or two
-- adjacent active shells.  Round 46 proves the stronger pairwise statement:
-- any two shell indices active in the SAME hat support are equal or adjacent.
--
-- This establishes exact width one for the concrete hat geometry itself.  It
-- does not yet identify the physical odd-P/Q Com support graph with one common
-- hat support; that same-object identification remains the only bridge needed
-- before `maxActiveDistance = 1` can be installed in the Com theorem.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat; zero; suc)

import DASHI.Physics.Closure.NSPeriodicNearShellOverlapCount as Hat

data _∈_ {A : Set} (x : A) : List A → Set where
  here : ∀ {xs} → x ∈ (x ∷ xs)
  there : ∀ {y xs} → x ∈ xs → x ∈ (y ∷ xs)

infix 4 _∈_

data WithinOne : Nat → Nat → Set where
  same : ∀ q → WithinOne q q
  next : ∀ q → WithinOne q (suc q)
  previous : ∀ q → WithinOne (suc q) q

withinOneSymmetric : ∀ {q r} → WithinOne q r → WithinOne r q
withinOneSymmetric (same q) = same q
withinOneSymmetric (next q) = previous q
withinOneSymmetric (previous q) = next q

activeShellPairWithinOne :
  ∀ support q r →
  q ∈ Hat.activeShells support →
  r ∈ Hat.activeShells support →
  WithinOne q r
activeShellPairWithinOne Hat.noActiveShell q r () rActive
activeShellPairWithinOne (Hat.oneActiveShell j) .j .j here here = same j
activeShellPairWithinOne (Hat.oneActiveShell j) .j r here (there ())
activeShellPairWithinOne (Hat.oneActiveShell j) q r (there ()) rActive
activeShellPairWithinOne (Hat.twoAdjacentShells j) .j .j here here = same j
activeShellPairWithinOne (Hat.twoAdjacentShells j) .j .(suc j) here (there here) = next j
activeShellPairWithinOne (Hat.twoAdjacentShells j) .j r here (there (there ()))
activeShellPairWithinOne (Hat.twoAdjacentShells j) .(suc j) .j (there here) here = previous j
activeShellPairWithinOne (Hat.twoAdjacentShells j) .(suc j) .(suc j) (there here) (there here) = same (suc j)
activeShellPairWithinOne (Hat.twoAdjacentShells j) .(suc j) r (there here) (there (there ()))
activeShellPairWithinOne (Hat.twoAdjacentShells j) q r (there (there ())) rActive

record PhysicalOddPQHatSupportIdentification : Set₁ where
  field
    supportActive : Nat → Nat → Bool
    commonHatSupport : Nat → Nat → Hat.DyadicHatSupport

    leftActiveInCommonHat : ∀ q r →
      supportActive q r ≡ true →
      q ∈ Hat.activeShells (commonHatSupport q r)

    rightActiveInCommonHat : ∀ q r →
      supportActive q r ≡ true →
      r ∈ Hat.activeShells (commonHatSupport q r)

open PhysicalOddPQHatSupportIdentification public

physicalActivePairWithinOne :
  (identification : PhysicalOddPQHatSupportIdentification) →
  ∀ q r →
  supportActive identification q r ≡ true →
  WithinOne q r
physicalActivePairWithinOne identification q r active =
  activeShellPairWithinOne
    (commonHatSupport identification q r)
    q r
    (leftActiveInCommonHat identification q r active)
    (rightActiveInCommonHat identification q r active)

concreteDyadicHatSupportHasExactWidthOne : Bool
concreteDyadicHatSupportHasExactWidthOne = true

physicalOddPQIdentifiedWithCommonDyadicHatSupport : Bool
physicalOddPQIdentifiedWithCommonDyadicHatSupport = false

concreteDyadicHatSupportHasExactWidthOneIsTrue :
  concreteDyadicHatSupportHasExactWidthOne ≡ true
concreteDyadicHatSupportHasExactWidthOneIsTrue = refl

physicalOddPQIdentifiedWithCommonDyadicHatSupportIsFalse :
  physicalOddPQIdentifiedWithCommonDyadicHatSupport ≡ false
physicalOddPQIdentifiedWithCommonDyadicHatSupportIsFalse = refl
