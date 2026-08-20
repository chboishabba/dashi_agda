module DASHI.Physics.Closure.NSTriadKNResonantDominantCommonHatRound63Exact where

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
-- ROUND 63 / B0 COMMON-HAT CONSTRUCTION
--
-- The preceding theorem proves that every resonant triad has a dominant pair
-- of shells related by `WithinOne`.  Here that relation is converted into the
-- repository's concrete `DyadicHatSupport`: one shell in the equal case, or
-- the corresponding two-adjacent-shell hat otherwise.
--
-- Thus the common-hat object is now constructed from resonance geometry.  It
-- is NOT the raw low-pass cutoff support and NOT the simple endpoint annular
-- support, both of which have explicit counterexamples in Round62/63.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)

import DASHI.Physics.Closure.NSTriadKNPhysicalTriadEnumeration as Physical
import DASHI.Physics.Closure.NSTriadKNLiteralDyadicShellConstants as Shell
import DASHI.Physics.Closure.NSTriadKNComDyadicHatWidthOneRound46Exact as Width
import DASHI.Physics.Closure.NSPeriodicNearShellOverlapCount as Hat
import DASHI.Physics.Closure.NSTriadKNResonantDominantTwoShellsRound63Exact as Dominant

record CommonHatForPair (left right : Nat) : Set where
  field
    support : Hat.DyadicHatSupport
    leftInSupport : left Width.∈ Hat.activeShells support
    rightInSupport : right Width.∈ Hat.activeShells support

open CommonHatForPair public

commonHatFromWithinOne :
  ∀ {left right} → Width.WithinOne left right → CommonHatForPair left right
commonHatFromWithinOne (Width.same q) = record
  { support = Hat.oneActiveShell q
  ; leftInSupport = Width.here refl
  ; rightInSupport = Width.here refl
  }
commonHatFromWithinOne (Width.next q) = record
  { support = Hat.twoAdjacentShells q
  ; leftInSupport = Width.here refl
  ; rightInSupport = Width.there (Width.here refl)
  }
commonHatFromWithinOne (Width.previous q) = record
  { support = Hat.twoAdjacentShells q
  ; leftInSupport = Width.there (Width.here refl)
  ; rightInSupport = Width.here refl
  }

record ResonantDominantCommonHat
    (tau : Physical.PhysicalTriadIncidence) : Set where
  field
    dominantPair : Dominant.DominantLegPair tau
    leftShell : Nat
    rightShell : Nat
    pairHat : CommonHatForPair leftShell rightShell

open ResonantDominantCommonHat public

resonantDominantCommonHat :
  (tau : Physical.PhysicalTriadIncidence) → ResonantDominantCommonHat tau
resonantDominantCommonHat tau
  with Dominant.resonantDominantTwoShells tau
... | Dominant.dominantPQ within = record
  { dominantPair = Dominant.dominantPQ within
  ; leftShell = Shell.shellIndex (Physical.p tau)
  ; rightShell = Shell.shellIndex (Physical.q tau)
  ; pairHat = commonHatFromWithinOne within
  }
... | Dominant.dominantPK within = record
  { dominantPair = Dominant.dominantPK within
  ; leftShell = Shell.shellIndex (Physical.p tau)
  ; rightShell = Shell.shellIndex (Physical.k tau)
  ; pairHat = commonHatFromWithinOne within
  }
... | Dominant.dominantQK within = record
  { dominantPair = Dominant.dominantQK within
  ; leftShell = Shell.shellIndex (Physical.q tau)
  ; rightShell = Shell.shellIndex (Physical.k tau)
  ; pairHat = commonHatFromWithinOne within
  }

round63EveryResonantTriadHasConstructedDominantCommonHat : Bool
round63EveryResonantTriadHasConstructedDominantCommonHat = true

round63EveryResonantTriadHasConstructedDominantCommonHatIsTrue :
  round63EveryResonantTriadHasConstructedDominantCommonHat ≡ true
round63EveryResonantTriadHasConstructedDominantCommonHatIsTrue = refl
