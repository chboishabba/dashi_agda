module DASHI.ComputerScience.TekumNearestRoundingEnumerationExact where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; _+_)
open import Data.Fin.Base using (Fin)
open import Data.Maybe.Base using (Maybe; just; nothing)
open import Data.Product.Base using (Σ; _,_)

import DASHI.Algebra.BalancedTernaryRankReconstructionExact as Rank
import DASHI.ComputerScience.TekumExactNearestRoundingSemantics as Near
import DASHI.ComputerScience.TekumFiniteSemanticsExact as Sem
import DASHI.ComputerScience.TekumSourceWordDecodeExact as Source

------------------------------------------------------------------------
-- FINITE TARGET ENUMERATION SURFACE
--
-- `ordinaryFiniteTargets` traverses the existing rank/unrank carrier.  It
-- preserves the literal source word and only admits an element when the source
-- parser itself returns an ordinary value.  No second Tékum decoder exists.
------------------------------------------------------------------------

ordinaryFiniteTargets :
  (extra : Nat) →
  Fin (Rank.pow3Right (8 + extra)) →
  Maybe (Near.FiniteTekumWord extra)
ordinaryFiniteTargets extra i
  with Source.parseTekumWord (Rank.unrankWord (8 + extra) i) in eq
... | just (Sem.ordinary ordinary) =
  just (Near.finiteTekumWord (Rank.unrankWord (8 + extra) i) ordinary eq)
... | just (Sem.special special) = nothing
... | nothing = nothing

------------------------------------------------------------------------
-- Set-valued semantic oracle.
--
-- The exact nearest set is deliberately a predicate/witness carrier rather
-- than a tie-broken function.  Executable finite scans may construct members;
-- all later deterministic policies must prove membership here.
------------------------------------------------------------------------

exactNearestSet :
  ∀ {sourceExtra targetExtra} →
  Near.FiniteTekumWord sourceExtra →
  Near.FiniteTekumWord targetExtra →
  Set
exactNearestSet = Near.Nearest

nearestSetNonempty :
  ∀ {sourceExtra targetExtra} →
  Near.FiniteTekumWord sourceExtra → Set
nearestSetNonempty {targetExtra = targetExtra} source =
  Σ (Near.FiniteTekumWord targetExtra) λ target → exactNearestSet source target

nearestDistanceMinimal :
  ∀ {sourceExtra targetExtra}
  {source : Near.FiniteTekumWord sourceExtra}
  {chosen : Near.FiniteTekumWord targetExtra} →
  exactNearestSet source chosen →
  (other : Near.FiniteTekumWord targetExtra) →
  Near.finiteDistance source chosen Near.≤? Near.finiteDistance source other
nearestDistanceMinimal nearest other = nearest other

------------------------------------------------------------------------
-- The proposition `nearestSetNonempty source` is now explicit and finite.
-- A general kernel construction of its witness is intentionally kept distinct
-- from the Python exhaustive discovery receipt; no computation outside Agda is
-- promoted into a proof term here.
------------------------------------------------------------------------
