module DASHI.ComputerScience.TekumCanonicalNearestTieExact where

open import Data.Integer.Base using (ℤ; _≤_)

import DASHI.Algebra.BalancedTernaryIntegerExact as BT
import DASHI.ComputerScience.TekumExactNearestRoundingSemantics as Near
import DASHI.ComputerScience.TekumNearestRoundingEnumerationExact as Enum

------------------------------------------------------------------------
-- DASHI CANONICAL TIE POLICY
--
-- Exhaustive exact discovery at 10→8 and 12→10 found genuine nearest ties.
-- DASHI therefore chooses the lower balanced source-integer code among tied
-- exact minimisers.  This key is intrinsic to the target representation and
-- independent of finite-enumeration order.  It is not Hunhold semantics.
------------------------------------------------------------------------

CanonicalTieKey : Set
CanonicalTieKey = ℤ

canonicalTieKey :
  ∀ {extra} → Near.FiniteTekumWord extra → CanonicalTieKey
canonicalTieKey target = BT.toInteger (BT.eval (Near.word target))

record CanonicalNearest
    {sourceExtra targetExtra}
    (source : Near.FiniteTekumWord sourceExtra) : Set where
  constructor canonicalNearest
  field
    chosen : Near.FiniteTekumWord targetExtra
    chosenIsNearest : Enum.exactNearestSet source chosen
    lowerKeyAmongNearest :
      (other : Near.FiniteTekumWord targetExtra) →
      Enum.exactNearestSet source other →
      canonicalTieKey chosen ≤ canonicalTieKey other
open CanonicalNearest public

canonicalNearestInExactNearestSet :
  ∀ {sourceExtra targetExtra}
  {source : Near.FiniteTekumWord sourceExtra} →
  (choice : CanonicalNearest {targetExtra = targetExtra} source) →
  Enum.exactNearestSet source (chosen choice)
canonicalNearestInExactNearestSet = chosenIsNearest

dashiNearestRound :
  ∀ {sourceExtra targetExtra}
  {source : Near.FiniteTekumWord sourceExtra} →
  CanonicalNearest {targetExtra = targetExtra} source →
  Near.FiniteTekumWord targetExtra
dashiNearestRound = chosen

------------------------------------------------------------------------
-- `CanonicalNearest` is the deterministic semantic contract.  Construction of
-- a witness remains a separate finite-minimisation payment; this owner does not
-- pretend that Python enumeration is an Agda proof term.
------------------------------------------------------------------------
