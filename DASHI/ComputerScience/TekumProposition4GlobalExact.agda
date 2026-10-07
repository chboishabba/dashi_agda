module DASHI.ComputerScience.TekumProposition4GlobalExact where

open import Agda.Builtin.Nat using (_+_)
open import Data.Integer.Base as ℤ using (_<_)
import Data.Vec.Base as Vec

import DASHI.Algebra.Trit as Trit
import DASHI.Algebra.BalancedTernaryIntegerExact as BT
import DASHI.ComputerScience.TekumOrderedSourceValueExact as Ordered
import DASHI.ComputerScience.TekumSourceParserTotalityExact as Total
import DASHI.ComputerScience.TekumWidthAdmissibilityExact as Width

------------------------------------------------------------------------
-- FULL HUNHOLD PROPOSITION 4 ON CORE WIDTHS
--
-- Source integer-code order is transported to the source-faithful total order:
--
--   NaR < finite rationals < infinity,
--
-- with zero represented by rational zero and every non-special source word
-- carrying a proved successful ordinary parser witness.  Ordinary finite order
-- delegates exclusively to the canonical exact rational decoder.
------------------------------------------------------------------------

orderedDecodeFromTotal :
  ∀ {extra}
  {word : Vec.Vec Trit.Trit (8 + extra)} →
  Total.TotalSourceParse word →
  Ordered.SourceOrderedDecode word
orderedDecodeFromTotal (Total.parsedNaR eq) = Ordered.decodedNaR eq
orderedDecodeFromTotal (Total.parsedZero eq) = Ordered.decodedZero eq
orderedDecodeFromTotal (Total.parsedInfinity eq) = Ordered.decodedInfinity eq
orderedDecodeFromTotal
    (Total.parsedOrdinary classEq
      (Total.ordinaryParseWitness r payload parsed parseEq)) =
  Ordered.decodedOrdinary classEq parseEq

sourceOrderedValue :
  ∀ {extra}
  (even : Width.EvenWidth (8 + extra)) →
  (word : Vec.Vec Trit.Trit (8 + extra)) →
  Ordered.OrderedTekumValue
sourceOrderedValue even word =
  Ordered.orderedValue
    (orderedDecodeFromTotal (Total.totalSourceParse even word))

hunholdProposition4Global :
  ∀ {extra}
  (even : Width.EvenWidth (8 + extra))
  (left right : Vec.Vec Trit.Trit (8 + extra)) →
  BT.toInteger (BT.eval left) ℤ.< BT.toInteger (BT.eval right) →
  Ordered._<ᵀ_
    (sourceOrderedValue even left)
    (sourceOrderedValue even right)
hunholdProposition4Global even left right integerLt =
  Ordered.sourceIntegerStrictImpliesOrderedStrict
    even
    (orderedDecodeFromTotal (Total.totalSourceParse even left))
    (orderedDecodeFromTotal (Total.totalSourceParse even right))
    integerLt
