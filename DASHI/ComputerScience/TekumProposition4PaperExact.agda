module DASHI.ComputerScience.TekumProposition4PaperExact where

open import Agda.Builtin.Nat using (_+_)
open import Data.Integer.Base as ℤ using (_<_)
import Data.Vec.Base as Vec

import DASHI.Algebra.Trit as Trit
import DASHI.Algebra.BalancedTernaryIntegerExact as BT
import DASHI.ComputerScience.TekumOrderedSourceValueExact as Ordered
import DASHI.ComputerScience.TekumProposition4GlobalExact as Global
import DASHI.ComputerScience.TekumWidthAdmissibilityExact as Width

------------------------------------------------------------------------
-- PAPER-FACING HUNHOLD PROPOSITION 4 ENDPOINT
--
-- The implementation proof is intentionally kept in the decomposed global
-- owners.  This module exports the compact interface promised by the original
-- completion plan: source integer-code strict order agrees with the exact
-- source-faithful Tekum order at every admissible core width.
------------------------------------------------------------------------

TekumOrderedValue : Set
TekumOrderedValue = Ordered.OrderedTekumValue

tekumOrderedValue :
  ∀ {extra}
  (even : Width.EvenWidth (8 + extra)) →
  Vec.Vec Trit.Trit (8 + extra) →
  TekumOrderedValue
tekumOrderedValue = Global.sourceOrderedValue

integerCodeOrderAgreesWithTekum :
  ∀ {extra}
  (even : Width.EvenWidth (8 + extra))
  (left right : Vec.Vec Trit.Trit (8 + extra)) →
  BT.toInteger (BT.eval left) ℤ.< BT.toInteger (BT.eval right) →
  Ordered._<ᵀ_
    (tekumOrderedValue even left)
    (tekumOrderedValue even right)
integerCodeOrderAgreesWithTekum = Global.hunholdProposition4Global

hunholdProposition4 :
  ∀ {extra}
  (even : Width.EvenWidth (8 + extra))
  (left right : Vec.Vec Trit.Trit (8 + extra)) →
  BT.toInteger (BT.eval left) ℤ.< BT.toInteger (BT.eval right) →
  Ordered._<ᵀ_
    (tekumOrderedValue even left)
    (tekumOrderedValue even right)
hunholdProposition4 = integerCodeOrderAgreesWithTekum
