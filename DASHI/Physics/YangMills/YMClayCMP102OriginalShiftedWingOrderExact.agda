module DASHI.Physics.YangMills.YMClayCMP102OriginalShiftedWingOrderExact where

------------------------------------------------------------------------
-- CMP102 original signed A/B tails, right cutoff offsets.
-- The generic Mertens positive wing theorem is valid at c, but
-- A needs c-1 and B needs c-2. The foundation's shifted wing
-- now carries the missing last one/two Cauchy coefficient rows.
-- The original c=1 B singleton is intentionally handled separately.
--
-- This file uses literal original CMP109.term coefficient streams,
-- original `Rectangle.rectangleSum`, original `Row.trianglePartial`,
-- and native Bishop real order, not an invented power series.
-- SOURCE WRITTEN; Agda kernel acceptance pending.
------------------------------------------------------------------------

open import Agda.Builtin.Nat using (Nat; zero; suc; _+_)
import Real as R
import RealProperties as P

import DASHI.Foundations.BishopFiniteCauchyShiftedWingAbsoluteExact as Shift
import DASHI.Foundations.BishopFiniteCauchyWingAbsoluteBoundExact as Wing
import DASHI.Foundations.BishopFiniteCauchyRowReindexExact as Row
import DASHI.Physics.YangMills.YMClayCMP102OriginalFiniteCauchyWingBoundsExact as Original
import DASHI.Physics.YangMills.YMClayCMP102OriginalFiniteTailGeometryExact as Tail

-- Original A square wing after its X factor starts at degree c.
-- This is the REAL shifted cutoff c-1 and retains last row c-1.
originalAShiftedAbsoluteWing : ∀ X n →
  R._≤_
    (R.∣ Tail.originalAWing X (suc n) ∣)
    (R._+_
      (R._-_
        (Row.trianglePartial
          (Wing.absoluteTerms (Original.aTerm X))
          (Wing.absoluteTerms (Original.aTerm X))
          ((suc n) + (suc n)))
        (Row.trianglePartial
          (Wing.absoluteTerms (Original.aTerm X))
          (Wing.absoluteTerms (Original.aTerm X)) (suc n)))
      (R.∣ Row.cauchyCoefficient
         (Original.aTerm X) (Original.aTerm X) n ∣))
originalAShiftedAbsoluteWing X n =
  Shift.originalWingOneEarlierAbsolute
    (Original.aTerm X) (Original.aTerm X) n

-- Original B square wing for c >= 2, after its X² factor,
-- starts at degree c. Both missing endpoint rows are charged.
originalBShiftedAbsoluteWing : ∀ X n →
  R._≤_
    (R.∣ Tail.originalBWing X (suc (suc n)) ∣)
    (R._+_
      (R._+_
        (R._-_
          (Row.trianglePartial
            (Wing.absoluteTerms (Original.bTerm X))
            (Wing.absoluteTerms (Original.bTerm X))
            ((suc (suc n)) + (suc (suc n))))
          (Row.trianglePartial
            (Wing.absoluteTerms (Original.bTerm X))
            (Wing.absoluteTerms (Original.bTerm X))
            (suc (suc n))))
        (R.∣ Row.cauchyCoefficient
          (Original.bTerm X) (Original.bTerm X) n ∣))
      (R.∣ Row.cauchyCoefficient
        (Original.bTerm X) (Original.bTerm X) (suc n) ∣))
originalBShiftedAbsoluteWing X n =
  Shift.originalWingTwoEarlierAbsolute
    (Original.bTerm X) (Original.bTerm X) n

-- Each actual original scalar residual is the sum of EXACTLY three
-- geometrically distinct terms: signed A wing, omitted B endpoint,
-- signed B wing. The finite Bishop triangle inequality is applied
-- before any positivity or factorial bounds. Thus the sign is
-- preserved throughout, including X<0.
originalSignedCauchyTailTriangleBound : ∀ X n →
  R._≤_
    (R.∣ Tail.originalSignedCauchyTail X n ∣)
    (R._+_
      (R._+_
        (R.∣ R.- (R._*_ X (Tail.originalAWing X (suc n))) ∣)
        (R.∣ Tail.originalOmittedLinearB X n ∣))
      (R.∣ R._*_
        (R._*_ X X)
        (Tail.originalBWing X (suc n)) ∣))
originalSignedCauchyTailTriangleBound X n =
  let
    A = R.- (R._*_ X (Tail.originalAWing X (suc n)))
    B = Tail.originalOmittedLinearB X n
    C = R._*_ (R._*_ X X) (Tail.originalBWing X (suc n))
  in
  P.≤-trans
    (P.∣x+y∣≤∣x∣+∣y∣ (R._+_ A B) C)
    (P.+-mono-≤
      (P.∣x+y∣≤∣x∣+∣y∣ A B)
      P.≤-refl)
