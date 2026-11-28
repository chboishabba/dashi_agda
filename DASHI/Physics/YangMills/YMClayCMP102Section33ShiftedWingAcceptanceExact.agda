module DASHI.Physics.YangMills.YMClayCMP102Section33ShiftedWingAcceptanceExact where

-- Exact original c-1/c-2 Cauchy tail offsets. Without these one
-- must NOT apply the old unshifted Mertens bound to CMP102.
-- Native Agda 2.9 and --safe trust graph PENDING.

import DASHI.Foundations.BishopFiniteCauchyShiftedWingAbsoluteExact as Shift
import DASHI.Physics.YangMills.YMClayCMP102OriginalShiftedWingOrderExact as Original

originalOneEarlier = Shift.originalWingOneEarlier
originalTwoEarlier = Shift.originalWingTwoEarlier
originalOneEarlierAbsolute = Shift.originalWingOneEarlierAbsolute
originalTwoEarlierAbsolute = Shift.originalWingTwoEarlierAbsolute
originalCMP102AShiftedOrder = Original.originalAShiftedAbsoluteWing
originalCMP102BShiftedOrder = Original.originalBShiftedAbsoluteWing
originalCMP102SignedTailTriangle = Original.originalSignedCauchyTailTriangleBound
