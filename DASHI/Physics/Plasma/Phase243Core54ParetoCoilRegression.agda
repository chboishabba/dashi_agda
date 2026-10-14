module DASHI.Physics.Plasma.Phase243Core54ParetoCoilRegression where

open import DASHI.Core.Prelude

import DASHI.Physics.Plasma.Phase243Core54ParetoCoilExact as Cut

open Cut

representativeCountPinned : representativeCount ≡ 54
representativeCountPinned = refl

abcGridRecordCountPinned : abcGridRecordCount ≡ 810
abcGridRecordCountPinned = refl

paretoFrontierNonEmptyPinned : Bool
paretoFrontierNonEmptyPinned = paretoFrontierNonEmpty canonicalCore54ParetoCoilReceipt

paretoFrontierNonEmptyPinnedIsTrue : paretoFrontierNonEmptyPinned ≡ true
paretoFrontierNonEmptyPinnedIsTrue = refl

coilShortlistNonEmptyPinned : Bool
coilShortlistNonEmptyPinned = coilShortlistNonEmpty canonicalCore54ParetoCoilReceipt

coilShortlistNonEmptyPinnedIsTrue : coilShortlistNonEmptyPinned ≡ true
coilShortlistNonEmptyPinnedIsTrue = refl

freeBoundaryStillOpenPinned : Bool
freeBoundaryStillOpenPinned = sameObjectCoilPlasmaFreeBoundaryPaid canonicalCore54ParetoCoilBoundary

freeBoundaryStillOpenPinnedIsFalse : freeBoundaryStillOpenPinned ≡ false
freeBoundaryStillOpenPinnedIsFalse = refl
