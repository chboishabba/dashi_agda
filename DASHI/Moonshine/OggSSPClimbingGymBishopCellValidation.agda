module DASHI.Moonshine.OggSSPClimbingGymBishopCellValidation where

open import DASHI.Core.Prelude

import DASHI.Analysis.BishopRadixCellQuantisationExact as BishopCell
import DASHI.Foundations.RadixValuationStageBridge as Radix

------------------------------------------------------------------------
-- RED-first contract: a certified non-boundary Bishop-real cell must compile
-- to the already-owned finite radial address without introducing a total real
-- floor or excluded-middle boundary decision.
------------------------------------------------------------------------

certifiedCellCompiles :
  ∀ {chart depth x} →
  BishopCell.CertifiedOpenRadixCell chart depth x →
  Radix.RadialTreeAddress chart depth
certifiedCellCompiles = BishopCell.certifiedRadialAddress

certifiedCompilerClosed :
  BishopCell.certifiedNonBoundaryCellToAddressClosed
    BishopCell.canonicalBishopRadixCellQuantisationBoundary
  ≡ true
certifiedCompilerClosed = refl

totalFloorStillNotClaimed :
  BishopCell.totalConstructiveRealFloorConstructed
    BishopCell.canonicalBishopRadixCellQuantisationBoundary
  ≡ false
totalFloorStillNotClaimed = refl

boundaryDecisionStillNotClaimed :
  BishopCell.radixBoundaryEqualityDecidableForEveryBishopReal
    BishopCell.canonicalBishopRadixCellQuantisationBoundary
  ≡ false
boundaryDecisionStillNotClaimed = refl
