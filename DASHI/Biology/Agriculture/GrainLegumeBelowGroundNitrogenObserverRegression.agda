module DASHI.Biology.Agriculture.GrainLegumeBelowGroundNitrogenObserverRegression where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (true; false)
open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Biology.Agriculture.GrainLegumeBelowGroundNitrogenObserverExact as O

mcNeillDOIPinned :
  O.mcNeillUnkovich2024DOI ≡ "10.1007/s11104-024-06515-y"
mcNeillDOIPinned = refl

liuDOIPinned :
  O.liuEtAl2024DOI ≡ "10.1016/j.fcr.2024.109412"
liuDOIPinned = refl

coarseRootsNotTotalBGN :
  O.coarseRootRecoveryEqualsTotalBelowGroundNitrogen
    O.canonicalBelowGroundObserverBoundary ≡ false
coarseRootsNotTotalBGN = refl

observerCalibrationOwned :
  O.belowGroundNitrogenObserverCalibrationOwned
    O.canonicalBelowGroundObserverBoundary ≡ true
observerCalibrationOwned = refl

canadianPercentagesNotQueensland :
  O.canadianResidueFractionsTransferToQueensland
    O.canonicalBelowGroundObserverBoundary ≡ false
canadianPercentagesNotQueensland = refl

calibrationNotDirectDenominator :
  O.observerCalibrationMakesGRDCBgDenominatorDirectMeasurement
    O.canonicalBelowGroundObserverBoundary ≡ false
calibrationNotDirectDenominator = refl
