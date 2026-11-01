module DASHI.Base369ZetaHeisenbergFiftyFourValidation where

open import Agda.Builtin.Bool using (true; false)
open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Moonshine.Base369ZetaHeisenbergFiftyFourCarrierExact as Z54
import DASHI.Moonshine.Monster3BFiniteHeisenbergGeneratorsExact as H

zetaPairCountPinned : Z54.nontrivialZetaSheetCount ≡ 2
zetaPairCountPinned = Z54.nontrivialZetaSheetCountIsTwo

zetaSheetsTimesVoxelPinned : Z54.zeta54SiteCount ≡ 54
zetaSheetsTimesVoxelPinned = Z54.zeta54SiteCountIsFiftyFour

sixByNinePinned : Z54.sixByNineSiteCount ≡ 54
sixByNinePinned = Z54.sixByNineSiteCountIsFiftyFour

sixFactorPinned : Z54.zetaTritCount ≡ 6
sixFactorPinned = Z54.zetaTritCountIsSix

nonaryFactorPinned : Z54.nonaryPointCount ≡ 9
nonaryFactorPinned = Z54.nonaryPointCountIsNine

heisenbergAxesPinned : Z54.heisenbergCoordinateCount ≡ 6
heisenbergAxesPinned = Z54.heisenbergCoordinateCountIsSix

heisenbergStatesPinned : Z54.heisenbergStateCount ≡ 729
heisenbergStatesPinned = Z54.heisenbergStateCountIsSevenTwentyNine

axisRoundTripPinned :
  (a : H.Axis6) → Z54.zetaTrit6ToAxis6 (Z54.axis6ToZetaTrit6 a) ≡ a
axisRoundTripPinned = Z54.axisZetaTritRoundTrip

fiftyFourNotHeisenbergRepresentationDimension :
  Z54.ZetaHeisenbergFiftyFourBoundary.fiftyFourIsHeisenbergRepresentationDimension
    Z54.canonicalZetaHeisenbergFiftyFourBoundary ≡ false
fiftyFourNotHeisenbergRepresentationDimension = refl

zetaPairNotWholeC3Carrier :
  Z54.ZetaHeisenbergFiftyFourBoundary.zetaSheetPairIsWholeC3CharacterCarrier
    Z54.canonicalZetaHeisenbergFiftyFourBoundary ≡ false
zetaPairNotWholeC3Carrier = refl
