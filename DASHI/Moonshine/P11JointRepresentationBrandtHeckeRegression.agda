module DASHI.Moonshine.P11JointRepresentationBrandtHeckeRegression where

open import DASHI.Core.Prelude

import DASHI.Moonshine.P11MatchedDihedralSplitLiftNoGoExact as Split
import DASHI.Moonshine.P11MatchedDihedralSixSectorBasisExact as Basis
import DASHI.Moonshine.P11MatchedDihedralLiftKernelFreedomExact as Freedom
import DASHI.Moonshine.P11MatchedDihedralUnitalHeckeCompletionExact as Unital
import DASHI.Moonshine.P11MatchedDihedralPositiveHeckeNoGoExact as PositiveNoGo

actualP11MatchedCarrierHasSixSectors :
  Basis.actualJ5MatchedSectorCountSix
    Basis.canonicalP11MatchedDihedralSixSectorBoundary
  ≡ true
actualP11MatchedCarrierHasSixSectors =
  Basis.actualJ5MatchedSectorCountSixIsTrue
    Basis.canonicalP11MatchedDihedralSixSectorBoundary

actualP11MatchedCarrierHasDimensionEleven :
  Basis.actualJ5MatchedDimensionEleven
    Basis.canonicalP11MatchedDihedralSixSectorBoundary
  ≡ true
actualP11MatchedCarrierHasDimensionEleven =
  Basis.actualJ5MatchedDimensionElevenIsTrue
    Basis.canonicalP11MatchedDihedralSixSectorBoundary

splitProjectionIsLossy :
  Split.explicitLossyTwoCoordinateProjectionConstructed
    Split.canonicalP11MatchedDihedralSplitLiftBoundary
  ≡ true
splitProjectionIsLossy =
  Split.explicitLossyTwoCoordinateProjectionConstructedIsTrue
    Split.canonicalP11MatchedDihedralSplitLiftBoundary

mechanicalIntertwinersAreTooCheap :
  Split.simultaneousBrandtIntertwinersMechanicallyConstructed
    Split.canonicalP11MatchedDihedralSplitLiftBoundary
  ≡ true
  × Split.mereIntertwinerExistenceTreatedAsExplanation
      Split.canonicalP11MatchedDihedralSplitLiftBoundary
    ≡ false
mechanicalIntertwinersAreTooCheap = refl , refl

splitPrimeSquaresUseProjector :
  Split.primeSquareRelationsUseProjectorNotFineIdentity
    Split.canonicalP11MatchedDihedralSplitLiftBoundary
  ≡ true
splitPrimeSquaresUseProjector =
  Split.primeSquareRelationsUseProjectorNotFineIdentityIsTrue
    Split.canonicalP11MatchedDihedralSplitLiftBoundary

kernelFreedomMakesFineLiftNonunique :
  Freedom.secondSimultaneousPrimeLiftFamilyConstructed
    Freedom.canonicalP11MatchedDihedralKernelFreedomBoundary
  ≡ true
  × Freedom.secondFamilyProvablyDistinct
      Freedom.canonicalP11MatchedDihedralKernelFreedomBoundary
    ≡ true
  × Freedom.intertwinerExistenceDeterminesUniqueFineHeckeAction
      Freedom.canonicalP11MatchedDihedralKernelFreedomBoundary
    ≡ false
kernelFreedomMakesFineLiftNonunique = refl , refl , refl

fullUnitalHeckeAlgebraCanStillBeEngineered :
  Unital.fullIdentityPrimeSquareRelationsConstructed
    Unital.canonicalP11MatchedDihedralUnitalCompletionBoundary
  ≡ true
  × Unital.coprimeHeckeProductsConstructedUpstairs
      Unital.canonicalP11MatchedDihedralUnitalCompletionBoundary
    ≡ true
fullUnitalHeckeAlgebraCanStillBeEngineered = refl , refl

engineeredUnitalCompletionFailsMultiplicityPositivity :
  Unital.ell2OperatorHasNegativeSectorCoefficient
    Unital.canonicalP11MatchedDihedralUnitalCompletionBoundary
  ≡ true
  × Unital.completionPromotedToNonnegativeGeometricCorrespondence
      Unital.canonicalP11MatchedDihedralUnitalCompletionBoundary
    ≡ false
engineeredUnitalCompletionFailsMultiplicityPositivity = refl , refl

naturalSingletVsFivePositiveLiftIsImpossible :
  PositiveNoGo.positiveOneVsFiveNecessaryDataProvedEmpty
    PositiveNoGo.canonicalP11MatchedDihedralPositiveHeckeNoGoBoundary
  ≡ true
  × PositiveNoGo.singletVsAllDoubletsCanCarryPositiveUnitalB2Lift
      PositiveNoGo.canonicalP11MatchedDihedralPositiveHeckeNoGoBoundary
    ≡ false
naturalSingletVsFivePositiveLiftIsImpossible = refl , refl

noGoIsScopedToThisRepresentationInvariant :
  PositiveNoGo.everyPossibleSixToTwoRepresentationInvariantRuledOutHere
    PositiveNoGo.canonicalP11MatchedDihedralPositiveHeckeNoGoBoundary
  ≡ false
noGoIsScopedToThisRepresentationInvariant =
  PositiveNoGo.everyPossibleSixToTwoRepresentationInvariantRuledOutHereIsFalse
    PositiveNoGo.canonicalP11MatchedDihedralPositiveHeckeNoGoBoundary

jointAlgebraAloneStillDoesNotIdentifyRepresentationAction :
  Unital.jointUnitalHeckeAlgebraAloneIdentifiesRepresentationAction
    Unital.canonicalP11MatchedDihedralUnitalCompletionBoundary
  ≡ false
jointAlgebraAloneStillDoesNotIdentifyRepresentationAction =
  Unital.jointUnitalHeckeAlgebraAloneIdentifiesRepresentationActionIsFalse
    Unital.canonicalP11MatchedDihedralUnitalCompletionBoundary
