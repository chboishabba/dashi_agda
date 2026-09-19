module DASHI.Mathematics.CrossPollination.MillenniumThreeLaneContinuationValidation where

open import Agda.Builtin.Bool using (false; true)
open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Mathematics.Complexity.ConcreteTapeMachineLocalityExact as PNP
import DASHI.Mathematics.AlgebraicGeometry.ProjectiveSpaceHomogeneousCoordinatesExact as Hodge
import DASHI.Mathematics.Automorphic.EllipticInfiniteLFunctionRoadExact as BSDAnalytic
import DASHI.Mathematics.Arithmetic.EllipticTwoDescentRoadExact as BSDArithmetic

pnpConcreteFiniteMachineCarrierPaid :
  PNP.finiteMachineCarrierPaid
    PNP.canonicalConcreteTapeMachineLocalityBoundary
  ≡ true
pnpConcreteFiniteMachineCarrierPaid = refl

pnpGenericAdapterStillOpen :
  PNP.genericMachineAdapterPaid
    PNP.canonicalConcreteTapeMachineLocalityBoundary
  ≡ false
pnpGenericAdapterStillOpen = refl

pnpStillOpen :
  PNP.pVsNPResolved
    PNP.canonicalConcreteTapeMachineLocalityBoundary
  ≡ false
pnpStillOpen = refl

hodgeHomogeneousPresentationPaid :
  Hodge.homogeneousCoordinatePresentationPaid
    Hodge.canonicalProjectiveSpaceGeometryComparisonBoundary
  ≡ true
hodgeHomogeneousPresentationPaid = refl

hodgeComparisonStillOpen :
  Hodge.singularDeRhamComparisonPaid
    Hodge.canonicalProjectiveSpaceGeometryComparisonBoundary
  ≡ false
hodgeComparisonStillOpen = refl

generalHodgeStillOpen :
  Hodge.generalHodgeConjecturePaid
    Hodge.canonicalProjectiveSpaceGeometryComparisonBoundary
  ≡ false
generalHodgeStillOpen = refl

bsdInfiniteRoadTyped :
  BSDAnalytic.infiniteRoadInterfacePaid
    BSDAnalytic.canonicalEllipticInfiniteAnalyticRoadBoundary
  ≡ true
bsdInfiniteRoadTyped = refl

bsdMellinStillOpen :
  BSDAnalytic.mellinRealizationPaid
    BSDAnalytic.canonicalEllipticInfiniteAnalyticRoadBoundary
  ≡ false
bsdMellinStillOpen = refl

bsdTwoDescentCarrierPaid :
  BSDArithmetic.globalLocalCarrierPaid
    BSDArithmetic.canonicalEllipticTwoDescentRoadBoundary
  ≡ true
bsdTwoDescentCarrierPaid = refl

bsdGlobalDescentStillOpen :
  BSDArithmetic.globalExactSequencePaid
    BSDArithmetic.canonicalEllipticTwoDescentRoadBoundary
  ≡ false
bsdGlobalDescentStillOpen = refl

------------------------------------------------------------------------
-- SECOND CONTINUATION: concrete index geometry and existing-proof reuse.
------------------------------------------------------------------------

import DASHI.Mathematics.Complexity.ConcreteTapeIndexedWindowExact as PNPIndex
import DASHI.Mathematics.AlgebraicGeometry.ProjectiveLineGenericCycleClassWeldExact as HodgeP1Weld
import DASHI.Mathematics.Automorphic.EllipticEulerCauchyToLimitExact as BSDCauchy
import DASHI.Mathematics.Arithmetic.EllipticFiniteSeedToSelmerExact as BSDSeed

pnpIndexedWindowGeometryPaid :
  PNPIndex.indexedWindowGeometryPaid
    PNPIndex.canonicalConcreteTapeIndexedWindowBoundary
  ≡ true
pnpIndexedWindowGeometryPaid = refl

pnpAllWindowLocalityStillOpen :
  PNPIndex.allWindowLocalityEquivalencePaid
    PNPIndex.canonicalConcreteTapeIndexedWindowBoundary
  ≡ false
pnpAllWindowLocalityStillOpen = refl

hodgeP1GenericWeldCompilerPaid :
  HodgeP1Weld.projectiveLineGenericCycleWeldCompilerPaid
    HodgeP1Weld.canonicalProjectiveLineGenericCycleWeldBoundary
  ≡ true
hodgeP1GenericWeldCompilerPaid = refl

hodgeCPnComparisonStillOpen :
  HodgeP1Weld.literalCPnComparisonPaid
    HodgeP1Weld.canonicalProjectiveLineGenericCycleWeldBoundary
  ≡ false
hodgeCPnComparisonStillOpen = refl

bsdCauchyCompletionCompilerPaid :
  BSDCauchy.cauchyToConstructiveLimitCompilerPaid
    BSDCauchy.canonicalEllipticEulerCauchyToLimitBoundary
  ≡ true
bsdCauchyCompletionCompilerPaid = refl

bsdEulerCauchyEstimateStillOpen :
  BSDCauchy.eulerCauchyEstimatePaid
    BSDCauchy.canonicalEllipticEulerCauchyToLimitBoundary
  ≡ false
bsdEulerCauchyEstimateStillOpen = refl

bsdFiniteSeedSelmerCompilerPaid :
  BSDSeed.finiteSeedToSelmerCompilerPaid
    BSDSeed.canonicalEllipticFiniteSeedToSelmerBoundary
  ≡ true
bsdFiniteSeedSelmerCompilerPaid = refl

bsdActualGlobalSelmerStillOpen :
  BSDSeed.actualGlobalSelmerInhabitantPaid
    BSDSeed.canonicalEllipticFiniteSeedToSelmerBoundary
  ≡ false
bsdActualGlobalSelmerStillOpen = refl
