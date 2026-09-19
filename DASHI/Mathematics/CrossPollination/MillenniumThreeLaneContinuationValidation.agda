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
