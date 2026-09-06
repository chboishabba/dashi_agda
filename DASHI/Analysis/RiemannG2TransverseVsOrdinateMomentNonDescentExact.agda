module DASHI.Analysis.RiemannG2TransverseVsOrdinateMomentNonDescentExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Analysis.RiemannWeilPairKernelFrobeniusExact as Pair
import DASHI.Analysis.RiemannHermitianDetectabilityGapExact as Detect
import DASHI.Analysis.RiemannAristotlePoleNearPhaseStatisticExact as Phase

------------------------------------------------------------------------
-- COORDINATE FIREWALL: TRANSVERSE alpha != TARGET-ORDINATE delta
--
-- The Alpöge--Furman/Hermitian pair lane measures displacement from the critical
-- line, alpha = Re(rho) - 1/2.  The live gap-split clustering consumer measures
-- target-relative ordinate displacement, delta = Im(rho) - t.
--
-- These are independent coordinates.  A weighted alpha^2 moment therefore
-- cannot directly inhabit a delta^2 local clustering producer.  This module
-- makes that non-descent exact with a finite collision.
------------------------------------------------------------------------

data ZeroCoordinateWorld : Set where
  sameTransverseNearOrdinate sameTransverseFarOrdinate : ZeroCoordinateWorld

transverseDisplacementCode : ZeroCoordinateWorld → Nat
transverseDisplacementCode sameTransverseNearOrdinate = 1
transverseDisplacementCode sameTransverseFarOrdinate = 1

targetOrdinateGapCode : ZeroCoordinateWorld → Nat
targetOrdinateGapCode sameTransverseNearOrdinate = 0
targetOrdinateGapCode sameTransverseFarOrdinate = 3

sameTransverseObservation :
  transverseDisplacementCode sameTransverseNearOrdinate ≡
  transverseDisplacementCode sameTransverseFarOrdinate
sameTransverseObservation = refl

targetOrdinateGapsDiffer :
  targetOrdinateGapCode sameTransverseNearOrdinate ≡
  targetOrdinateGapCode sameTransverseFarOrdinate → ⊥
targetOrdinateGapsDiffer ()

record TransverseVsOrdinateMomentBoundary : Set where
  constructor transverse-vs-ordinate-moment-boundary
  field
    transverseMomentLaneExistsInRepo : Bool
    transverseMomentLaneExistsInRepoIsTrue :
      transverseMomentLaneExistsInRepo ≡ true

    hermitianLocalizationLaneExistsInRepo : Bool
    hermitianLocalizationLaneExistsInRepoIsTrue :
      hermitianLocalizationLaneExistsInRepo ≡ true

    targetRelativeGapLaneExistsInRepo : Bool
    targetRelativeGapLaneExistsInRepoIsTrue :
      targetRelativeGapLaneExistsInRepo ≡ true

    transverseMomentDeterminesTargetOrdinateMoment : Bool
    transverseMomentDeterminesTargetOrdinateMomentIsFalse :
      transverseMomentDeterminesTargetOrdinateMoment ≡ false

    pairKernelWeightedTransverseMomentDirectlyClosesGapClustering : Bool
    pairKernelWeightedTransverseMomentDirectlyClosesGapClusteringIsFalse :
      pairKernelWeightedTransverseMomentDirectlyClosesGapClustering ≡ false

    targetRelativePhaseGapCoordinateIsCorrectCarrier : Bool
    targetRelativePhaseGapCoordinateIsCorrectCarrierIsTrue :
      targetRelativePhaseGapCoordinateIsCorrectCarrier ≡ true

    rhDerived : Bool
    rhDerivedIsFalse : rhDerived ≡ false

    boundedReading : String

open TransverseVsOrdinateMomentBoundary public

canonicalTransverseVsOrdinateMomentBoundary : TransverseVsOrdinateMomentBoundary
canonicalTransverseVsOrdinateMomentBoundary =
  transverse-vs-ordinate-moment-boundary
    true refl
    true refl
    true refl
    false refl
    false refl
    true refl
    false refl
    "Do not route the Alpöge--Furman/Hermitian weighted transverse moment directly into low-gap clustering. Its coordinate alpha measures off-critical-line displacement, while clustering needs delta = ordinate-target. The finite collision has identical transverse code and different target-ordinate gaps. The correct in-repo carrier is the targetRelativeGap coordinate of RiemannAristotlePoleNearPhaseStatisticExact, welded to the existing selected near window."

------------------------------------------------------------------------
-- Existing owners remain honest about their open coordinates.
------------------------------------------------------------------------

pairWeightedTransverseMomentStillOpen :
  Pair.PairKernelFrobeniusBoundary.weightedTransverseMomentBoundProvedHere
    Pair.pairKernelFrobeniusBoundary ≡ false
pairWeightedTransverseMomentStillOpen = refl

hermitianLocalizationStillOpen :
  Detect.HermitianDetectabilityBoundary.localizationProducerConstructedHere
    Detect.hermitianDetectabilityBoundary ≡ false
hermitianLocalizationStillOpen = refl

concreteTargetPhaseStatisticStillOpen :
  Phase.PoleNearPhaseStatisticBoundary.repositoryAlreadyOwnsConcretePoleNearPhaseStatistic
    Phase.canonicalPoleNearPhaseStatisticBoundary ≡ false
concreteTargetPhaseStatisticStillOpen = refl
