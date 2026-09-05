module DASHI.Physics.QuantumVacuum.CasimirResidualScaleLocalGeometricCauchyReuseExact where

open import Agda.Builtin.Nat using (Nat)
open import Data.Rational.Base as ℚ using (ℚ; 0ℚ; _≤_; _*_)
open import Data.Empty using (⊥)

import DASHI.Physics.YangMills.BalabanContinuumScaleLocalObservableCauchyExact as Scale
import DASHI.Physics.YangMills.BalabanTraceKoteckyPreissGeometricExact as Geo

------------------------------------------------------------------------
-- CASIMIR RESIDUAL CUTOFF TAIL VIA THE EXISTING SCALE-LOCAL COMPILER
--
-- The YM owner is application-neutral at its mathematical core: a summable
-- bound on successive changes of one literal trajectory gives an exact finite
-- tail modulus.  Casimir reuses that theorem shape on its post-cancellation
-- cutoff trajectory.  No Yang--Mills physical estimate is imported.
------------------------------------------------------------------------

record CasimirScaleLocalResidualData : Set₁ where
  field
    majorant : Scale.ScaleLocalIncrementMajorant

    residualDifferenceMagnitude : Nat → Nat → ℚ
    residualDifferenceNonnegative : ∀ start count →
      0ℚ ≤ residualDifferenceMagnitude start count

    sameLiteralPostCancellationTrajectory : Set

    residualDifferenceBelowIncrementTail : ∀ start count →
      residualDifferenceMagnitude start count
      ≤ Scale.scaleIncrementTail majorant start count

open CasimirScaleLocalResidualData public

asScaleCauchyData :
  CasimirScaleLocalResidualData →
  Scale.RenormalizedObservableScaleCauchyData
asScaleCauchyData C = record
  { Scale.majorant = majorant C
  ; Scale.scaleDifferenceMagnitude = residualDifferenceMagnitude C
  ; Scale.differenceNonnegative = residualDifferenceNonnegative C
  ; Scale.differenceBelowIncrementTail = residualDifferenceBelowIncrementTail C
  }

casimirResidualDyadicCauchyModulus :
  (C : CasimirScaleLocalResidualData) → ∀ start count →
  residualDifferenceMagnitude C start count
  ≤ Scale.coefficient (majorant C) * (Geo.half * Geo.halfPower start)
casimirResidualDyadicCauchyModulus C =
  Scale.renormalizedObservableCauchyModulus (asScaleCauchyData C)

record ReverseCasimirScaleLocalObligations : Set where
  field
    postCancellationResidualIdentified : Set
    successiveCutoffIncrementMagnitudeIdentified : Set
    dyadicIncrementMajorantProved : Set
    finiteDifferenceBelowGeneratedTail : Set
    rationalModulusTransportedToBishopMetric : Set

open ReverseCasimirScaleLocalObligations public

data YangMillsPhysicalIncrementReceiptAutomaticallyIsCasimirReceipt : Set where

yangMillsApplicationDoesNotTransfer :
  YangMillsPhysicalIncrementReceiptAutomaticallyIsCasimirReceipt → ⊥
yangMillsApplicationDoesNotTransfer ()
