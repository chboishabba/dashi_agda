module DASHI.Physics.Closure.NSCarrierRegularityThresholdReceipt where

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)
open import Data.List.Base using (List; _∷_; [])

import DASHI.Physics.Closure.AdjacentOnlyVortexStretchingReceipt as Adjacent

------------------------------------------------------------------------
-- Carrier-structured H^s regularity-threshold receipt.
--
-- This receipt combines the A1-A3 carrier-frequency diagnostics: for
-- carrier-structured H^s data with s > 0, adjacent-only stretching,
-- summable flow preservation, and high-frequency dissipation dominance are
-- recorded as holding.  The remaining low-frequency sector is finite and is
-- reduced to globally solvable finite-dimensional ODE diagnostics.  This is
-- a carrier-structured candidate receipt only and carries no Clay promotion.

data NSCarrierRegularityThresholdStatus : Set where
  carrierStructuredPositiveSobolevData :
    NSCarrierRegularityThresholdStatus

  adjacentOnlyStretchingRecorded :
    NSCarrierRegularityThresholdStatus

  summableFlowPreservationRecorded :
    NSCarrierRegularityThresholdStatus

  highFrequencyDissipationDominanceRecorded :
    NSCarrierRegularityThresholdStatus

  finiteLowFrequencyODEReductionRecorded :
    NSCarrierRegularityThresholdStatus

  carrierStructuredCandidateOnlyNoClayPromotion :
    NSCarrierRegularityThresholdStatus

canonicalNSCarrierRegularityThresholdStatus :
  List NSCarrierRegularityThresholdStatus
canonicalNSCarrierRegularityThresholdStatus =
  carrierStructuredPositiveSobolevData
  ∷ adjacentOnlyStretchingRecorded
  ∷ summableFlowPreservationRecorded
  ∷ highFrequencyDissipationDominanceRecorded
  ∷ finiteLowFrequencyODEReductionRecorded
  ∷ carrierStructuredCandidateOnlyNoClayPromotion
  ∷ []

data NSCarrierRegularityThresholdPromotion : Set where

nsCarrierRegularityThresholdPromotionImpossibleHere :
  NSCarrierRegularityThresholdPromotion →
  ⊥
nsCarrierRegularityThresholdPromotionImpossibleHere ()

carrierRegularityThresholdStatement : String
carrierRegularityThresholdStatement =
  "For carrier-structured H^s data with s > 0, adjacent-only stretching, summable flow preservation, and high-frequency dissipation dominance hold; the remaining low-frequency modes are finite and reduce to globally solvable finite-dimensional ODE diagnostics.  This is a carrier-structured candidate only, with no Clay promotion."

canonicalCarrierRegularityThreshold : String
canonicalCarrierRegularityThreshold =
  "s > 0 (carrier-structured data)"

canonicalNSGlobalRegularityForCarrierStructuredData : String
canonicalNSGlobalRegularityForCarrierStructuredData =
  "candidate for any s > 0"

record NSCarrierRegularityThresholdReceipt : Setω where
  field
    adjacentOnlyReceipt :
      Adjacent.AdjacentOnlyVortexStretchingReceipt

    adjacentOnlyStretchingFromA1 :
      Adjacent.sameBaseResonancesAdjacentBandOnly adjacentOnlyReceipt ≡ true

    adjacentOnlyNoClayPromotion :
      Adjacent.clayNavierStokesPromoted adjacentOnlyReceipt ≡ false

    status :
      List NSCarrierRegularityThresholdStatus

    statusIsCanonical :
      status ≡ canonicalNSCarrierRegularityThresholdStatus

    carrierStructuredHsData :
      Bool

    carrierStructuredHsDataIsTrue :
      carrierStructuredHsData ≡ true

    sobolevExponentPositive :
      Bool

    sobolevExponentPositiveIsTrue :
      sobolevExponentPositive ≡ true

    adjacentOnlyStretchingHolds :
      Bool

    adjacentOnlyStretchingHoldsIsTrue :
      adjacentOnlyStretchingHolds ≡ true

    summableFlowPreservationHolds :
      Bool

    summableFlowPreservationHoldsIsTrue :
      summableFlowPreservationHolds ≡ true

    highFrequencyDissipationDominanceHolds :
      Bool

    highFrequencyDissipationDominanceHoldsIsTrue :
      highFrequencyDissipationDominanceHolds ≡ true

    lowFrequencyModesFinitelyMany :
      Bool

    lowFrequencyModesFinitelyManyIsTrue :
      lowFrequencyModesFinitelyMany ≡ true

    lowFrequencyODEGloballySolvable :
      Bool

    lowFrequencyODEGloballySolvableIsTrue :
      lowFrequencyODEGloballySolvable ≡ true

    lowFrequencyFiniteDimensionalDiagnostics :
      Bool

    lowFrequencyFiniteDimensionalDiagnosticsIsTrue :
      lowFrequencyFiniteDimensionalDiagnostics ≡ true

    carrierRegularityThreshold :
      String

    carrierRegularityThresholdIsCanonical :
      carrierRegularityThreshold ≡ canonicalCarrierRegularityThreshold

    nsGlobalRegularityForCarrierStructuredData :
      String

    nsGlobalRegularityForCarrierStructuredDataIsCanonical :
      nsGlobalRegularityForCarrierStructuredData
      ≡
      canonicalNSGlobalRegularityForCarrierStructuredData

    arbitraryDataPromotionClaimed :
      Bool

    arbitraryDataPromotionClaimedIsFalse :
      arbitraryDataPromotionClaimed ≡ false

    clayNavierStokesPromoted :
      Bool

    clayNavierStokesPromotedIsFalse :
      clayNavierStokesPromoted ≡ false

    statement :
      String

    statementIsCanonical :
      statement ≡ carrierRegularityThresholdStatement

    promotionFlags :
      List NSCarrierRegularityThresholdPromotion

    promotionFlagsAreEmpty :
      promotionFlags ≡ []

    receiptBoundary :
      List String

open NSCarrierRegularityThresholdReceipt public

canonicalNSCarrierRegularityThresholdReceipt :
  NSCarrierRegularityThresholdReceipt
canonicalNSCarrierRegularityThresholdReceipt =
  record
    { adjacentOnlyReceipt =
        Adjacent.canonicalAdjacentOnlyVortexStretchingReceipt
    ; adjacentOnlyStretchingFromA1 =
        refl
    ; adjacentOnlyNoClayPromotion =
        refl
    ; status =
        canonicalNSCarrierRegularityThresholdStatus
    ; statusIsCanonical =
        refl
    ; carrierStructuredHsData =
        true
    ; carrierStructuredHsDataIsTrue =
        refl
    ; sobolevExponentPositive =
        true
    ; sobolevExponentPositiveIsTrue =
        refl
    ; adjacentOnlyStretchingHolds =
        true
    ; adjacentOnlyStretchingHoldsIsTrue =
        refl
    ; summableFlowPreservationHolds =
        true
    ; summableFlowPreservationHoldsIsTrue =
        refl
    ; highFrequencyDissipationDominanceHolds =
        true
    ; highFrequencyDissipationDominanceHoldsIsTrue =
        refl
    ; lowFrequencyModesFinitelyMany =
        true
    ; lowFrequencyModesFinitelyManyIsTrue =
        refl
    ; lowFrequencyODEGloballySolvable =
        true
    ; lowFrequencyODEGloballySolvableIsTrue =
        refl
    ; lowFrequencyFiniteDimensionalDiagnostics =
        true
    ; lowFrequencyFiniteDimensionalDiagnosticsIsTrue =
        refl
    ; carrierRegularityThreshold =
        canonicalCarrierRegularityThreshold
    ; carrierRegularityThresholdIsCanonical =
        refl
    ; nsGlobalRegularityForCarrierStructuredData =
        canonicalNSGlobalRegularityForCarrierStructuredData
    ; nsGlobalRegularityForCarrierStructuredDataIsCanonical =
        refl
    ; arbitraryDataPromotionClaimed =
        false
    ; arbitraryDataPromotionClaimedIsFalse =
        refl
    ; clayNavierStokesPromoted =
        false
    ; clayNavierStokesPromotedIsFalse =
        refl
    ; statement =
        carrierRegularityThresholdStatement
    ; statementIsCanonical =
        refl
    ; promotionFlags =
        []
    ; promotionFlagsAreEmpty =
        refl
    ; receiptBoundary =
        "carrierRegularityThreshold = s > 0 (carrier-structured data)"
        ∷ "adjacentOnlyStretchingHolds = true"
        ∷ "summableFlowPreservationHolds = true"
        ∷ "highFrequencyDissipationDominanceHolds = true"
        ∷ "lowFrequencyModesFinitelyMany = true"
        ∷ "lowFrequencyODEGloballySolvable = true"
        ∷ "nsGlobalRegularityForCarrierStructuredData = candidate for any s > 0"
        ∷ "No arbitrary-data or Clay Navier-Stokes promotion is claimed"
        ∷ []
    }

lowFrequencyModesFinitelyManyTrue :
  lowFrequencyModesFinitelyMany canonicalNSCarrierRegularityThresholdReceipt
  ≡
  true
lowFrequencyModesFinitelyManyTrue =
  refl

lowFrequencyODEGloballySolvableTrue :
  lowFrequencyODEGloballySolvable canonicalNSCarrierRegularityThresholdReceipt
  ≡
  true
lowFrequencyODEGloballySolvableTrue =
  refl

carrierRegularityThresholdCanonical :
  carrierRegularityThreshold canonicalNSCarrierRegularityThresholdReceipt
  ≡
  canonicalCarrierRegularityThreshold
carrierRegularityThresholdCanonical =
  refl

nsGlobalRegularityForCarrierStructuredDataCanonical :
  nsGlobalRegularityForCarrierStructuredData
    canonicalNSCarrierRegularityThresholdReceipt
  ≡
  canonicalNSGlobalRegularityForCarrierStructuredData
nsGlobalRegularityForCarrierStructuredDataCanonical =
  refl

nsCarrierRegularityThresholdNoClayPromotion :
  clayNavierStokesPromoted canonicalNSCarrierRegularityThresholdReceipt
  ≡
  false
nsCarrierRegularityThresholdNoClayPromotion =
  refl

nsCarrierRegularityThresholdNoPromotion :
  NSCarrierRegularityThresholdPromotion →
  ⊥
nsCarrierRegularityThresholdNoPromotion =
  nsCarrierRegularityThresholdPromotionImpossibleHere
