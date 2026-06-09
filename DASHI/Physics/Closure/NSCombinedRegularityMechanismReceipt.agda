module DASHI.Physics.Closure.NSCombinedRegularityMechanismReceipt where

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)
open import Data.List.Base using (List; _∷_; [])

import DASHI.Physics.Closure.AdjacentOnlyVortexStretchingReceipt as Adjacent
import DASHI.Physics.Closure.NSFlowPreservationBoundReceipt as Flow
import DASHI.Physics.Closure.NSH118ThresholdReceipt as Threshold
import DASHI.Physics.Closure.NSSubcriticalDissipationReceipt as Dissipation

------------------------------------------------------------------------
-- Combined large-data regularity mechanism receipt.
--
-- This receipt records the candidate combined mechanism only.  Within each
-- prime lane, vortex stretching is adjacent-only, dissipation dominates at
-- high frequency for s >= 11/8, and the remaining low-frequency sector is a
-- globally bounded finite-dimensional ODE diagnostic.  Across prime lanes,
-- flow preservation suppresses cross-prime interactions to zero in the
-- carrier limit; the carrier-structured NS system is therefore recorded as
-- per-lane adjacent-only equations coupled by summably-small cross-lane
-- forcing.  The cross-lane forcing is a candidate summable perturbation and
-- no Clay/global terminal promotion is made here.

data CombinedMechanismFlag : Set where
  perLaneRegularityPlusCrossLaneCoupling :
    CombinedMechanismFlag

data CandidateFlag : Set where
  candidate :
    CandidateFlag

data NSLargeDataGlobalRegularityMechanismFlag : Set where
  identifiedCandidate :
    NSLargeDataGlobalRegularityMechanismFlag

data NSCombinedRegularityMechanismStatus : Set where
  perPrimeLaneAdjacentOnlyStretching :
    NSCombinedRegularityMechanismStatus

  perPrimeLaneHighFrequencyDissipationDominatesForS>=11/8 :
    NSCombinedRegularityMechanismStatus

  perPrimeLaneLowFrequencyFiniteDimensionalODEGloballyBounded :
    NSCombinedRegularityMechanismStatus

  crossPrimeInteractionsSuppressedToZeroByFlowPreservationStatus :
    NSCombinedRegularityMechanismStatus

  carrierStructuredNSDecomposesIntoPerLaneAdjacentOnlyEquations :
    NSCombinedRegularityMechanismStatus

  summablySmallCrossLaneForcingCandidate :
    NSCombinedRegularityMechanismStatus

  noClayOrGlobalTerminalPromotion :
    NSCombinedRegularityMechanismStatus

canonicalNSCombinedRegularityMechanismStatus :
  List NSCombinedRegularityMechanismStatus
canonicalNSCombinedRegularityMechanismStatus =
  perPrimeLaneAdjacentOnlyStretching
  ∷ perPrimeLaneHighFrequencyDissipationDominatesForS>=11/8
  ∷ perPrimeLaneLowFrequencyFiniteDimensionalODEGloballyBounded
  ∷ crossPrimeInteractionsSuppressedToZeroByFlowPreservationStatus
  ∷ carrierStructuredNSDecomposesIntoPerLaneAdjacentOnlyEquations
  ∷ summablySmallCrossLaneForcingCandidate
  ∷ noClayOrGlobalTerminalPromotion
  ∷ []

data NSCombinedRegularityMechanismPromotion : Set where

nsCombinedRegularityMechanismPromotionImpossibleHere :
  NSCombinedRegularityMechanismPromotion →
  ⊥
nsCombinedRegularityMechanismPromotionImpossibleHere ()

nsCombinedRegularityMechanismStatement :
  String
nsCombinedRegularityMechanismStatement =
  "Combined large-data NS regularity mechanism candidate: within each prime lane, vortex stretching is adjacent-only, high-frequency dissipation dominates for s >= 11/8, and the low-frequency sector is a globally bounded finite-dimensional ODE.  Across prime lanes, flow preservation suppresses cross-prime interactions to zero, so carrier-structured NS decomposes into per-lane adjacent-only equations coupled by summably-small cross-lane forcing.  The cross-lane coupling is recorded as a candidate summable perturbation that does not destroy per-lane bounds; no Clay or global terminal promotion follows."

record NSCombinedRegularityMechanismReceipt : Setω where
  field
    adjacentOnlyReceipt :
      Adjacent.AdjacentOnlyVortexStretchingReceipt

    adjacentOnlySameBaseFromReceipt :
      Adjacent.sameBaseResonancesAdjacentBandOnly adjacentOnlyReceipt ≡ true

    adjacentOnlyNoClayPromotion :
      Adjacent.clayNavierStokesPromoted adjacentOnlyReceipt ≡ false

    dissipationReceipt :
      Dissipation.NSSubcriticalDissipationReceipt

    dissipationDominatesForS>=11/8FromReceipt :
      Dissipation.nsAdjacentOnlyDissipationDominanceForS>=11/8
        dissipationReceipt
      ≡
      true

    dissipationNoClayPromotion :
      Dissipation.clayNavierStokesPromoted dissipationReceipt ≡ false

    thresholdReceipt :
      Threshold.NSH118ThresholdReceipt

    thresholdAllowsLargeDataAtOrAbove11/8 :
      Threshold.sAtLeastElevenEighthsLargeDataAllowed thresholdReceipt ≡ true

    thresholdNoClayPromotion :
      Threshold.clayNavierStokesPromoted thresholdReceipt ≡ false

    flowPreservationReceipt :
      Flow.NSFlowPreservationBoundReceipt

    flowSuppressionFromReceipt :
      Flow.offCarrierTermGoesToZero flowPreservationReceipt ≡ true

    flowSummabilityFromReceipt :
      Flow.summableForHsWithS>0 flowPreservationReceipt ≡ true

    flowNoClayPromotion :
      Flow.clayNavierStokesPromoted flowPreservationReceipt ≡ false

    status :
      List NSCombinedRegularityMechanismStatus

    statusIsCanonical :
      status ≡ canonicalNSCombinedRegularityMechanismStatus

    combinedMechanism :
      CombinedMechanismFlag

    combinedMechanismIsPerLaneRegularityPlusCrossLaneCoupling :
      combinedMechanism ≡ perLaneRegularityPlusCrossLaneCoupling

    withinPrimeLaneAdjacentOnlyVortexStretching :
      Bool

    withinPrimeLaneAdjacentOnlyVortexStretchingIsTrue :
      withinPrimeLaneAdjacentOnlyVortexStretching ≡ true

    withinPrimeLaneDissipationDominatesHighFrequencyForS>=11/8 :
      Bool

    withinPrimeLaneDissipationDominatesHighFrequencyForS>=11/8IsTrue :
      withinPrimeLaneDissipationDominatesHighFrequencyForS>=11/8 ≡ true

    withinPrimeLaneLowFrequencyODEGloballyBounded :
      Bool

    withinPrimeLaneLowFrequencyODEGloballyBoundedIsTrue :
      withinPrimeLaneLowFrequencyODEGloballyBounded ≡ true

    crossPrimeInteractionsSuppressedToZeroByFlowPreservation :
      Bool

    crossPrimeInteractionsSuppressedToZeroByFlowPreservationIsTrue :
      crossPrimeInteractionsSuppressedToZeroByFlowPreservation ≡ true

    carrierStructuredNSPerLaneAdjacentOnlyEquations :
      Bool

    carrierStructuredNSPerLaneAdjacentOnlyEquationsIsTrue :
      carrierStructuredNSPerLaneAdjacentOnlyEquations ≡ true

    perLaneEquationsCoupledBySummablySmallCrossLaneForcing :
      Bool

    perLaneEquationsCoupledBySummablySmallCrossLaneForcingIsTrue :
      perLaneEquationsCoupledBySummablySmallCrossLaneForcing ≡ true

    crossLaneCouplingIsSummablePerturbation :
      CandidateFlag

    crossLaneCouplingIsSummablePerturbationIsCandidate :
      crossLaneCouplingIsSummablePerturbation ≡ candidate

    crossLanePerturbationDoesNotDestroyPerLaneBounds :
      CandidateFlag

    crossLanePerturbationDoesNotDestroyPerLaneBoundsIsCandidate :
      crossLanePerturbationDoesNotDestroyPerLaneBounds ≡ candidate

    globalRegularityFromCombination :
      CandidateFlag

    globalRegularityFromCombinationIsCandidate :
      globalRegularityFromCombination ≡ candidate

    nsLargeDataGlobalRegularityMechanism :
      NSLargeDataGlobalRegularityMechanismFlag

    nsLargeDataGlobalRegularityMechanismIsIdentifiedCandidate :
      nsLargeDataGlobalRegularityMechanism ≡ identifiedCandidate

    clayNavierStokesPromoted :
      Bool

    clayNavierStokesPromotedIsFalse :
      clayNavierStokesPromoted ≡ false

    terminalClayClaimPromoted :
      Bool

    terminalClayClaimPromotedIsFalse :
      terminalClayClaimPromoted ≡ false

    globalTerminalPromotion :
      Bool

    globalTerminalPromotionIsFalse :
      globalTerminalPromotion ≡ false

    statement :
      String

    statementIsCanonical :
      statement ≡ nsCombinedRegularityMechanismStatement

    promotionFlags :
      List NSCombinedRegularityMechanismPromotion

    promotionFlagsAreEmpty :
      promotionFlags ≡ []

    receiptBoundary :
      List String

open NSCombinedRegularityMechanismReceipt public

canonicalNSCombinedRegularityMechanismReceipt :
  NSCombinedRegularityMechanismReceipt
canonicalNSCombinedRegularityMechanismReceipt =
  record
    { adjacentOnlyReceipt =
        Adjacent.canonicalAdjacentOnlyVortexStretchingReceipt
    ; adjacentOnlySameBaseFromReceipt =
        refl
    ; adjacentOnlyNoClayPromotion =
        refl
    ; dissipationReceipt =
        Dissipation.canonicalNSSubcriticalDissipationReceipt
    ; dissipationDominatesForS>=11/8FromReceipt =
        refl
    ; dissipationNoClayPromotion =
        refl
    ; thresholdReceipt =
        Threshold.canonicalNSH118ThresholdReceipt
    ; thresholdAllowsLargeDataAtOrAbove11/8 =
        refl
    ; thresholdNoClayPromotion =
        refl
    ; flowPreservationReceipt =
        Flow.canonicalNSFlowPreservationBoundReceipt
    ; flowSuppressionFromReceipt =
        refl
    ; flowSummabilityFromReceipt =
        refl
    ; flowNoClayPromotion =
        refl
    ; status =
        canonicalNSCombinedRegularityMechanismStatus
    ; statusIsCanonical =
        refl
    ; combinedMechanism =
        perLaneRegularityPlusCrossLaneCoupling
    ; combinedMechanismIsPerLaneRegularityPlusCrossLaneCoupling =
        refl
    ; withinPrimeLaneAdjacentOnlyVortexStretching =
        true
    ; withinPrimeLaneAdjacentOnlyVortexStretchingIsTrue =
        refl
    ; withinPrimeLaneDissipationDominatesHighFrequencyForS>=11/8 =
        true
    ; withinPrimeLaneDissipationDominatesHighFrequencyForS>=11/8IsTrue =
        refl
    ; withinPrimeLaneLowFrequencyODEGloballyBounded =
        true
    ; withinPrimeLaneLowFrequencyODEGloballyBoundedIsTrue =
        refl
    ; crossPrimeInteractionsSuppressedToZeroByFlowPreservation =
        true
    ; crossPrimeInteractionsSuppressedToZeroByFlowPreservationIsTrue =
        refl
    ; carrierStructuredNSPerLaneAdjacentOnlyEquations =
        true
    ; carrierStructuredNSPerLaneAdjacentOnlyEquationsIsTrue =
        refl
    ; perLaneEquationsCoupledBySummablySmallCrossLaneForcing =
        true
    ; perLaneEquationsCoupledBySummablySmallCrossLaneForcingIsTrue =
        refl
    ; crossLaneCouplingIsSummablePerturbation =
        candidate
    ; crossLaneCouplingIsSummablePerturbationIsCandidate =
        refl
    ; crossLanePerturbationDoesNotDestroyPerLaneBounds =
        candidate
    ; crossLanePerturbationDoesNotDestroyPerLaneBoundsIsCandidate =
        refl
    ; globalRegularityFromCombination =
        candidate
    ; globalRegularityFromCombinationIsCandidate =
        refl
    ; nsLargeDataGlobalRegularityMechanism =
        identifiedCandidate
    ; nsLargeDataGlobalRegularityMechanismIsIdentifiedCandidate =
        refl
    ; clayNavierStokesPromoted =
        false
    ; clayNavierStokesPromotedIsFalse =
        refl
    ; terminalClayClaimPromoted =
        false
    ; terminalClayClaimPromotedIsFalse =
        refl
    ; globalTerminalPromotion =
        false
    ; globalTerminalPromotionIsFalse =
        refl
    ; statement =
        nsCombinedRegularityMechanismStatement
    ; statementIsCanonical =
        refl
    ; promotionFlags =
        []
    ; promotionFlagsAreEmpty =
        refl
    ; receiptBoundary =
        "combinedMechanism = perLaneRegularityPlusCrossLaneCoupling"
        ∷ "Within each prime lane: adjacent-only vortex stretching"
        ∷ "Within each prime lane: dissipation dominates at high frequency for s >= 11/8"
        ∷ "Within each prime lane: finite-dimensional low-frequency ODE is recorded as globally bounded"
        ∷ "Across prime lanes: flow preservation suppresses cross-prime interactions to zero"
        ∷ "Carrier-structured NS decomposes into per-lane adjacent-only equations coupled by summably-small cross-lane forcing"
        ∷ "crossLaneCouplingIsSummablePerturbation = candidate"
        ∷ "globalRegularityFromCombination = candidate"
        ∷ "nsLargeDataGlobalRegularityMechanism = identified candidate"
        ∷ "No Clay or global terminal promotion is recorded"
        ∷ []
    }

canonicalCombinedMechanismFlag :
  combinedMechanism canonicalNSCombinedRegularityMechanismReceipt
  ≡
  perLaneRegularityPlusCrossLaneCoupling
canonicalCombinedMechanismFlag =
  refl

canonicalCrossLaneCouplingIsSummablePerturbation :
  crossLaneCouplingIsSummablePerturbation
    canonicalNSCombinedRegularityMechanismReceipt
  ≡
  candidate
canonicalCrossLaneCouplingIsSummablePerturbation =
  refl

canonicalGlobalRegularityFromCombinationCandidate :
  globalRegularityFromCombination canonicalNSCombinedRegularityMechanismReceipt
  ≡
  candidate
canonicalGlobalRegularityFromCombinationCandidate =
  refl

canonicalNSLargeDataGlobalRegularityMechanismIdentifiedCandidate :
  nsLargeDataGlobalRegularityMechanism
    canonicalNSCombinedRegularityMechanismReceipt
  ≡
  identifiedCandidate
canonicalNSLargeDataGlobalRegularityMechanismIdentifiedCandidate =
  refl

canonicalNSCombinedRegularityMechanismNoGlobalTerminalPromotion :
  globalTerminalPromotion canonicalNSCombinedRegularityMechanismReceipt
  ≡
  false
canonicalNSCombinedRegularityMechanismNoGlobalTerminalPromotion =
  refl
