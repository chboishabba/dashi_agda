module DASHI.Physics.Closure.YML2StatusReceipt where

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)
open import Data.List.Base using (List; _∷_; [])

import DASHI.Physics.Closure.CarrierRGTrajectoryYMReceipt as RG
import DASHI.Physics.Closure.UniformBoundStrongCouplingReceipt as Bound
import DASHI.Physics.Closure.StringTensionCarrierReceipt as Tension
import DASHI.Physics.Closure.LatticeMassGapFromTransferMatrixReceipt as Gap

data YML2EstablishedItem : Set where
  strongCouplingExpansionAtCarrierBeta :
    YML2EstablishedItem

  carrierStringTensionInCarrierUnits :
    YML2EstablishedItem

  exponentialPlaquetteDecayInStrongPhase :
    YML2EstablishedItem

  finiteLatticeMassGapEstimate :
    YML2EstablishedItem

canonicalYML2EstablishedItems :
  List YML2EstablishedItem
canonicalYML2EstablishedItems =
  strongCouplingExpansionAtCarrierBeta
  ∷ carrierStringTensionInCarrierUnits
  ∷ exponentialPlaquetteDecayInStrongPhase
  ∷ finiteLatticeMassGapEstimate
  ∷ []

data YML2OpenItem : Set where
  runningGaugeCouplingMissing :
    YML2OpenItem

  betaToInfinityContinuumLimitMissing :
    YML2OpenItem

  tightnessAsDepthGrowsMissing :
    YML2OpenItem

  dimensionfulScaleAnchorMissing :
    YML2OpenItem

canonicalYML2OpenItems : List YML2OpenItem
canonicalYML2OpenItems =
  runningGaugeCouplingMissing
  ∷ betaToInfinityContinuumLimitMissing
  ∷ tightnessAsDepthGrowsMissing
  ∷ dimensionfulScaleAnchorMissing
  ∷ []

data YML2Promotion : Set where

yml2PromotionImpossibleHere :
  YML2Promotion →
  ⊥
yml2PromotionImpossibleHere ()

yml2StatusStatement : String
yml2StatusStatement =
  "YM L2 is partially inhabited in the carrier strong-coupling regime: sigma approx 5.27, plaquette correlators decay exponentially at beta=alpha1, and the finite lattice gap is recorded, but continuum beta running and gap survival remain open."

sigmaApproximationLabel : String
sigmaApproximationLabel =
  "sigma approx 5.27"

record YML2StatusReceipt : Setω where
  field
    strongBoundReceipt :
      Bound.UniformBoundStrongCouplingReceipt

    strongBoundPartial :
      Bound.ymL2PartiallyInhabited strongBoundReceipt ≡ true

    stringTensionReceipt :
      Tension.StringTensionCarrierReceipt

    stringTensionRecorded :
      Tension.stringTensionFromStrongCoupling stringTensionReceipt ≡ true

    sigmaApproximation :
      String

    sigmaApproximationIsCanonical :
      sigmaApproximation ≡ sigmaApproximationLabel

    exponentialDecayRecorded :
      Bool

    exponentialDecayRecordedIsTrue :
      exponentialDecayRecorded ≡ true

    latticeGapReceipt :
      Gap.LatticeMassGapFromTransferMatrixReceipt

    finiteLatticeGapPositive :
      Gap.finiteLatticeGapPositive latticeGapReceipt ≡ true

    finiteLatticeGapRecorded :
      Bool

    finiteLatticeGapRecordedIsTrue :
      finiteLatticeGapRecorded ≡ true

    rgTrajectoryReceipt :
      RG.CarrierRGTrajectoryYMReceipt

    carrierRGTrajectoryStillOpen :
      RG.carrierRGTrajectoryConstructed rgTrajectoryReceipt ≡ false

    ymL2PartiallyInhabited :
      Bool

    ymL2PartiallyInhabitedIsTrue :
      ymL2PartiallyInhabited ≡ true

    ymL2ContinuumLimitOpen :
      Bool

    ymL2ContinuumLimitOpenIsTrue :
      ymL2ContinuumLimitOpen ≡ true

    ymL3TightnessRequiresBetaRunning :
      Bool

    ymL3TightnessRequiresBetaRunningIsTrue :
      ymL3TightnessRequiresBetaRunning ≡ true

    continuumUniformBoundsProved :
      Bool

    continuumUniformBoundsProvedIsFalse :
      continuumUniformBoundsProved ≡ false

    continuumBetaRunningConstructed :
      Bool

    continuumBetaRunningConstructedIsFalse :
      continuumBetaRunningConstructed ≡ false

    continuumGapSurvivalProved :
      Bool

    continuumGapSurvivalProvedIsFalse :
      continuumGapSurvivalProved ≡ false

    continuumYangMillsConstructed :
      Bool

    continuumYangMillsConstructedIsFalse :
      continuumYangMillsConstructed ≡ false

    clayYangMillsPromoted :
      Bool

    clayYangMillsPromotedIsFalse :
      clayYangMillsPromoted ≡ false

    terminalClayClaimPromoted :
      Bool

    terminalClayClaimPromotedIsFalse :
      terminalClayClaimPromoted ≡ false

    establishedItems :
      List YML2EstablishedItem

    establishedItemsAreCanonical :
      establishedItems ≡ canonicalYML2EstablishedItems

    openItems :
      List YML2OpenItem

    openItemsAreCanonical :
      openItems ≡ canonicalYML2OpenItems

    promotionFlags :
      List YML2Promotion

    promotionFlagsAreEmpty :
      promotionFlags ≡ []

    statement :
      String

    statementIsCanonical :
      statement ≡ yml2StatusStatement

    receiptBoundary :
      List String

open YML2StatusReceipt public

canonicalYML2StatusReceipt :
  YML2StatusReceipt
canonicalYML2StatusReceipt =
  record
    { strongBoundReceipt =
        Bound.canonicalUniformBoundStrongCouplingReceipt
    ; strongBoundPartial =
        refl
    ; stringTensionReceipt =
        Tension.canonicalStringTensionCarrierReceipt
    ; stringTensionRecorded =
        refl
    ; sigmaApproximation =
        sigmaApproximationLabel
    ; sigmaApproximationIsCanonical =
        refl
    ; exponentialDecayRecorded =
        true
    ; exponentialDecayRecordedIsTrue =
        refl
    ; latticeGapReceipt =
        Gap.canonicalLatticeMassGapFromTransferMatrixReceipt
    ; finiteLatticeGapPositive =
        refl
    ; finiteLatticeGapRecorded =
        true
    ; finiteLatticeGapRecordedIsTrue =
        refl
    ; rgTrajectoryReceipt =
        RG.canonicalCarrierRGTrajectoryYMReceipt
    ; carrierRGTrajectoryStillOpen =
        refl
    ; ymL2PartiallyInhabited =
        true
    ; ymL2PartiallyInhabitedIsTrue =
        refl
    ; ymL2ContinuumLimitOpen =
        true
    ; ymL2ContinuumLimitOpenIsTrue =
        refl
    ; ymL3TightnessRequiresBetaRunning =
        true
    ; ymL3TightnessRequiresBetaRunningIsTrue =
        refl
    ; continuumUniformBoundsProved =
        false
    ; continuumUniformBoundsProvedIsFalse =
        refl
    ; continuumBetaRunningConstructed =
        false
    ; continuumBetaRunningConstructedIsFalse =
        refl
    ; continuumGapSurvivalProved =
        false
    ; continuumGapSurvivalProvedIsFalse =
        refl
    ; continuumYangMillsConstructed =
        false
    ; continuumYangMillsConstructedIsFalse =
        refl
    ; clayYangMillsPromoted =
        false
    ; clayYangMillsPromotedIsFalse =
        refl
    ; terminalClayClaimPromoted =
        false
    ; terminalClayClaimPromotedIsFalse =
        refl
    ; establishedItems =
        canonicalYML2EstablishedItems
    ; establishedItemsAreCanonical =
        refl
    ; openItems =
        canonicalYML2OpenItems
    ; openItemsAreCanonical =
        refl
    ; promotionFlags =
        []
    ; promotionFlagsAreEmpty =
        refl
    ; statement =
        yml2StatusStatement
    ; statementIsCanonical =
        refl
    ; receiptBoundary =
        "Strong-coupling L2 is recorded at beta=alpha1 with sigma approx 5.27 and exponential plaquette decay"
        ∷ "The finite lattice gap is recorded, but this does not supply the beta->infinity Wilson continuum trajectory"
        ∷ "YM L3/L4 require continuum beta running, tightness, continuum gap survival, and continuum measure construction"
        ∷ "No Clay Yang-Mills or terminal Clay claim is promoted"
        ∷ []
    }

yml2StatusKeepsClayFalse :
  clayYangMillsPromoted canonicalYML2StatusReceipt ≡ false
yml2StatusKeepsClayFalse =
  refl

yml2StatusKeepsTerminalFalse :
  terminalClayClaimPromoted canonicalYML2StatusReceipt ≡ false
yml2StatusKeepsTerminalFalse =
  refl
