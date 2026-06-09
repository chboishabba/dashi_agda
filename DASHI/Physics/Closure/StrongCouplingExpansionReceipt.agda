module DASHI.Physics.Closure.StrongCouplingExpansionReceipt where

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)
open import Data.List.Base using (List; _∷_; [])

import DASHI.Physics.Closure.YML1StatusReceipt as YML1

data StrongCouplingExpansionStep : Set where
  wilsonBoltzmannExpansion :
    StrongCouplingExpansionStep

  haarLinkIntegralNormalisation :
    StrongCouplingExpansionStep

  oneLinkIntegralVanishes :
    StrongCouplingExpansionStep

  twoLinkIntegralContractsIndices :
    StrongCouplingExpansionStep

  leadingPlaquetteExpectationOrderBeta :
    StrongCouplingExpansionStep

canonicalStrongCouplingExpansionSteps :
  List StrongCouplingExpansionStep
canonicalStrongCouplingExpansionSteps =
  wilsonBoltzmannExpansion
  ∷ haarLinkIntegralNormalisation
  ∷ oneLinkIntegralVanishes
  ∷ twoLinkIntegralContractsIndices
  ∷ leadingPlaquetteExpectationOrderBeta
  ∷ []

data StrongCouplingExpansionBoundary : Set where
  finiteWilsonLatticeOnly :
    StrongCouplingExpansionBoundary

  betaIdentifiedWithCarrierAlphaOneDiagnostic :
    StrongCouplingExpansionBoundary

  continuumRunningNotSupplied :
    StrongCouplingExpansionBoundary

  noClayMassGapPromotion :
    StrongCouplingExpansionBoundary

canonicalStrongCouplingExpansionBoundaries :
  List StrongCouplingExpansionBoundary
canonicalStrongCouplingExpansionBoundaries =
  finiteWilsonLatticeOnly
  ∷ betaIdentifiedWithCarrierAlphaOneDiagnostic
  ∷ continuumRunningNotSupplied
  ∷ noClayMassGapPromotion
  ∷ []

data StrongCouplingPromotion : Set where

strongCouplingPromotionImpossibleHere :
  StrongCouplingPromotion →
  ⊥
strongCouplingPromotionImpossibleHere ()

wilsonPartitionExpansionLabel : String
wilsonPartitionExpansionLabel =
  "Z = integral prod_l dU_l exp((beta/2N) sum_square Re Tr(U_square)); expand plaquette factors in powers of beta"

plaquetteExpectationLabel : String
plaquetteExpectationLabel =
  "<Re Tr(U_square)> = beta/(2 N^2) + O(beta^3); for SU(2), beta/8 + O(beta^3)"

carrierStrongCouplingLabel : String
carrierStrongCouplingLabel =
  "carrier beta is identified diagnostically with alpha1 ~= 0.04124, hence beta << 1"

record StrongCouplingExpansionReceipt : Setω where
  field
    yml1Status :
      YML1.YML1StatusReceipt

    yml1FiniteScope :
      YML1.ymL1CarrierLatticeInhabited yml1Status ≡ true

    yml1KeepsClayFalse :
      YML1.clayYangMillsPromoted yml1Status ≡ false

    partitionExpansion :
      String

    partitionExpansionIsCanonical :
      partitionExpansion ≡ wilsonPartitionExpansionLabel

    plaquetteExpectation :
      String

    plaquetteExpectationIsCanonical :
      plaquetteExpectation ≡ plaquetteExpectationLabel

    carrierBetaLabel :
      String

    carrierBetaLabelIsCanonical :
      carrierBetaLabel ≡ carrierStrongCouplingLabel

    strongCouplingRegime :
      Bool

    strongCouplingRegimeIsTrue :
      strongCouplingRegime ≡ true

    plaquetteExpectationBetaOverEight :
      Bool

    plaquetteExpectationBetaOverEightIsTrue :
      plaquetteExpectationBetaOverEight ≡ true

    linkVariablesNearlyRandom :
      Bool

    linkVariablesNearlyRandomIsTrue :
      linkVariablesNearlyRandom ≡ true

    continuumExpansionProved :
      Bool

    continuumExpansionProvedIsFalse :
      continuumExpansionProved ≡ false

    clayYangMillsPromoted :
      Bool

    clayYangMillsPromotedIsFalse :
      clayYangMillsPromoted ≡ false

    terminalClayClaimPromoted :
      Bool

    terminalClayClaimPromotedIsFalse :
      terminalClayClaimPromoted ≡ false

    steps :
      List StrongCouplingExpansionStep

    stepsAreCanonical :
      steps ≡ canonicalStrongCouplingExpansionSteps

    boundaries :
      List StrongCouplingExpansionBoundary

    boundariesAreCanonical :
      boundaries ≡ canonicalStrongCouplingExpansionBoundaries

    promotionFlags :
      List StrongCouplingPromotion

    promotionFlagsAreEmpty :
      promotionFlags ≡ []

    receiptBoundary :
      List String

open StrongCouplingExpansionReceipt public

canonicalStrongCouplingExpansionReceipt :
  StrongCouplingExpansionReceipt
canonicalStrongCouplingExpansionReceipt =
  record
    { yml1Status =
        YML1.canonicalYML1StatusReceipt
    ; yml1FiniteScope =
        refl
    ; yml1KeepsClayFalse =
        refl
    ; partitionExpansion =
        wilsonPartitionExpansionLabel
    ; partitionExpansionIsCanonical =
        refl
    ; plaquetteExpectation =
        plaquetteExpectationLabel
    ; plaquetteExpectationIsCanonical =
        refl
    ; carrierBetaLabel =
        carrierStrongCouplingLabel
    ; carrierBetaLabelIsCanonical =
        refl
    ; strongCouplingRegime =
        true
    ; strongCouplingRegimeIsTrue =
        refl
    ; plaquetteExpectationBetaOverEight =
        true
    ; plaquetteExpectationBetaOverEightIsTrue =
        refl
    ; linkVariablesNearlyRandom =
        true
    ; linkVariablesNearlyRandomIsTrue =
        refl
    ; continuumExpansionProved =
        false
    ; continuumExpansionProvedIsFalse =
        refl
    ; clayYangMillsPromoted =
        false
    ; clayYangMillsPromotedIsFalse =
        refl
    ; terminalClayClaimPromoted =
        false
    ; terminalClayClaimPromotedIsFalse =
        refl
    ; steps =
        canonicalStrongCouplingExpansionSteps
    ; stepsAreCanonical =
        refl
    ; boundaries =
        canonicalStrongCouplingExpansionBoundaries
    ; boundariesAreCanonical =
        refl
    ; promotionFlags =
        []
    ; promotionFlagsAreEmpty =
        refl
    ; receiptBoundary =
        "Records the finite-lattice Wilson strong-coupling expansion with beta identified diagnostically as alpha1"
        ∷ "For SU(2), the leading plaquette expectation is beta/8 + O(beta^3)"
        ∷ "This is a finite-lattice strong-coupling receipt only; continuum Yang-Mills and Clay mass gap remain false"
        ∷ []
    }

strongCouplingExpansionKeepsClayFalse :
  clayYangMillsPromoted canonicalStrongCouplingExpansionReceipt ≡ false
strongCouplingExpansionKeepsClayFalse =
  refl

strongCouplingExpansionKeepsTerminalFalse :
  terminalClayClaimPromoted canonicalStrongCouplingExpansionReceipt ≡ false
strongCouplingExpansionKeepsTerminalFalse =
  refl
